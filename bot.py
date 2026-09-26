"""
Bot Telegram — Dictée en arabe pour débutants.

Principe :
  1. /lettres  → l'élève coche les lettres qu'il a déjà apprises.
  2. /dictee   → il choisit le nombre de mots puis leur longueur.
  3. Le bot INVENTE des mots au hasard (ils n'ont pas besoin d'avoir un sens),
     construits uniquement avec les lettres cochées, entièrement vocalisés.
  4. Il envoie chaque mot en note vocale, sans l'écriture.
  5. « 👁️ Afficher la réponse » révèle le mot écrit avec ses harakât.
  6. « ➡️ Mot suivant » enchaîne ; à la fin, un bilan récapitule la série.

Choix techniques :
  - python-telegram-bot v21/v22 (async).
  - Synthèse vocale : edge-tts (voix neuronales Microsoft, gratuites, bien plus
    claires que gTTS en arabe), avec repli automatique sur gTTS en cas d'échec.
  - Chaque audio est écrit dans un fichier temporaire, envoyé, puis supprimé.
  - PicklePersistence : les lettres de chaque élève survivent au redémarrage du bot.
"""

from __future__ import annotations

import asyncio
import html
import logging
import os
import random
import re
import secrets
import tempfile
from pathlib import Path

import edge_tts
from dotenv import load_dotenv
from gtts import gTTS
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ChatAction, ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    PicklePersistence,
)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

BASE_DIR = Path(__file__).resolve().parent
load_dotenv(BASE_DIR / "config.txt")  # contient TELEGRAM_BOT_TOKEN=... (et réglages optionnels)
# Sur le serveur, le token est écrit dans config.local.txt (jamais envoyé sur GitHub).
load_dotenv(BASE_DIR / "config.local.txt", override=True)

DATA_DIR = Path(os.getenv("DATA_DIR", BASE_DIR))  # le serveur utilise /var/lib/dictee
AUDIO_TMP_DIR = DATA_DIR / "audio_tmp"            # fichiers audio temporaires
PERSISTENCE_FILE = DATA_DIR / "bot_data.pickle"   # lettres enregistrées de chaque élève

TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TTS_VOICE = os.getenv("TTS_VOICE", "ar-SA-HamedNeural")  # ou ar-SA-ZariyahNeural (voix féminine)
TTS_RATE = os.getenv("TTS_RATE", "-20%")                 # débit ralenti pour la dictée

SESSION_SIZES = (3, 5, 10)
MIN_LETTERS = 2
LETTERS_PER_ROW = 4

# Longueur des mots inventés, en nombre de syllabes (min, max).
WORD_LENGTHS = {
    "court": ("Courts", (1, 2)),
    "moyen": ("Moyens", (2, 3)),
    "long": ("Longs", (3, 4)),
}

# Autoriser un alif avec hamza en début de mot (أَ / أُ / إِ) quand ا est cochée.
# Passe à False si la hamza n'a pas encore été vue en cours.
ALLOW_INITIAL_HAMZA = True

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=logging.INFO,
)
logging.getLogger("httpx").setLevel(logging.WARNING)  # évite le bruit des requêtes HTTP
logger = logging.getLogger("dictee_arabe")

# ---------------------------------------------------------------------------
# Alphabet
# ---------------------------------------------------------------------------

# Les 28 lettres, dans l'ordre alphabétique classique.
ALPHABET = [
    "ا", "ب", "ت", "ث", "ج", "ح", "خ", "د", "ذ", "ر", "ز", "س", "ش", "ص",
    "ض", "ط", "ظ", "ع", "غ", "ف", "ق", "ك", "ل", "م", "ن", "ه", "و", "ي",
]
ALPHABET_SET = frozenset(ALPHABET)

FATHA, DAMMA, KASRA = "\u064E", "\u064F", "\u0650"   # a, ou, i
SUKUN, SHADDA = "\u0652", "\u0651"
SHORT_VOWELS = (FATHA, DAMMA, KASRA)
LONG_VOWEL_LETTER = {FATHA: "ا", DAMMA: "و", KASRA: "ي"}  # voyelles longues : aa, ouu, ii
SEMI_VOWELS = ("و", "ي")

DIACRITICS_RE = re.compile(r"[\u064B-\u065F\u0670]")
HAMZA_TO_ALIF = {"أ": "ا", "إ": "ا"}


def ordered(letters: set[str]) -> list[str]:
    """Trie un ensemble de lettres dans l'ordre alphabétique arabe."""
    return [letter for letter in ALPHABET if letter in letters]


def consonants_of(letters: set[str]) -> list[str]:
    """Lettres utilisables comme consonnes (toutes sauf l'alif, qui ne porte pas de voyelle)."""
    return [letter for letter in ordered(letters) if letter != "ا"]


def spelled_letters(word: str) -> str:
    """بَابْ → « ب · ا · ب » : aide le débutant à vérifier lettre par lettre."""
    bare = DIACRITICS_RE.sub("", word)
    return " · ".join(bare)


def base_letters(word: str) -> set[str]:
    """Lettres de base d'un mot (hamza rattachée à l'alif), pour les contrôles."""
    return {HAMZA_TO_ALIF.get(ch, ch) for ch in DIACRITICS_RE.sub("", word)}


# ---------------------------------------------------------------------------
# Générateur de mots inventés
# ---------------------------------------------------------------------------
#
# Un mot est une suite de syllabes. Chaque syllabe =
#   consonne d'attaque (+ chadda éventuelle) + voyelle courte
#   + éventuellement une voyelle longue (ا / و / ي)
#   + éventuellement une consonne finale avec soukoun.
#
# Règles appliquées pour que le mot soit prononçable et lisible par un débutant :
#   - Seules les lettres cochées sont utilisées.
#   - Le mot se termine toujours par une consonne avec soukoun ou une voyelle longue
#     (c'est ainsi qu'on prononce un mot isolé : l'audio correspond à l'écrit).
#   - و / ي en fin de syllabe seulement après fatha (diphtongues « aw », « ay »).
#   - Pas deux voyelles longues ou deux soukoun qui se suivent.
#   - La chadda (lettre doublée) n'apparaît qu'en milieu de mot.

def _pick(options: list[str], avoid: set[str]) -> str:
    """Choisit au hasard en évitant certaines lettres si c'est possible."""
    preferred = [o for o in options if o not in avoid]
    return random.choice(preferred or options)


def generate_word(letters: set[str], syllables: int) -> str:
    consonants = consonants_of(letters)
    if not consonants:
        raise ValueError("Il faut au moins une lettre autre que ا")

    parts: list[str] = []
    avoid_next: set[str] = set()   # lettres à éviter en début de syllabe suivante
    geminate_next = False           # la prochaine attaque porte une chadda
    prev_coda: str | None = None    # consonne finale (avec soukoun) de la syllabe précédente

    for i in range(syllables):
        is_first, is_last = i == 0, i == syllables - 1
        vowel = random.choice(SHORT_VOWELS)

        # 1) Attaque : consonne, ou alif-hamza en tout début de mot.
        use_hamza = (
            is_first and ALLOW_INITIAL_HAMZA and "ا" in letters and random.random() < 0.2
        )
        if use_hamza:
            onset = "إ" if vowel == KASRA else "أ"
        else:
            onset = _pick(consonants, avoid_next)
            if onset == prev_coda:
                # « بْب » s'écrit « بّ » : on retire le soukoun et on met une chadda.
                parts.pop()
                geminate_next = True
        shadda = SHADDA if geminate_next else ""
        parts.append(onset + shadda + vowel)
        had_shadda, geminate_next = geminate_next, False

        # 2) Voyelle longue ?  (أَا s'écrirait آ : on l'évite)
        long_letter = LONG_VOWEL_LETTER[vowel]
        is_long = (
            long_letter in letters
            and random.random() < 0.35
            and not (use_hamza and vowel == FATHA)
            # « وُو » suivi d'un autre و serait illisible : pas de voyelle longue
            # au milieu du mot si cette lettre est la seule consonne disponible.
            and not (not is_last and set(consonants) <= {long_letter})
        )
        if is_long:
            parts.append(long_letter)

        # 3) Consonne finale avec soukoun ?
        if is_last:
            wants_coda = (not is_long) or random.random() < 0.5
        else:
            # Avec une seule consonne, une finale en milieu de mot devient toujours
            # une chadda (بْب → بّ) : on la rend plus rare pour ne pas en abuser.
            coda_rate = 0.35 if len(consonants) > 1 else 0.1
            wants_coda = (not is_long) and random.random() < coda_rate

        coda = None
        if wants_coda:
            allowed = [c for c in consonants if c not in SEMI_VOWELS or (vowel == FATHA and not is_long)]
            if not allowed and is_last and not is_long:
                # Seules و/ي sont disponibles : on force la fatha → diphtongue « aw » / « ay ».
                vowel = FATHA
                parts[-1] = parts[-1][:-1].replace("إ", "أ") + FATHA
                allowed = list(consonants)
            if allowed:
                coda = random.choice(allowed)
                parts.append(coda + SUKUN)

        # 4) Préparer la syllabe suivante.
        prev_coda = coda
        avoid_next = {coda} if coda else ({long_letter} if is_long else set())
        if (not is_last and not is_long and coda is None and not had_shadda
                and random.random() < 0.15):
            geminate_next = True

    return "".join(parts)


def generate_session_words(letters: set[str], count: int, length_key: str) -> list[str]:
    """Génère `count` mots différents (si possible) pour une série."""
    lo, hi = WORD_LENGTHS[length_key][1]
    words: list[str] = []
    for _ in range(count):
        for _attempt in range(40):
            word = generate_word(letters, random.randint(lo, hi))
            if word not in words:
                break
        words.append(word)
    return words


# ---------------------------------------------------------------------------
# Synthèse vocale (fichiers temporaires)
# ---------------------------------------------------------------------------

async def _synthesize_edge(text: str, dest: Path) -> None:
    communicate = edge_tts.Communicate(text, TTS_VOICE, rate=TTS_RATE)
    await communicate.save(str(dest))
    if not dest.exists() or dest.stat().st_size == 0:
        raise RuntimeError("fichier audio vide")


def _synthesize_gtts(text: str, dest: Path) -> None:
    gTTS(text=text, lang="ar", slow=True).save(str(dest))


async def synthesize(text: str) -> Path:
    """Crée un MP3 temporaire prononçant `text`. L'appelant doit le supprimer."""
    fd, name = tempfile.mkstemp(suffix=".mp3", dir=AUDIO_TMP_DIR)
    os.close(fd)
    path = Path(name)
    try:
        try:
            await _synthesize_edge(text, path)
        except Exception as exc:  # réseau, service indisponible…
            logger.warning("edge-tts en échec (%s) → repli sur gTTS", exc)
            await asyncio.to_thread(_synthesize_gtts, text, path)
        return path
    except Exception:
        path.unlink(missing_ok=True)
        raise


def clean_temp_audio() -> None:
    """Supprime les fichiers audio laissés par un arrêt brutal du bot."""
    for leftover in AUDIO_TMP_DIR.glob("*.mp3"):
        leftover.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Claviers & textes
# ---------------------------------------------------------------------------

def letters_keyboard(selected: set[str]) -> InlineKeyboardMarkup:
    """Grille des 28 lettres, 4 par ligne, lue de droite à gauche comme l'arabe."""
    rows: list[list[InlineKeyboardButton]] = []
    for start in range(0, len(ALPHABET), LETTERS_PER_ROW):
        row = []
        for i in range(start, min(start + LETTERS_PER_ROW, len(ALPHABET))):
            letter = ALPHABET[i]
            label = f"✅ {letter}" if letter in selected else letter
            row.append(InlineKeyboardButton(label, callback_data=f"L:{i}"))
        rows.append(list(reversed(row)))  # ا en haut à droite
    rows.append([
        InlineKeyboardButton("Tout sélectionner", callback_data="L:ALL"),
        InlineKeyboardButton("Tout réinitialiser", callback_data="L:RESET"),
    ])
    rows.append([InlineKeyboardButton("💾 Enregistrer", callback_data="L:SAVE")])
    return InlineKeyboardMarkup(rows)


def letters_text(selected: set[str]) -> str:
    return (
        "🔤 <b>Lettres apprises</b>\n"
        "Touche une lettre pour la cocher ou la décocher, puis enregistre.\n\n"
        f"Sélection : <b>{len(selected)}/{len(ALPHABET)}</b>"
    )


def word_caption(index: int, total: int) -> str:
    return f"🎧 <b>Mot {index + 1}/{total}</b> — écoute et écris-le sur ta feuille."


async def safe_edit_text(query, text: str, reply_markup=None) -> None:
    """edit_message_text qui ignore l'erreur « message is not modified »."""
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=reply_markup)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


def letters_problem(letters: set[str]) -> str | None:
    """Renvoie un message d'erreur si la sélection ne permet pas de dictée."""
    if len(letters) < MIN_LETTERS:
        return f"⚠️ Sélectionne au moins {MIN_LETTERS} lettres avec /lettres avant de lancer une dictée."
    if not consonants_of(letters):
        return "⚠️ Coche au moins une lettre en plus de ا avec /lettres."
    return None


# ---------------------------------------------------------------------------
# Commandes
# ---------------------------------------------------------------------------

HELP_TEXT = (
    "السَّلَامُ عَلَيْكُم 👋\n\n"
    "Je t'aide à t'entraîner à la <b>dictée en arabe</b>.\n\n"
    "1️⃣ /lettres — coche les lettres que tu as déjà apprises\n"
    "2️⃣ /dictee — je t'invente des mots avec uniquement ces lettres\n"
    "⏹ /stop — arrête la dictée en cours\n\n"
    "Pour chaque mot : écoute la note vocale, écris le mot, puis touche "
    "« 👁️ Afficher la réponse » pour te corriger.\n"
    "ℹ️ Les mots sont inventés : ils n'ont pas forcément de sens, c'est normal !"
)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.effective_message.reply_text(HELP_TEXT, parse_mode=ParseMode.HTML)


async def cmd_letters(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    # Brouillon : rien n'est pris en compte tant que l'élève n'a pas enregistré.
    draft = set(context.user_data.get("letters", set()))
    context.user_data["draft_letters"] = draft
    await update.effective_message.reply_text(
        letters_text(draft), parse_mode=ParseMode.HTML, reply_markup=letters_keyboard(draft)
    )


async def cmd_dictation(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_dictation_menu(update.effective_chat.id, context)


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if context.user_data.pop("session", None):
        await update.effective_message.reply_text("⏹ Dictée arrêtée. Relance-la avec /dictee.")
    else:
        await update.effective_message.reply_text("Aucune dictée en cours.")


# ---------------------------------------------------------------------------
# /lettres — boutons
# ---------------------------------------------------------------------------

async def on_letters(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    action = query.data.split(":", 1)[1]
    draft: set[str] = context.user_data.setdefault(
        "draft_letters", set(context.user_data.get("letters", set()))
    )

    if action == "SAVE":
        context.user_data["letters"] = set(draft)
        await query.answer("Sélection enregistrée ✅")
        letters_line = " ".join(ordered(draft)) or "aucune"
        problem = letters_problem(draft)
        next_step = problem or "Lance /dictee quand tu es prêt."
        await safe_edit_text(
            query,
            f"💾 <b>{len(draft)} lettre(s) enregistrée(s)</b>\n{letters_line}\n\n{next_step}",
        )
        return

    if action == "ALL":
        draft.update(ALPHABET)
    elif action == "RESET":
        draft.clear()
    else:
        letter = ALPHABET[int(action)]
        if letter in draft:
            draft.discard(letter)
        else:
            draft.add(letter)

    await query.answer()
    await safe_edit_text(query, letters_text(draft), reply_markup=letters_keyboard(draft))


# ---------------------------------------------------------------------------
# /dictee — menu, déroulement, bilan
# ---------------------------------------------------------------------------

async def send_dictation_menu(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    letters: set[str] = context.user_data.get("letters", set())
    problem = letters_problem(letters)
    if problem:
        await context.bot.send_message(chat_id, problem)
        return

    buttons = [InlineKeyboardButton(f"{n} mots", callback_data=f"C:{n}") for n in SESSION_SIZES]
    await context.bot.send_message(
        chat_id,
        f"📝 <b>Nouvelle dictée</b>\n"
        f"Lettres : {' '.join(ordered(letters))}\n\n"
        "Combien de mots veux-tu ?",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([buttons]),
    )


async def on_choose_count(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Étape 2 du menu : choix de la longueur des mots."""
    query = update.callback_query
    await query.answer()
    count = int(query.data.split(":", 1)[1])
    buttons = [
        InlineKeyboardButton(label, callback_data=f"G:{count}:{key}")
        for key, (label, _) in WORD_LENGTHS.items()
    ]
    await safe_edit_text(
        query,
        f"📝 <b>{count} mots</b>\nQuelle longueur de mots ?",
        reply_markup=InlineKeyboardMarkup([buttons]),
    )


async def on_start_session(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    _, raw_count, length_key = query.data.split(":")
    count = int(raw_count)

    letters: set[str] = context.user_data.get("letters", set())
    problem = letters_problem(letters)
    if problem or length_key not in WORD_LENGTHS:
        await safe_edit_text(query, problem or "⚠️ Relance /dictee.")
        return

    context.user_data["session"] = {
        "id": secrets.token_hex(4),  # identifie la série → les vieux boutons deviennent inactifs
        "words": generate_session_words(letters, count, length_key),
        "index": 0,
    }
    await safe_edit_text(
        query,
        f"🎧 <b>C'est parti : {count} mots {WORD_LENGTHS[length_key][0].lower()}</b>\n"
        "Écoute, écris le mot sur ta feuille, puis vérifie.\n"
        "Tu peux réécouter la note vocale autant de fois que tu veux.",
    )
    await send_current_word(query.message.chat_id, context)


async def send_current_word(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    session = context.user_data["session"]
    index = session["index"]
    total = len(session["words"])
    word = session["words"][index]

    reveal_kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("👁️ Afficher la réponse", callback_data=f"R:{session['id']}:{index}")
    ]])

    await context.bot.send_chat_action(chat_id, ChatAction.RECORD_VOICE)
    audio_path: Path | None = None
    try:
        audio_path = await synthesize(word)
        with audio_path.open("rb") as audio:
            await context.bot.send_voice(
                chat_id,
                voice=audio,
                caption=word_caption(index, total),
                parse_mode=ParseMode.HTML,
                reply_markup=reveal_kb,
            )
    except Exception:
        logger.exception("Échec de l'envoi audio pour %s", word)
        skip_kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("➡️ Mot suivant", callback_data=f"N:{session['id']}:{index}")
        ]])
        await context.bot.send_message(
            chat_id,
            f"❌ Impossible de générer l'audio du mot {index + 1}/{total} pour le moment.",
            reply_markup=skip_kb,
        )
    finally:
        if audio_path:
            audio_path.unlink(missing_ok=True)  # nettoyage du fichier temporaire


def _active_session(context: ContextTypes.DEFAULT_TYPE, data: str) -> tuple[dict, int] | None:
    """Vérifie qu'un bouton appartient bien à la dictée en cours."""
    _, session_id, raw_index = data.split(":")
    session = context.user_data.get("session")
    index = int(raw_index)
    if not session or session["id"] != session_id or index >= len(session["words"]):
        return None
    return session, index


async def on_reveal(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    found = _active_session(context, query.data)
    if not found:
        await query.answer("Cette dictée est terminée. Relance /dictee.")
        return
    session, index = found
    await query.answer()

    word = session["words"][index]
    total = len(session["words"])
    is_last = index == total - 1

    next_kb = InlineKeyboardMarkup([[
        InlineKeyboardButton(
            "🏁 Voir le bilan" if is_last else "➡️ Mot suivant",
            callback_data=f"N:{session['id']}:{index}",
        )
    ]])
    caption = (
        f"🎧 <b>Mot {index + 1}/{total}</b>\n\n"
        f"✍️ <b>{html.escape(word)}</b>\n"
        f"🔤 {html.escape(spelled_letters(word))}"
    )
    try:
        await query.edit_message_caption(caption=caption, parse_mode=ParseMode.HTML, reply_markup=next_kb)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


async def on_next(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    found = _active_session(context, query.data)
    # session["index"] != index → bouton déjà utilisé (double clic) : on ignore.
    if not found or found[0]["index"] != found[1]:
        await query.answer("C'est déjà fait ✔️")
        return
    session, _ = found
    await query.answer()

    try:
        await query.edit_message_reply_markup(reply_markup=None)  # garde le fil propre
    except BadRequest:
        pass

    session["index"] += 1
    chat_id = query.message.chat_id
    if session["index"] >= len(session["words"]):
        await send_summary(chat_id, context)
    else:
        await send_current_word(chat_id, context)


async def send_summary(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    session = context.user_data.pop("session")
    lines = [
        f"{i}. <b>{html.escape(word)}</b>   ({html.escape(spelled_letters(word))})"
        for i, word in enumerate(session["words"], start=1)
    ]
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Nouvelle dictée", callback_data="D:NEW")]])
    await context.bot.send_message(
        chat_id,
        f"🏁 <b>Bilan de la dictée</b> — {len(lines)} mots\n\n"
        + "\n".join(lines)
        + "\n\n📄 Compare avec ta feuille. بَارَكَ اللهُ فِيكَ !",
        parse_mode=ParseMode.HTML,
        reply_markup=kb,
    )


async def on_new_dictation(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except BadRequest:
        pass
    await send_dictation_menu(query.message.chat_id, context)


# ---------------------------------------------------------------------------
# Démarrage
# ---------------------------------------------------------------------------

async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.error("Erreur non gérée", exc_info=context.error)


async def post_init(app: Application) -> None:
    """Affiche les commandes dans le menu « / » de Telegram."""
    await app.bot.set_my_commands([
        BotCommand("lettres", "Choisir les lettres apprises"),
        BotCommand("dictee", "Lancer une dictée"),
        BotCommand("stop", "Arrêter la dictée en cours"),
        BotCommand("aide", "Comment ça marche"),
    ])


def build_application(token: str, builder=None) -> Application:
    """Assemble le bot (séparé de main() pour pouvoir le tester)."""
    AUDIO_TMP_DIR.mkdir(exist_ok=True)
    clean_temp_audio()

    builder = builder or Application.builder()
    app = (
        builder.token(token)
        .persistence(PicklePersistence(filepath=PERSISTENCE_FILE))
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler(["start", "aide"], cmd_start))
    app.add_handler(CommandHandler("lettres", cmd_letters))
    app.add_handler(CommandHandler("dictee", cmd_dictation))
    app.add_handler(CommandHandler("stop", cmd_stop))

    app.add_handler(CallbackQueryHandler(on_letters, pattern=r"^L:"))
    app.add_handler(CallbackQueryHandler(on_choose_count, pattern=r"^C:\d+$"))
    app.add_handler(CallbackQueryHandler(on_start_session, pattern=r"^G:\d+:\w+$"))
    app.add_handler(CallbackQueryHandler(on_reveal, pattern=r"^R:"))
    app.add_handler(CallbackQueryHandler(on_next, pattern=r"^N:"))
    app.add_handler(CallbackQueryHandler(on_new_dictation, pattern=r"^D:NEW$"))

    app.add_error_handler(on_error)
    return app


def main() -> None:
    if not TOKEN or TOKEN.startswith("COLLE_"):
        raise SystemExit(
            "TELEGRAM_BOT_TOKEN manquant : ouvre le fichier config.txt et colle le token donné par @BotFather."
        )
    app = build_application(TOKEN)
    logger.info("Bot démarré — laisse cette fenêtre ouverte. Ctrl+C pour arrêter.")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
