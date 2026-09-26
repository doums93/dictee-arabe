"""
Bot Telegram — Dictée en arabe pour débutants.

Principe :
  1. /lettres   → l'élève coche les lettres qu'il a déjà apprises.
  2. /reglages  → il choisit ce qu'il a déjà vu : voyelles longues, soukoun, chadda,
                  hamza, ainsi que la vitesse et la voix (/voix).
  3. /dictee    → nombre de mots, longueur, puis c'est parti.
     Le bot pioche d'abord de VRAIS mots (mots.json, avec traduction) qui ne
     contiennent que les lettres et les signes autorisés, et complète avec des
     mots INVENTÉS (signalés comme tels) : la réserve de mots est infinie.
  4. Chaque mot est envoyé en note vocale, sans l'écriture.
     « 👁️ Afficher la réponse » révèle le mot vocalisé (+ traduction ou « mot inventé »).
     « 🐢 Plus lentement » renvoie le même mot au ralenti.
  5. À la fin, un bilan récapitule la série.

Choix techniques :
  - python-telegram-bot v22 (async).
  - Synthèse vocale : edge-tts (voix neuronales Microsoft, gratuites), repli sur gTTS.
  - Audios écrits dans des fichiers temporaires, supprimés juste après l'envoi.
  - PicklePersistence : lettres et réglages de chaque élève conservés au redémarrage
    (sur Railway, attacher un volume pour les garder aussi lors des mises à jour).
"""

from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import random
import re
import secrets
import tempfile
from dataclasses import dataclass
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
load_dotenv(BASE_DIR / "config.txt")  # TELEGRAM_BOT_TOKEN=... (et réglages optionnels)
# Sur un serveur, le token peut être écrit dans config.local.txt (jamais envoyé sur GitHub).
load_dotenv(BASE_DIR / "config.local.txt", override=True)

# Dossier des données : DATA_DIR, sinon le volume Railway s'il existe, sinon le dossier du bot.
DATA_DIR = Path(os.getenv("DATA_DIR") or os.getenv("RAILWAY_VOLUME_MOUNT_PATH") or BASE_DIR)
AUDIO_TMP_DIR = DATA_DIR / "audio_tmp"            # fichiers audio temporaires
PERSISTENCE_FILE = DATA_DIR / "bot_data.pickle"   # lettres et réglages de chaque élève
WORDS_FILE = BASE_DIR / "mots.json"               # banque de vrais mots vocalisés

TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
DEFAULT_VOICE = os.getenv("TTS_VOICE", "ar-SA-HamedNeural")

# Voix masculines proposées dans /voix (identifiant edge-tts, nom affiché).
VOICES = [
    ("ar-SA-HamedNeural", "Hamed — Arabie saoudite"),
    ("ar-EG-ShakirNeural", "Shakir — Égypte"),
    ("ar-AE-HamdanNeural", "Hamdan — Émirats"),
    ("ar-JO-TaimNeural", "Taim — Jordanie"),
    ("ar-KW-FahedNeural", "Fahed — Koweït"),
    ("ar-QA-MoazNeural", "Moaz — Qatar"),
]
VOICE_SAMPLE = "بَابْ ، كِتَابْ ، قَلَمْ ، شَمْسْ"

# Vitesses proposées dans /reglages (clé : libellé, débit edge-tts).
SPEEDS = {
    "normale": ("Normale", "+0%"),
    "lente": ("Lente", "-20%"),
    "tres_lente": ("Très lente", "-40%"),
}
SLOW_REPLAY_RATE = "-50%"   # bouton « 🐢 Plus lentement »

# Réglages par défaut d'un nouvel élève.
DEFAULT_SETTINGS = {
    "long": True,      # voyelles longues (ا و ي)
    "sukun": False,    # soukoun ( ْ )
    "shadda": False,   # chadda ( ّ )
    "hamza": False,    # hamza sur alif (أ إ)
    "speed": "lente",
    "voice": DEFAULT_VOICE,
}

SESSION_SIZES = (3, 5, 10)
MIN_LETTERS = 2
LETTERS_PER_ROW = 4
REAL_WORD_RATIO = 0.7   # part de vrais mots dans une dictée (le reste est inventé)
RECENT_REAL_MAX = 80    # vrais mots mémorisés pour éviter de les redonner trop vite

# Longueur des mots, en nombre de syllabes (min, max).
WORD_LENGTHS = {
    "court": ("Courts", (1, 2)),
    "moyen": ("Moyens", (2, 3)),
    "long": ("Longs", (3, 4)),
}

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=logging.INFO,
)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger = logging.getLogger("dictee_arabe")

# ---------------------------------------------------------------------------
# Alphabet et signes
# ---------------------------------------------------------------------------

ALPHABET = [
    "ا", "ب", "ت", "ث", "ج", "ح", "خ", "د", "ذ", "ر", "ز", "س", "ش", "ص",
    "ض", "ط", "ظ", "ع", "غ", "ف", "ق", "ك", "ل", "م", "ن", "ه", "و", "ي",
]
ALPHABET_SET = frozenset(ALPHABET)

FATHA, DAMMA, KASRA = "\u064E", "\u064F", "\u0650"   # a, ou, i
SUKUN, SHADDA = "\u0652", "\u0651"
SHORT_VOWELS = (FATHA, DAMMA, KASRA)
MARKS = frozenset(SHORT_VOWELS + (SUKUN, SHADDA))
LONG_VOWEL_LETTER = {FATHA: "ا", DAMMA: "و", KASRA: "ي"}  # aa, ouu, ii
SEMI_VOWELS = ("و", "ي")
HAMZA_ALIFS = ("أ", "إ")

DIACRITICS_RE = re.compile(r"[\u064B-\u065F\u0670]")


def ordered(letters: set[str]) -> list[str]:
    """Trie un ensemble de lettres dans l'ordre alphabétique arabe."""
    return [letter for letter in ALPHABET if letter in letters]


def consonants_of(letters: set[str]) -> list[str]:
    """Lettres utilisables comme consonnes (toutes sauf l'alif)."""
    return [letter for letter in ordered(letters) if letter != "ا"]


def spelled_letters(word: str) -> str:
    """بَابْ → « ب · ا · ب » : aide à vérifier lettre par lettre."""
    return " · ".join(DIACRITICS_RE.sub("", word))


# ---------------------------------------------------------------------------
# Analyse d'un mot vocalisé
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class WordInfo:
    arabic: str
    french: str | None          # None = mot inventé
    consonants: frozenset[str]  # lettres portant une voyelle, un soukoun ou une chadda
    madd: bool                  # contient une voyelle longue
    sukun: bool
    shadda: bool
    hamza: bool                 # contient أ ou إ
    syllables: int              # nombre de voyelles courtes


def analyze_word(word: str, french: str | None = None) -> WordInfo:
    """Décompose un mot entièrement vocalisé et vérifie qu'il est bien écrit.

    Lève ValueError si le mot contient un caractère non géré (ة, ى, ء, tanwîn…),
    une lettre sans signe, ou une voyelle longue mal placée.
    """
    units: list[tuple[str, set[str]]] = []
    for ch in word:
        if ch in MARKS:
            if not units:
                raise ValueError("signe sans lettre")
            units[-1][1].add(ch)
        elif ch in ALPHABET_SET or ch in HAMZA_ALIFS:
            units.append((ch, set()))
        else:
            raise ValueError(f"caractère non géré : {ch!r}")
    if not units:
        raise ValueError("mot vide")

    consonants: set[str] = set()
    madd = sukun = shadda = hamza = False
    syllables = 0
    prev_vowel: str | None = None

    for letter, marks in units:
        vowels = marks & set(SHORT_VOWELS)
        if len(vowels) > 1:
            raise ValueError("deux voyelles sur une lettre")
        vowel = next(iter(vowels), None)

        if letter in HAMZA_ALIFS:
            if not marks:
                raise ValueError("hamza sans signe")
            hamza = True
        elif letter == "ا":
            if marks:
                raise ValueError("alif avec un signe (hamzat al-wasl non géré)")
            if prev_vowel != FATHA:
                raise ValueError("alif de prolongation sans fatha avant")
            madd = True
            prev_vowel = None
            continue
        elif letter in SEMI_VOWELS and not marks:
            expected = DAMMA if letter == "و" else KASRA
            if prev_vowel != expected:
                raise ValueError(f"{letter} sans signe et sans la bonne voyelle avant")
            madd = True
            prev_vowel = None
            continue
        elif not marks:
            raise ValueError(f"lettre {letter} sans signe")
        else:
            consonants.add(letter)

        sukun |= SUKUN in marks
        shadda |= SHADDA in marks
        if vowel:
            syllables += 1
        prev_vowel = vowel

    return WordInfo(word, french, frozenset(consonants), madd, sukun, shadda, hamza, syllables)


def is_allowed(info: WordInfo, letters: set[str], settings: dict) -> bool:
    """Le mot ne contient-il que des lettres et des signes déjà vus ?"""
    if not info.consonants <= letters:
        return False
    if info.madd and not settings["long"]:
        return False
    if info.sukun and not settings["sukun"]:
        return False
    if info.shadda and not settings["shadda"]:
        return False
    if info.hamza and not (settings["hamza"] and "ا" in letters):
        return False
    return True


# ---------------------------------------------------------------------------
# Banque de vrais mots
# ---------------------------------------------------------------------------

REAL_WORDS: list[WordInfo] = []


def load_word_bank(path: Path) -> list[WordInfo]:
    """Charge mots.json ; les mots mal écrits sont signalés dans les logs et ignorés."""
    if not path.exists():
        logger.warning("%s introuvable : seuls des mots inventés seront proposés", path.name)
        return []
    bank: list[WordInfo] = []
    seen: set[str] = set()
    for entry in json.loads(path.read_text(encoding="utf-8")):
        arabic, french = entry["mot"].strip(), entry.get("fr", "").strip()
        if arabic in seen:
            continue
        try:
            bank.append(analyze_word(arabic, french or "—"))
            seen.add(arabic)
        except ValueError as exc:
            logger.warning("Mot ignoré dans %s : %s (%s)", path.name, arabic, exc)
    logger.info("%d vrais mots chargés depuis %s", len(bank), path.name)
    return bank


def eligible_real_words(letters: set[str], settings: dict, length_key: str) -> list[WordInfo]:
    lo, hi = WORD_LENGTHS[length_key][1]
    return [
        w for w in REAL_WORDS
        if is_allowed(w, letters, settings) and lo <= max(w.syllables, 1) <= hi
    ]


# ---------------------------------------------------------------------------
# Générateur de mots inventés
# ---------------------------------------------------------------------------
#
# Un mot = une suite de syllabes : consonne (+ chadda) + voyelle courte
#   (+ voyelle longue) (+ consonne finale avec soukoun).
# Règles :
#   - seules les lettres cochées servent de consonnes ;
#   - voyelles longues : ا و ي sont utilisées dès que l'option est active,
#     et chaque mot en contient au moins une ;
#   - soukoun, chadda, hamza : uniquement si l'option est active ;
#   - avec le soukoun, le mot se termine par une consonne + soukoun ou une voyelle
#     longue (prononciation d'un mot isolé) ;
#   - و / ي avec soukoun seulement après une fatha (« aw », « ay ») ;
#   - « بْب » est toujours écrit « بّ ».

def _pick(options: list[str], avoid: set[str]) -> str:
    preferred = [o for o in options if o not in avoid]
    return random.choice(preferred or options)


def generate_word(letters: set[str], syllables: int, settings: dict) -> str:
    consonants = consonants_of(letters)
    if not consonants:
        raise ValueError("Il faut au moins une lettre autre que ا")
    long_ok, sukun_ok = settings["long"], settings["sukun"]
    shadda_ok = settings["shadda"]
    hamza_ok = settings["hamza"] and "ا" in letters

    forced_long = random.randrange(syllables) if long_ok else None
    parts: list[str] = []
    avoid_next: set[str] = set()
    geminate_next = False
    prev_coda: str | None = None

    for i in range(syllables):
        is_first, is_last = i == 0, i == syllables - 1

        # 1) Attaque : alif-hamza (début de mot) ou consonne.
        use_hamza = is_first and hamza_ok and random.random() < 0.2
        onset = None
        if not use_hamza:
            onset = _pick(consonants, avoid_next)
            if onset == prev_coda:
                parts.pop()  # retire « consonne + soukoun » de la syllabe précédente
                if shadda_ok:
                    geminate_next = True      # « بْب » → « بّ »
        had_shadda = geminate_next

        # 2) Voyelle courte, puis voyelle longue éventuelle.
        want_long = long_ok and (i == forced_long or random.random() < 0.3)
        vowel_choices = list(SHORT_VOWELS)
        if want_long:
            vowel_choices = [
                v for v in SHORT_VOWELS
                if not (use_hamza and v == FATHA)  # أَا s'écrirait آ
                # « وُو » suivi d'un autre و serait illisible
                and not (not is_last and set(consonants) <= {LONG_VOWEL_LETTER[v]})
            ]
            if not vowel_choices:
                want_long, vowel_choices = False, list(SHORT_VOWELS)
        vowel = random.choice(vowel_choices)

        if use_hamza:
            onset = "إ" if vowel == KASRA else "أ"
        parts.append(onset + (SHADDA if geminate_next else "") + vowel)
        geminate_next = False

        long_letter = LONG_VOWEL_LETTER[vowel]
        if want_long:
            parts.append(long_letter)

        # 3) Consonne finale avec soukoun ?
        coda = None
        if sukun_ok:
            if is_last:
                wants_coda = (not want_long) or random.random() < 0.5
            else:
                rate = 0.35 if len(consonants) > 1 else 0.1
                wants_coda = (not want_long) and random.random() < rate
            if wants_coda:
                allowed = [
                    c for c in consonants
                    if c not in SEMI_VOWELS or (vowel == FATHA and not want_long)
                ]
                if not allowed and is_last and not want_long:
                    # Seules و/ي sont disponibles : fatha forcée → « aw » / « ay ».
                    vowel = FATHA
                    parts[-1] = parts[-1][:-1].replace("إ", "أ") + FATHA
                    allowed = list(consonants)
                if allowed:
                    coda = random.choice(allowed)
                    parts.append(coda + SUKUN)

        # 4) Préparer la syllabe suivante.
        prev_coda = coda
        avoid_next = {coda} if coda else ({long_letter} if want_long else set())
        gem_rate = 0.15 if sukun_ok else 0.25
        if (shadda_ok and not is_last and not want_long and coda is None
                and not had_shadda and random.random() < gem_rate):
            geminate_next = True

    return "".join(parts)


def invented_word(letters: set[str], length_key: str, settings: dict) -> WordInfo:
    lo, hi = WORD_LENGTHS[length_key][1]
    return analyze_word(generate_word(letters, random.randint(lo, hi), settings))


def build_session_words(
    letters: set[str], settings: dict, count: int, length_key: str, recent: list[str]
) -> list[dict]:
    """Mélange de vrais mots (priorité aux moins récents) et de mots inventés."""
    pool = eligible_real_words(letters, settings, length_key)
    random.shuffle(pool)
    pool.sort(key=lambda w: w.arabic in recent)  # les mots non vus récemment d'abord
    n_real = min(len(pool), round(count * REAL_WORD_RATIO))
    chosen = pool[:n_real]

    taken = {w.arabic for w in chosen}
    while len(chosen) < count:
        for _ in range(40):
            word = invented_word(letters, length_key, settings)
            if word.arabic not in taken:
                break
        taken.add(word.arabic)
        chosen.append(word)

    random.shuffle(chosen)
    return [{"ar": w.arabic, "fr": w.french} for w in chosen]


# ---------------------------------------------------------------------------
# Synthèse vocale (fichiers temporaires)
# ---------------------------------------------------------------------------

async def _synthesize_edge(text: str, voice: str, rate: str, dest: Path) -> None:
    communicate = edge_tts.Communicate(text, voice, rate=rate)
    await communicate.save(str(dest))
    if not dest.exists() or dest.stat().st_size == 0:
        raise RuntimeError("fichier audio vide")


def _synthesize_gtts(text: str, dest: Path) -> None:
    gTTS(text=text, lang="ar", slow=True).save(str(dest))


async def synthesize(text: str, voice: str, rate: str) -> Path:
    """Crée un MP3 temporaire prononçant `text`. L'appelant doit le supprimer."""
    fd, name = tempfile.mkstemp(suffix=".mp3", dir=AUDIO_TMP_DIR)
    os.close(fd)
    path = Path(name)
    try:
        try:
            await _synthesize_edge(text, voice, rate, path)
        except Exception as exc:
            logger.warning("edge-tts en échec avec %s (%s)", voice, exc)
            if voice != DEFAULT_VOICE:
                try:
                    await _synthesize_edge(text, DEFAULT_VOICE, rate, path)
                    return path
                except Exception:
                    pass
            await asyncio.to_thread(_synthesize_gtts, text, path)
        return path
    except Exception:
        path.unlink(missing_ok=True)
        raise


async def send_voice_note(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, text: str, voice: str, rate: str,
    caption: str, reply_markup: InlineKeyboardMarkup | None = None,
) -> None:
    await context.bot.send_chat_action(chat_id, ChatAction.RECORD_VOICE)
    path = await synthesize(text, voice, rate)
    try:
        with path.open("rb") as audio:
            await context.bot.send_voice(
                chat_id, voice=audio, caption=caption,
                parse_mode=ParseMode.HTML, reply_markup=reply_markup,
            )
    finally:
        path.unlink(missing_ok=True)  # nettoyage du fichier temporaire


def clean_temp_audio() -> None:
    for leftover in AUDIO_TMP_DIR.glob("*.mp3"):
        leftover.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Réglages de l'élève
# ---------------------------------------------------------------------------

def settings_of(context: ContextTypes.DEFAULT_TYPE) -> dict:
    settings = context.user_data.setdefault("settings", {})
    for key, value in DEFAULT_SETTINGS.items():
        settings.setdefault(key, value)
    if settings["voice"] not in {v for v, _ in VOICES}:
        settings["voice"] = DEFAULT_VOICE
    return settings


def voice_label(voice: str) -> str:
    return next((label for v, label in VOICES if v == voice), voice)


def settings_summary(settings: dict) -> str:
    def mark(key: str) -> str:
        return "✅" if settings[key] else "❌"
    return (
        f"{mark('long')} voyelles longues   {mark('sukun')} soukoun   "
        f"{mark('shadda')} chadda   {mark('hamza')} hamza\n"
        f"🔊 {voice_label(settings['voice']).split(' —')[0]}, vitesse "
        f"{SPEEDS[settings['speed']][0].lower()}"
    )


def settings_keyboard(settings: dict) -> InlineKeyboardMarkup:
    def toggle(key: str, label: str) -> InlineKeyboardButton:
        return InlineKeyboardButton(f"{'✅' if settings[key] else '❌'} {label}", callback_data=f"O:{key}")
    return InlineKeyboardMarkup([
        [toggle("long", "Voyelles longues (ا و ي)")],
        [toggle("sukun", "Soukoun ( ـْ )"), toggle("shadda", "Chadda ( ـّ )")],
        [toggle("hamza", "Hamza (أ إ)")],
        [InlineKeyboardButton(f"🐢 Vitesse : {SPEEDS[settings['speed']][0]}", callback_data="O:speed")],
        [InlineKeyboardButton(f"🎙️ Voix : {voice_label(settings['voice'])}", callback_data="O:voice")],
    ])


SETTINGS_TEXT = (
    "⚙️ <b>Réglages de ta dictée</b>\n"
    "Touche une option pour l'activer ✅ ou la désactiver ❌.\n"
    "Active seulement ce que tu as déjà vu en cours."
)


def voices_keyboard(current: str) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton(("✅ " if v == current else "▶️ ") + label, callback_data=f"V:{i}")]
        for i, (v, label) in enumerate(VOICES)
    ]
    return InlineKeyboardMarkup(rows)


# ---------------------------------------------------------------------------
# Claviers et textes communs
# ---------------------------------------------------------------------------

def letters_keyboard(selected: set[str]) -> InlineKeyboardMarkup:
    """Grille des 28 lettres, 4 par ligne, lue de droite à gauche."""
    rows: list[list[InlineKeyboardButton]] = []
    for start in range(0, len(ALPHABET), LETTERS_PER_ROW):
        row = []
        for i in range(start, min(start + LETTERS_PER_ROW, len(ALPHABET))):
            letter = ALPHABET[i]
            label = f"✅ {letter}" if letter in selected else letter
            row.append(InlineKeyboardButton(label, callback_data=f"L:{i}"))
        rows.append(list(reversed(row)))
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


def letters_problem(letters: set[str]) -> str | None:
    if len(letters) < MIN_LETTERS:
        return f"⚠️ Sélectionne au moins {MIN_LETTERS} lettres avec /lettres avant de lancer une dictée."
    if not consonants_of(letters):
        return "⚠️ Coche au moins une lettre en plus de ا avec /lettres."
    return None


async def safe_edit_text(query, text: str, reply_markup=None) -> None:
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=reply_markup)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


def word_keyboard(session: dict, index: int, revealed: bool) -> InlineKeyboardMarkup:
    sid = session["id"]
    is_last = index == len(session["words"]) - 1
    first = (
        InlineKeyboardButton("🏁 Voir le bilan" if is_last else "➡️ Mot suivant", callback_data=f"N:{sid}:{index}")
        if revealed
        else InlineKeyboardButton("👁️ Afficher la réponse", callback_data=f"R:{sid}:{index}")
    )
    return InlineKeyboardMarkup([
        [first],
        [InlineKeyboardButton("🐢 Réécouter plus lentement", callback_data=f"S:{sid}:{index}")],
    ])


def meaning_line(word: dict) -> str:
    if word["fr"]:
        return f"🇫🇷 {html.escape(word['fr'])}"
    return "🧪 <i>Mot inventé (pas de sens), juste pour l'entraînement</i>"


# ---------------------------------------------------------------------------
# Commandes
# ---------------------------------------------------------------------------

HELP_TEXT = (
    "السَّلَامُ عَلَيْكُم 👋\n\n"
    "Je t'aide à t'entraîner à la <b>dictée en arabe</b>.\n\n"
    "1️⃣ /lettres : coche les lettres que tu as déjà apprises\n"
    "2️⃣ /reglages : voyelles longues, soukoun, chadda, hamza, vitesse\n"
    "3️⃣ /dictee : lance une dictée avec uniquement ce que tu as vu\n"
    "🎙️ /voix : choisis la voix qui te parle le mieux\n"
    "⏹ /stop : arrête la dictée en cours\n\n"
    "Je te dicte surtout de vrais mots (avec leur traduction), et j'invente des mots "
    "quand il n'en existe pas assez avec tes lettres : ils sont signalés 🧪."
)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.effective_message.reply_text(HELP_TEXT, parse_mode=ParseMode.HTML)


async def cmd_letters(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    draft = set(context.user_data.get("letters", set()))
    context.user_data["draft_letters"] = draft
    await update.effective_message.reply_text(
        letters_text(draft), parse_mode=ParseMode.HTML, reply_markup=letters_keyboard(draft)
    )


async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    settings = settings_of(context)
    await update.effective_message.reply_text(
        SETTINGS_TEXT, parse_mode=ParseMode.HTML, reply_markup=settings_keyboard(settings)
    )


async def cmd_voices(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_voices_menu(update.effective_chat.id, context)


async def send_voices_menu(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    settings = settings_of(context)
    await context.bot.send_message(
        chat_id,
        "🎙️ <b>Choix de la voix</b>\n"
        "Touche une voix pour l'écouter, puis garde celle que tu comprends le mieux.",
        parse_mode=ParseMode.HTML,
        reply_markup=voices_keyboard(settings["voice"]),
    )


async def cmd_dictation(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_dictation_menu(update.effective_chat.id, context)


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if context.user_data.pop("session", None):
        await update.effective_message.reply_text("⏹ Dictée arrêtée. Relance-la avec /dictee.")
    else:
        await update.effective_message.reply_text("Aucune dictée en cours.")


# ---------------------------------------------------------------------------
# /lettres, /reglages, /voix — boutons
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
        next_step = letters_problem(draft) or "Lance /dictee quand tu es prêt."
        await safe_edit_text(
            query,
            f"💾 <b>{len(draft)} lettre(s) enregistrée(s)</b>\n{letters_line}\n\n"
            "ℹ️ Les voyelles longues (ا و ي) sont utilisées automatiquement si elles "
            "sont activées dans /reglages.\n\n" + next_step,
        )
        return

    if action == "ALL":
        draft.update(ALPHABET)
    elif action == "RESET":
        draft.clear()
    else:
        letter = ALPHABET[int(action)]
        draft.symmetric_difference_update({letter})

    await query.answer()
    await safe_edit_text(query, letters_text(draft), reply_markup=letters_keyboard(draft))


async def on_setting(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    key = query.data.split(":", 1)[1]
    settings = settings_of(context)

    if key == "voice":
        await query.answer()
        await send_voices_menu(query.message.chat_id, context)
        return
    if key == "speed":
        order = list(SPEEDS)
        settings["speed"] = order[(order.index(settings["speed"]) + 1) % len(order)]
    elif key in ("long", "sukun", "shadda", "hamza"):
        settings[key] = not settings[key]
    await query.answer("Réglage enregistré ✅")
    await safe_edit_text(query, SETTINGS_TEXT, reply_markup=settings_keyboard(settings))


async def on_voice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """V:i → écouter un échantillon ; K:i → garder cette voix."""
    query = update.callback_query
    action, raw = query.data.split(":")
    index = int(raw)
    if not 0 <= index < len(VOICES):
        await query.answer()
        return
    voice, label = VOICES[index]
    settings = settings_of(context)

    if action == "K":
        settings["voice"] = voice
        await query.answer("Voix enregistrée ✅")
        try:
            await query.edit_message_reply_markup(reply_markup=None)
        except BadRequest:
            pass
        await context.bot.send_message(
            query.message.chat_id, f"✅ Voix choisie : <b>{html.escape(label)}</b>", parse_mode=ParseMode.HTML
        )
        return

    await query.answer("Écoute l'exemple 🎧")
    keep_kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Garder cette voix", callback_data=f"K:{index}")]])
    try:
        await send_voice_note(
            context, query.message.chat_id, VOICE_SAMPLE, voice, SPEEDS[settings["speed"]][1],
            f"🎙️ <b>{html.escape(label)}</b>\n{VOICE_SAMPLE}", keep_kb,
        )
    except Exception:
        logger.exception("Échantillon impossible pour %s", voice)
        await context.bot.send_message(query.message.chat_id, "❌ Cette voix est indisponible pour le moment.")


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
        f"Lettres : {' '.join(ordered(letters))}\n"
        f"{settings_summary(settings_of(context))}\n"
        "<i>(modifiable avec /reglages)</i>\n\n"
        "Combien de mots veux-tu ?",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([buttons]),
    )


async def on_choose_count(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    count = int(query.data.split(":", 1)[1])
    buttons = [
        InlineKeyboardButton(label, callback_data=f"G:{count}:{key}")
        for key, (label, _) in WORD_LENGTHS.items()
    ]
    await safe_edit_text(
        query, f"📝 <b>{count} mots</b>\nQuelle longueur de mots ?",
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

    settings = settings_of(context)
    recent: list[str] = context.user_data.setdefault("recent_real", [])
    words = build_session_words(letters, settings, count, length_key, recent)
    for w in words:
        if w["fr"]:
            recent.append(w["ar"])
    del recent[:-RECENT_REAL_MAX]

    context.user_data["session"] = {"id": secrets.token_hex(4), "words": words, "index": 0}
    n_real = sum(1 for w in words if w["fr"])
    await safe_edit_text(
        query,
        f"🎧 <b>C'est parti : {count} mots {WORD_LENGTHS[length_key][0].lower()}</b>\n"
        f"📖 {n_real} vrai(s) mot(s), 🧪 {count - n_real} inventé(s)\n"
        "Écoute, écris le mot sur ta feuille, puis vérifie.",
    )
    await send_current_word(query.message.chat_id, context)


async def send_current_word(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    session = context.user_data["session"]
    index = session["index"]
    total = len(session["words"])
    word = session["words"][index]
    settings = settings_of(context)
    try:
        await send_voice_note(
            context, chat_id, word["ar"], settings["voice"], SPEEDS[settings["speed"]][1],
            f"🎧 <b>Mot {index + 1}/{total}</b> — écoute et écris-le sur ta feuille.",
            word_keyboard(session, index, revealed=False),
        )
    except Exception:
        logger.exception("Échec de l'envoi audio pour %s", word["ar"])
        skip_kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("➡️ Mot suivant", callback_data=f"N:{session['id']}:{index}")
        ]])
        await context.bot.send_message(
            chat_id, f"❌ Impossible de générer l'audio du mot {index + 1}/{total} pour le moment.",
            reply_markup=skip_kb,
        )


def _active_session(context: ContextTypes.DEFAULT_TYPE, data: str) -> tuple[dict, int] | None:
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
    caption = (
        f"🎧 <b>Mot {index + 1}/{len(session['words'])}</b>\n\n"
        f"✍️ <b>{html.escape(word['ar'])}</b>\n"
        f"🔤 {html.escape(spelled_letters(word['ar']))}\n"
        f"{meaning_line(word)}"
    )
    try:
        await query.edit_message_caption(
            caption=caption, parse_mode=ParseMode.HTML,
            reply_markup=word_keyboard(session, index, revealed=True),
        )
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


async def on_slow(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    found = _active_session(context, query.data)
    if not found:
        await query.answer("Cette dictée est terminée. Relance /dictee.")
        return
    session, index = found
    await query.answer("Version lente 🐢")
    settings = settings_of(context)
    try:
        await send_voice_note(
            context, query.message.chat_id, session["words"][index]["ar"], settings["voice"],
            SLOW_REPLAY_RATE, f"🐢 Mot {index + 1}, au ralenti",
        )
    except Exception:
        logger.exception("Échec de la version lente")
        await context.bot.send_message(query.message.chat_id, "❌ Version lente indisponible pour le moment.")


async def on_next(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    found = _active_session(context, query.data)
    if not found or found[0]["index"] != found[1]:
        await query.answer("C'est déjà fait ✔️")
        return
    session, _ = found
    await query.answer()
    try:
        await query.edit_message_reply_markup(reply_markup=None)
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
        f"{i}. <b>{html.escape(w['ar'])}</b> — "
        + (html.escape(w["fr"]) if w["fr"] else "🧪 inventé")
        for i, w in enumerate(session["words"], start=1)
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
    await app.bot.set_my_commands([
        BotCommand("dictee", "Lancer une dictée"),
        BotCommand("lettres", "Choisir les lettres apprises"),
        BotCommand("reglages", "Voyelles longues, soukoun, chadda, vitesse"),
        BotCommand("voix", "Choisir la voix"),
        BotCommand("stop", "Arrêter la dictée en cours"),
        BotCommand("aide", "Comment ça marche"),
    ])


def build_application(token: str, builder=None) -> Application:
    """Assemble le bot (séparé de main() pour pouvoir le tester)."""
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    AUDIO_TMP_DIR.mkdir(exist_ok=True)
    clean_temp_audio()
    REAL_WORDS[:] = load_word_bank(WORDS_FILE)

    builder = builder or Application.builder()
    app = (
        builder.token(token)
        .persistence(PicklePersistence(filepath=PERSISTENCE_FILE))
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler(["start", "aide"], cmd_start))
    app.add_handler(CommandHandler("lettres", cmd_letters))
    app.add_handler(CommandHandler("reglages", cmd_settings))
    app.add_handler(CommandHandler("voix", cmd_voices))
    app.add_handler(CommandHandler("dictee", cmd_dictation))
    app.add_handler(CommandHandler("stop", cmd_stop))

    app.add_handler(CallbackQueryHandler(on_letters, pattern=r"^L:"))
    app.add_handler(CallbackQueryHandler(on_setting, pattern=r"^O:\w+$"))
    app.add_handler(CallbackQueryHandler(on_voice, pattern=r"^[VK]:\d+$"))
    app.add_handler(CallbackQueryHandler(on_choose_count, pattern=r"^C:\d+$"))
    app.add_handler(CallbackQueryHandler(on_start_session, pattern=r"^G:\d+:\w+$"))
    app.add_handler(CallbackQueryHandler(on_reveal, pattern=r"^R:"))
    app.add_handler(CallbackQueryHandler(on_slow, pattern=r"^S:"))
    app.add_handler(CallbackQueryHandler(on_next, pattern=r"^N:"))
    app.add_handler(CallbackQueryHandler(on_new_dictation, pattern=r"^D:NEW$"))

    app.add_error_handler(on_error)
    return app


def main() -> None:
    if not TOKEN or TOKEN.startswith("COLLE_"):
        raise SystemExit(
            "TELEGRAM_BOT_TOKEN manquant : ajoute-le (variable Railway, ou config.txt sur ton PC)."
        )
    app = build_application(TOKEN)
    logger.info("Bot démarré — laisse cette fenêtre ouverte. Ctrl+C pour arrêter.")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
