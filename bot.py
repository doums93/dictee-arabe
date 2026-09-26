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
import io
import json
import logging
import os
import random
import re
import secrets
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

# Pause entre les mots d'une phrase (clé : libellé, secondes).
PAUSES = {"0.5": ("0,5 s", 0.5), "1": ("1 s", 1.0), "2": ("2 s", 2.0), "3": ("3 s", 3.0)}

# Réglages par défaut d'un nouvel élève.
DEFAULT_SETTINGS = {
    "long": True,      # voyelles longues (ا و ي)
    "sukun": False,    # soukoun ( ْ )
    "shadda": False,   # chadda ( ّ )
    "hamza": False,    # hamza sur alif (أ إ)
    "speed": "lente",
    "pause": "1",      # pause entre les mots d'une phrase
    "voice": DEFAULT_VOICE,
}

SESSION_SIZES = {"w": (3, 5, 10), "p": (1, 3, 5)}   # mots / phrases par dictée
# Taille des phrases (clé : libellé, nombre de mots).
PHRASE_LENGTHS = {"court": ("3 mots", 3), "moyen": ("5 mots", 5), "long": ("7 mots", 7)}
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
# Synthèse vocale (tout en mémoire, aucun fichier écrit)
# ---------------------------------------------------------------------------
#
# Voyelle finale : seul, un mot est lu « à la pause » et la voix avale sa dernière
# voyelle (كَتَبَ → katab). Pour l'apprentissage on veut « kataba ». Astuce : on fait lire
# le mot suivi d'un mot témoin (il n'est alors plus en fin de phrase), puis on coupe
# l'audio juste après le mot grâce aux repères de temps envoyés par edge-tts.
# Chaque audio se termine ensuite par END_SILENCE secondes de silence.

CARRIER_WORD = "كَمْ"       # mot témoin, coupé de l'audio final
CARRIER_MARGIN = 0.1        # secondes gardées après la fin du mot (laisse la voyelle finir)
END_SILENCE = 1.0           # secondes de silence ajoutées à la fin de chaque audio
TICKS_PER_SECOND = 10_000_000


def ends_with_short_vowel(word: str) -> bool:
    """La dernière lettre porte-t-elle une voyelle courte (ثُمَّ, كَتَبَ, نَحْنُ) ?"""
    trailing = set()
    for ch in reversed(word):
        if ch not in MARKS:
            break
        trailing.add(ch)
    return bool(trailing & set(SHORT_VOWELS))


# --- Lecture des trames MP3 (couche III), pour couper et ajouter du silence -------------

_MP3_BITRATES = {
    1: [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320],   # MPEG-1
    2: [0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160],       # MPEG-2 / 2.5
}
_MP3_RATES = {3: [44100, 48000, 32000], 2: [22050, 24000, 16000], 0: [11025, 12000, 8000]}


def _frame_info(header: bytes) -> tuple[int, float, tuple] | None:
    """(longueur en octets, durée en secondes, format) d'une trame, ou None."""
    if len(header) < 4 or header[0] != 0xFF or (header[1] & 0xE0) != 0xE0:
        return None
    version, layer = (header[1] >> 3) & 3, (header[1] >> 1) & 3
    bitrate_idx, rate_idx, padding = (header[2] >> 4) & 0xF, (header[2] >> 2) & 3, (header[2] >> 1) & 1
    if version == 1 or layer != 1 or bitrate_idx in (0, 15) or rate_idx == 3:
        return None
    mpeg1 = version == 3
    bitrate = _MP3_BITRATES[1 if mpeg1 else 2][bitrate_idx] * 1000
    rate = _MP3_RATES[version][rate_idx]
    length = (144 if mpeg1 else 72) * bitrate // rate + padding
    if length <= 4:
        return None
    fmt = (version, rate_idx, header[3] >> 6)  # version, fréquence, mono/stéréo
    return length, (1152 if mpeg1 else 576) / rate, fmt


def _audio_start(data: bytes) -> int:
    if data[:3] == b"ID3" and len(data) >= 10:  # en-tête ID3v2 éventuel
        return 10 + ((data[6] << 21) | (data[7] << 14) | (data[8] << 7) | data[9])
    return 0


def mp3_format(data: bytes) -> tuple | None:
    info = _frame_info(data[_audio_start(data):][:4])
    return info[2] if info else None


def trim_mp3(data: bytes, seconds: float) -> bytes | None:
    """Garde les trames qui commencent avant `seconds`. None si illisible."""
    start = pos = _audio_start(data)
    elapsed, frames = 0.0, 0
    while pos + 4 <= len(data) and elapsed < seconds:
        info = _frame_info(data[pos:pos + 4])
        if not info:
            break
        pos += info[0]
        elapsed += info[1]
        frames += 1
    return data[start:min(pos, len(data))] if frames else None


def mp3_silence(like: bytes, seconds: float) -> bytes:
    """Trames muettes au même format que `like` (en-tête copié, contenu à zéro = silence)."""
    start = _audio_start(like)
    header = bytearray(like[start:start + 4])
    if not _frame_info(bytes(header)):
        return b""
    header[1] |= 0x01    # pas de somme de contrôle CRC
    header[2] &= ~0x02   # pas d'octet de bourrage
    length, duration, _ = _frame_info(bytes(header))
    frame = bytes(header) + bytes(length - 4)
    return frame * max(1, round(seconds / duration))


async def _edge_audio(text: str, voice: str, rate: str, word_boundary: bool = False):
    """Renvoie (octets MP3, fin du premier mot en secondes ou None)."""
    communicate = edge_tts.Communicate(
        text, voice, rate=rate, boundary="WordBoundary" if word_boundary else "SentenceBoundary"
    )
    audio = bytearray()
    first_word_end = None
    async for chunk in communicate.stream():
        if chunk["type"] == "audio":
            audio += chunk["data"]
        elif chunk["type"] == "WordBoundary" and first_word_end is None:
            first_word_end = (chunk["offset"] + chunk["duration"]) / TICKS_PER_SECOND
    if not audio:
        raise RuntimeError("audio vide")
    return bytes(audio), first_word_end


def _gtts_audio(text: str) -> bytes:
    buffer = io.BytesIO()
    gTTS(text=text, lang="ar", slow=True).write_to_fp(buffer)
    return buffer.getvalue()


async def speak(text: str, voice: str, rate: str) -> bytes:
    """MP3 d'un mot ou d'un texte, voyelle finale prononcée si besoin (sans silence final)."""
    if ends_with_short_vowel(text):
        try:
            audio, word_end = await _edge_audio(f"{text} {CARRIER_WORD}", voice, rate, word_boundary=True)
            trimmed = trim_mp3(audio, word_end + CARRIER_MARGIN) if word_end else None
            if trimmed:
                return trimmed
            raise RuntimeError("repères de mots absents")
        except Exception as exc:
            logger.warning("Voyelle finale non forcée pour %s (%s)", text, exc)
    for candidate in dict.fromkeys((voice, DEFAULT_VOICE)):
        try:
            return (await _edge_audio(text, candidate, rate))[0]
        except Exception as exc:
            logger.warning("edge-tts en échec avec %s (%s)", candidate, exc)
    return await asyncio.to_thread(_gtts_audio, text)


async def render_audio(words: list[str], voice: str, rate: str, pause: float) -> bytes:
    """Audio final : un mot, ou une phrase mot par mot avec `pause` secondes entre les mots,
    puis END_SILENCE secondes de silence."""
    segments = await asyncio.gather(*(speak(w, voice, rate) for w in words))
    formats = {mp3_format(s) for s in segments}
    if len(segments) > 1 and (len(formats) != 1 or None in formats):
        # Formats différents (voix de secours) : on lit la phrase d'un seul bloc.
        segments = [await speak(" ، ".join(words), voice, rate)]
    audio = segments[0]
    for segment in segments[1:]:
        audio += mp3_silence(audio, pause) + segment[_audio_start(segment):]
    return audio + mp3_silence(audio, END_SILENCE)


async def send_voice_note(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, words: list[str], voice: str, rate: str,
    pause: float, caption: str, reply_markup: InlineKeyboardMarkup | None = None,
) -> None:
    await context.bot.send_chat_action(chat_id, ChatAction.RECORD_VOICE)
    audio = await render_audio(words, voice, rate, pause)
    await context.bot.send_voice(
        chat_id, voice=audio, filename="dictee.mp3", caption=caption,
        parse_mode=ParseMode.HTML, reply_markup=reply_markup,
    )


def clean_temp_audio() -> None:
    """Supprime d'anciens fichiers audio temporaires (versions précédentes du bot)."""
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
    if settings["pause"] not in PAUSES:
        settings["pause"] = DEFAULT_SETTINGS["pause"]
    return settings


def audio_params(settings: dict, slow: bool = False) -> tuple[str, str, float]:
    """(voix, débit, pause entre les mots) selon les réglages de l'élève."""
    rate = SLOW_REPLAY_RATE if slow else SPEEDS[settings["speed"]][1]
    pause = PAUSES[settings["pause"]][1] * (1.5 if slow else 1)
    return settings["voice"], rate, pause


def voice_label(voice: str) -> str:
    return next((label for v, label in VOICES if v == voice), voice)


def settings_summary(settings: dict) -> str:
    def mark(key: str) -> str:
        return "✅" if settings[key] else "❌"
    return (
        f"{mark('long')} voyelles longues   {mark('sukun')} soukoun   "
        f"{mark('shadda')} chadda   {mark('hamza')} hamza\n"
        f"🔊 {voice_label(settings['voice']).split(' —')[0]}, vitesse "
        f"{SPEEDS[settings['speed']][0].lower()}, pause entre les mots "
        f"{PAUSES[settings['pause']][0]}"
    )


def settings_keyboard(settings: dict) -> InlineKeyboardMarkup:
    def toggle(key: str, label: str) -> InlineKeyboardButton:
        return InlineKeyboardButton(f"{'✅' if settings[key] else '❌'} {label}", callback_data=f"O:{key}")
    return InlineKeyboardMarkup([
        [toggle("long", "Voyelles longues (ا و ي)")],
        [toggle("sukun", "Soukoun ( ـْ )"), toggle("shadda", "Chadda ( ـّ )")],
        [toggle("hamza", "Hamza (أ إ)")],
        [InlineKeyboardButton(f"🐢 Vitesse : {SPEEDS[settings['speed']][0]}", callback_data="O:speed")],
        [InlineKeyboardButton(f"⏸️ Pause entre les mots (phrases) : {PAUSES[settings['pause']][0]}",
                              callback_data="O:pause")],
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
    is_last = index == len(session["items"]) - 1
    unit = "Phrase" if session["mode"] == "p" else "Mot"
    first = (
        InlineKeyboardButton("🏁 Voir le bilan" if is_last else f"➡️ {unit} suivant{'e' if unit == 'Phrase' else ''}",
                             callback_data=f"N:{sid}:{index}")
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


def item_text(item: list[dict]) -> str:
    return " ".join(w["ar"] for w in item)


def item_label(session: dict, index: int) -> str:
    unit = "Phrase" if session["mode"] == "p" else "Mot"
    return f"{unit} {index + 1}/{len(session['items'])}"


def reveal_caption(session: dict, index: int) -> str:
    item = session["items"][index]
    if len(item) == 1:
        word = item[0]
        details = f"🔤 {html.escape(spelled_letters(word['ar']))}\n{meaning_line(word)}"
    else:
        details = "\n".join(
            f"• {html.escape(w['ar'])} — " + (html.escape(w["fr"]) if w["fr"] else "🧪 <i>inventé</i>")
            for w in item
        )
    return f"🎧 <b>{item_label(session, index)}</b>\n\n✍️ <b>{html.escape(item_text(item))}</b>\n{details}"


# ---------------------------------------------------------------------------
# Commandes
# ---------------------------------------------------------------------------

HELP_TEXT = (
    "السَّلَامُ عَلَيْكُم 👋\n\n"
    "Je t'aide à t'entraîner à la <b>dictée en arabe</b>.\n\n"
    "1️⃣ /lettres : coche les lettres que tu as déjà apprises\n"
    "2️⃣ /reglages : voyelles longues, soukoun, chadda, hamza, vitesse, pauses\n"
    "3️⃣ /dictee : dictée de mots ou de phrases, avec uniquement ce que tu as vu\n"
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
    if key in ("speed", "pause"):
        options = list(SPEEDS if key == "speed" else PAUSES)
        settings[key] = options[(options.index(settings[key]) + 1) % len(options)]
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
            context, query.message.chat_id, [VOICE_SAMPLE], voice, SPEEDS[settings["speed"]][1], 0,
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
    await context.bot.send_message(
        chat_id,
        f"📝 <b>Nouvelle dictée</b>\n"
        f"Lettres : {' '.join(ordered(letters))}\n"
        f"{settings_summary(settings_of(context))}\n"
        "<i>(modifiable avec /reglages)</i>\n\n"
        "Que veux-tu travailler ?",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔤 Des mots", callback_data="M:w"),
            InlineKeyboardButton("🗣️ Des phrases", callback_data="M:p"),
        ]]),
    )


async def on_choose_mode(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    mode = query.data.split(":", 1)[1]
    unit = "phrases" if mode == "p" else "mots"
    buttons = [InlineKeyboardButton(f"{n} {unit if n > 1 else unit[:-1]}", callback_data=f"C:{mode}:{n}")
               for n in SESSION_SIZES[mode]]
    await safe_edit_text(query, f"📝 <b>Dictée de {unit}</b>\nCombien ?",
                         reply_markup=InlineKeyboardMarkup([buttons]))


async def on_choose_count(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    _, mode, raw_count = query.data.split(":")
    count = int(raw_count)
    if mode == "p":
        options = {key: label for key, (label, _) in PHRASE_LENGTHS.items()}
        question = "Combien de mots par phrase ?"
    else:
        options = {key: label for key, (label, _) in WORD_LENGTHS.items()}
        question = "Quelle longueur de mots ?"
    buttons = [InlineKeyboardButton(label, callback_data=f"G:{mode}:{count}:{key}") for key, label in options.items()]
    await safe_edit_text(query, f"📝 <b>{count} × {'phrase' if mode == 'p' else 'mot'}</b>\n{question}",
                         reply_markup=InlineKeyboardMarkup([buttons]))


async def on_start_session(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    _, mode, raw_count, length_key = query.data.split(":")
    count = int(raw_count)

    letters: set[str] = context.user_data.get("letters", set())
    problem = letters_problem(letters)
    lengths = PHRASE_LENGTHS if mode == "p" else WORD_LENGTHS
    if problem or length_key not in lengths:
        await safe_edit_text(query, problem or "⚠️ Relance /dictee.")
        return

    settings = settings_of(context)
    recent: list[str] = context.user_data.setdefault("recent_real", [])
    if mode == "p":
        size = PHRASE_LENGTHS[length_key][1]
        items = [
            build_session_words(letters, settings, size, random.choice(["court", "moyen"]), recent)
            for _ in range(count)
        ]
        intro = f"🗣️ <b>C'est parti : {count} phrase(s) de {size} mots</b>\n" \
                f"⏸️ {PAUSES[settings['pause']][0]} de pause entre les mots (modifiable dans /reglages)\n"
    else:
        items = [[w] for w in build_session_words(letters, settings, count, length_key, recent)]
        intro = f"🎧 <b>C'est parti : {count} mots {WORD_LENGTHS[length_key][0].lower()}</b>\n"
    all_words = [w for item in items for w in item]
    recent.extend(w["ar"] for w in all_words if w["fr"])
    del recent[:-RECENT_REAL_MAX]

    context.user_data["session"] = {"id": secrets.token_hex(4), "mode": mode, "items": items, "index": 0}
    n_real = sum(1 for w in all_words if w["fr"])
    await safe_edit_text(
        query,
        intro + f"📖 {n_real} vrai(s) mot(s), 🧪 {len(all_words) - n_real} inventé(s)\n"
        "Écoute, écris sur ta feuille, puis vérifie.",
    )
    await send_current_item(query.message.chat_id, context)


async def send_current_item(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    session = context.user_data["session"]
    index = session["index"]
    item = session["items"][index]
    voice, rate, pause = audio_params(settings_of(context))
    try:
        await send_voice_note(
            context, chat_id, [w["ar"] for w in item], voice, rate, pause,
            f"🎧 <b>{item_label(session, index)}</b> — écoute et écris sur ta feuille.",
            word_keyboard(session, index, revealed=False),
        )
    except Exception:
        logger.exception("Échec de l'envoi audio pour %s", item_text(item))
        skip_kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("➡️ Suivant", callback_data=f"N:{session['id']}:{index}")
        ]])
        await context.bot.send_message(
            chat_id, f"❌ Impossible de générer l'audio ({item_label(session, index)}) pour le moment.",
            reply_markup=skip_kb,
        )


def _active_session(context: ContextTypes.DEFAULT_TYPE, data: str) -> tuple[dict, int] | None:
    _, session_id, raw_index = data.split(":")
    session = context.user_data.get("session")
    index = int(raw_index)
    if not session or session.get("id") != session_id or index >= len(session.get("items", [])):
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
    try:
        await query.edit_message_caption(
            caption=reveal_caption(session, index), parse_mode=ParseMode.HTML,
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
    voice, rate, pause = audio_params(settings_of(context), slow=True)
    try:
        await send_voice_note(
            context, query.message.chat_id, [w["ar"] for w in session["items"][index]], voice, rate, pause,
            f"🐢 {item_label(session, index)}, au ralenti",
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
    if session["index"] >= len(session["items"]):
        await send_summary(chat_id, context)
    else:
        await send_current_item(chat_id, context)


async def send_summary(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    session = context.user_data.pop("session")
    lines = []
    for i, item in enumerate(session["items"], start=1):
        if len(item) == 1:
            w = item[0]
            lines.append(f"{i}. <b>{html.escape(w['ar'])}</b> — "
                         + (html.escape(w["fr"]) if w["fr"] else "🧪 inventé"))
        else:
            lines.append(f"{i}. <b>{html.escape(item_text(item))}</b>")
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Nouvelle dictée", callback_data="D:NEW")]])
    await context.bot.send_message(
        chat_id,
        f"🏁 <b>Bilan de la dictée</b>\n\n" + "\n".join(lines)
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
    app.add_handler(CallbackQueryHandler(on_choose_mode, pattern=r"^M:[wp]$"))
    app.add_handler(CallbackQueryHandler(on_choose_count, pattern=r"^C:[wp]:\d+$"))
    app.add_handler(CallbackQueryHandler(on_start_session, pattern=r"^G:[wp]:\d+:\w+$"))
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
