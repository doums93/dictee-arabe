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
import shutil
from dataclasses import dataclass
from pathlib import Path

import edge_tts

try:
    import numpy as np
except ImportError:  # sans numpy : pas de prolongement, audio simple
    np = None
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

# Mode de dictée : « normal » appuie sur les voyelles longues pour qu'elles s'entendent bien,
# « difficile » garde la prononciation naturelle.
MODES = {
    "normal": "🟢 Normal : prolongements appuyés",
    "difficile": "🔴 Difficile : voix naturelle",
}

# Pause entre les mots d'une phrase (clé : libellé, secondes).
PAUSES = {"0.5": ("0,5 s", 0.5), "1": ("1 s", 1.0), "2": ("2 s", 2.0), "3": ("3 s", 3.0)}

# Réglages par défaut d'un nouvel élève.
DEFAULT_SETTINGS = {
    "long": True,      # voyelles longues (ا و ي)
    "sukun": False,    # soukoun ( ْ )
    "shadda": False,   # chadda ( ّ )
    "hamza": False,    # hamza sur alif (أ إ)
    "mode": "normal",  # normal = prolongements appuyés, difficile = voix naturelle
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

# Longueur des mots : (libellé, nombre de LETTRES min-max, syllabes tentées par le générateur).
WORD_LENGTHS = {
    "court": ("3 lettres", (3, 3), (1, 3)),
    "moyen": ("4 lettres", (4, 4), (2, 4)),
    "long": ("5 lettres et +", (5, 7), (3, 5)),
}


def letter_count(word: str) -> int:
    """Nombre de lettres écrites (les voyelles courtes, soukoun et chadda ne comptent pas)."""
    return sum(1 for ch in word if ch not in MARKS)

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
        if is_allowed(w, letters, settings) and lo <= letter_count(w.arabic) <= hi
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
    """Mot inventé ayant le nombre de lettres demandé (on réessaie jusqu'à tomber juste)."""
    _, (lo, hi), (syl_lo, syl_hi) = WORD_LENGTHS[length_key]
    word = ""
    for _ in range(300):
        word = generate_word(letters, random.randint(syl_lo, syl_hi), settings)
        if lo <= letter_count(word) <= hi:
            break
    return analyze_word(word)


def build_session_words(
    letters: set[str], settings: dict, count: int, length_key: str, recent: list[str],
    taken: set[str] | None = None,
) -> list[dict]:
    """Mélange de vrais mots (priorité aux moins récents) et de mots inventés.

    `taken` = mots déjà utilisés dans la dictée en cours : ils ne reviennent pas
    (utile pour que chaque phrase ait des mots différents). Il est mis à jour.
    """
    taken = taken if taken is not None else set()
    pool = [w for w in eligible_real_words(letters, settings, length_key) if w.arabic not in taken]
    random.shuffle(pool)
    pool.sort(key=lambda w: w.arabic in recent)  # les mots non vus récemment d'abord
    n_real = min(len(pool), round(count * REAL_WORD_RATIO))
    chosen = pool[:n_real]
    taken.update(w.arabic for w in chosen)

    # Longueur demandée d'abord ; en tout dernier recours (plus aucun mot nouveau possible
    # avec si peu de lettres), une longueur plus grande plutôt qu'un doublon.
    order = list(WORD_LENGTHS)
    fallback_lengths = [length_key] + order[order.index(length_key) + 1:]
    while len(chosen) < count:
        word = None
        for key in fallback_lengths:
            for _ in range(200):
                candidate = invented_word(letters, key, settings)
                if candidate.arabic not in taken:
                    word = candidate
                    break
            if word:
                break
        word = word or candidate   # vraiment plus aucun mot nouveau possible : on accepte un doublon
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
CARRIER_MARGIN = 0.1        # (version de secours sans ffmpeg) secondes gardées après le mot
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
    """Renvoie (octets MP3, liste des mots [(début, fin)] en secondes)."""
    communicate = edge_tts.Communicate(
        text, voice, rate=rate, boundary="WordBoundary" if word_boundary else "SentenceBoundary"
    )
    audio = bytearray()
    words: list[tuple[float, float]] = []
    async for chunk in communicate.stream():
        if chunk["type"] == "audio":
            audio += chunk["data"]
        elif chunk["type"] == "WordBoundary":
            start = chunk["offset"] / TICKS_PER_SECOND
            words.append((start, start + chunk["duration"] / TICKS_PER_SECOND))
    if not audio:
        raise RuntimeError("audio vide")
    return bytes(audio), words


def _gtts_audio(text: str) -> bytes:
    buffer = io.BytesIO()
    gTTS(text=text, lang="ar", slow=True).write_to_fp(buffer)
    return buffer.getvalue()


async def speak(text: str, voice: str, rate: str) -> bytes:
    """Version de secours (sans ffmpeg) : MP3 d'un mot, voyelle finale prononcée si besoin."""
    if ends_with_short_vowel(text):
        try:
            audio, bounds = await _edge_audio(f"{text} {CARRIER_WORD}", voice, rate, word_boundary=True)
            trimmed = trim_mp3(audio, bounds[0][1] + CARRIER_MARGIN) if bounds else None
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


# ---------------------------------------------------------------------------
# Traitement du son (ffmpeg + numpy) : coupe précise, prolongements, silences
# ---------------------------------------------------------------------------
#
# Mode normal : on ÉTIRE le son des voyelles longues directement dans l'audio (TD-PSOLA).
# Une voyelle est une vibration régulière : on repère chaque vibration de la voyelle longue
# puis on la rejoue en l'étalant progressivement, avec un fondu entre chaque vibration.
# La voyelle dure plus longtemps en gardant ses variations naturelles ; le reste du mot
# n'est pas modifié.

SAMPLE_RATE = 24000
# Mode normal : chaque voyelle longue est amenée à MADD_TARGET secondes (au moins +MADD_MIN_ADD).
# Durée visée identique pour ا و ي, quelle que soit la façon dont la voix l'a prononcée.
MADD_TARGET = 0.45
MADD_MIN_ADD = 0.12
FADE = 0.03            # durée (s) de l'extinction en fin de mot coupé (dans le silence du « k »)
DECODER_DELAY = 0.045  # retard (s) ajouté par le décodage MP3 par rapport aux repères de la voix


def _find_ffmpeg() -> str | None:
    exe = shutil.which("ffmpeg")
    if exe:
        return exe
    try:
        import imageio_ffmpeg  # ffmpeg fourni par pip (requirements.txt)
        return imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        return None


FFMPEG = _find_ffmpeg()


async def _ffmpeg(args: list[str], data: bytes) -> bytes:
    proc = await asyncio.create_subprocess_exec(
        FFMPEG, "-hide_banner", "-v", "error", *args,
        stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
    )
    out, err = await proc.communicate(data)
    if proc.returncode != 0 or not out:
        raise RuntimeError(f"ffmpeg : {err.decode(errors='ignore')[-200:]}")
    return out


async def decode_pcm(mp3: bytes) -> "np.ndarray":
    raw = await _ffmpeg(["-i", "pipe:0", "-f", "s16le", "-ac", "1", "-ar", str(SAMPLE_RATE), "pipe:1"], mp3)
    return np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0


async def encode_pcm(pcm: "np.ndarray") -> tuple[bytes, str]:
    """PCM → (octets, nom de fichier). MP3 d'abord, sinon OGG/Opus."""
    raw = (np.clip(pcm, -1.0, 1.0) * 32767).astype(np.int16).tobytes()
    source = ["-f", "s16le", "-ar", str(SAMPLE_RATE), "-ac", "1", "-i", "pipe:0"]
    for codec, fmt, name in (("libmp3lame", "mp3", "dictee.mp3"), ("libopus", "ogg", "dictee.ogg")):
        try:
            return await _ffmpeg(source + ["-c:a", codec, "-b:a", "64k", "-f", fmt, "pipe:1"], raw), name
        except Exception as exc:
            logger.warning("Encodage %s impossible (%s)", codec, exc)
    raise RuntimeError("aucun encodeur audio disponible")


def phonetic_units(word: str) -> list[tuple[str, float]]:
    """Découpe un mot en sons avec une durée relative : consonne « C », voyelle courte « V »,
    voyelle longue « L » (sert à estimer où tombe chaque voyelle longue dans l'audio)."""
    units: list[tuple[str, float]] = []
    prev_vowel = None
    for i, ch in enumerate(word):
        if ch in SHORT_VOWELS:
            units.append(("V", 0.9))
            prev_vowel = ch
        elif ch == SHADDA:
            units.append(("C", 1.0))           # consonne doublée
        elif ch in MARKS:
            prev_vowel = None
        else:
            has_mark = i + 1 < len(word) and word[i + 1] in MARKS
            if not has_mark and LONG_VOWEL_LETTER.get(prev_vowel) == ch:
                units.append(("L" + ch, 2.2))    # « Lا », « Lو » ou « Lي »
            else:
                units.append(("C", 1.0))
            prev_vowel = None
    return units


def _periodicity(frame: "np.ndarray") -> tuple[float, int]:
    """(régularité 0→1, période en échantillons) d'un extrait : corrélation NORMALISÉE entre
    l'extrait et lui-même décalé d'une période (≈ 1 pour une voyelle tenue)."""
    x = frame - frame.mean()
    n = len(x)
    if n < 64 or float(np.dot(x, x)) < 1e-6:
        return 0.0, 0
    lo, hi = SAMPLE_RATE // 400, min(SAMPLE_RATE // 70, n // 2)   # voix entre 70 et 400 Hz
    if hi <= lo:
        return 0.0, 0
    spectrum = np.fft.rfft(x, 2 * n)
    ac = np.fft.irfft(spectrum * np.conj(spectrum))[:n]
    energy = np.cumsum(x ** 2)
    lags = np.arange(lo, hi)
    head = energy[n - lags - 1]                           # énergie de x[0 : n-lag]
    tail = energy[-1] - energy[lags - 1]                  # énergie de x[lag : n]
    r = ac[lo:hi] / np.sqrt(head * tail + 1e-12)
    k = int(np.argmax(r))
    return float(r[k]), int(lags[k])


def _local_strength(x: "np.ndarray", pos: int, win: int) -> tuple[float, int, float]:
    frame = x[max(0, pos - win // 2): pos + win // 2]
    if len(frame) < win // 2:
        return 0.0, 0, 0.0
    strength, period = _periodicity(frame)
    return strength, period, float(np.sqrt(np.mean(frame ** 2)))


def _pitch_marks(x: "np.ndarray", start: int, end: int, period: int) -> list[int]:
    """Un repère par vibration de la voix (période), suivi pas à pas entre start et end."""
    center = (start + end) // 2
    seg = x[center - period // 2: center + period // 2]
    first = center - period // 2 + int(np.argmax(seg))

    def follow(mark: int, direction: int) -> list[int]:
        marks, p = [], period
        while True:
            ref = x[mark - p // 2: mark + p // 2]
            best_lag, best_corr = None, 0.3
            for lag in range(int(0.8 * p), int(1.2 * p) + 1):
                nxt = mark + direction * lag
                cand = x[nxt - p // 2: nxt + p // 2]
                if len(cand) != len(ref) or len(ref) == 0:
                    break
                corr = float(np.dot(ref, cand) / (np.linalg.norm(ref) * np.linalg.norm(cand) + 1e-9))
                if corr > best_corr:
                    best_lag, best_corr = lag, corr
            if best_lag is None:
                return marks
            mark += direction * best_lag
            p = best_lag
            if not (start <= mark <= end):
                return marks
            marks.append(mark)

    return sorted(follow(first, -1) + [first] + follow(first, +1))


def _psola_stretch(x: "np.ndarray", marks: list[int], extra: int) -> "np.ndarray":
    """Allonge la zone entre le premier et le dernier repère de `extra` échantillons.
    L'allongement est progressif (nul aux bords, maximal au milieu de la voyelle) et chaque
    vibration est recollée avec un fondu (fenêtre de Hann) : c'est la méthode TD-PSOLA."""
    m = np.asarray(marks)
    periods = np.diff(m)
    p_at = np.concatenate([[periods[0]], (periods[:-1] + periods[1:]) // 2, [periods[-1]]])
    first, last = int(m[0]), int(m[-1])
    length = last - first
    # Correspondance temps de sortie → temps d'entrée : pente 1 aux bords, plus lente au milieu.
    # Profil en plateau : montée douce sur le 1er quart, allongement constant au milieu,
    # retour doux sur le dernier quart (l'allongement est réparti sur toute la voyelle).
    tau = np.arange(length + 1, dtype=np.float64)
    ramp = np.clip(np.minimum(tau, length - tau) / (0.25 * length), 0.0, 1.0)
    bump = 0.5 - 0.5 * np.cos(np.pi * ramp)
    slope = 1.0 + (extra / max(float(bump.sum()), 1.0)) * bump
    out_time = np.concatenate([[0.0], np.cumsum(slope[:-1])])
    total = int(round(out_time[-1]))

    new_len = len(x) + total - length
    y = np.zeros(new_len + 4 * int(p_at.max()), dtype=np.float64)
    wsum = np.zeros_like(y)

    # Partie avant la voyelle (fondu sortant sur une période, complété par le 1er grain).
    p0 = int(p_at[0])
    left = np.ones(first, dtype=np.float64)
    left[-p0:] = 0.5 + 0.5 * np.cos(np.pi * np.arange(1, p0 + 1) / p0)
    y[:first] += x[:first] * left
    wsum[:first] += left

    # Grains : un par vibration de sortie, pris sur la vibration d'entrée correspondante.
    t = 0.0
    while True:
        in_pos = first + float(np.interp(t, out_time, tau))
        j = int(np.argmin(np.abs(m - in_pos)))
        p = int(p_at[j])
        grain = x[m[j] - p: m[j] + p]
        if len(grain) == 2 * p:
            window = np.hanning(2 * p)
            at = first + int(round(t)) - p
            y[at: at + 2 * p] += grain * window
            wsum[at: at + 2 * p] += window
        if t >= total:
            break
        t = min(t + p, float(total))

    # Partie après la voyelle (fondu entrant sur une période).
    pn = int(p_at[-1])
    tail = x[last:]
    right = np.ones(len(tail), dtype=np.float64)
    right[:pn] = 0.5 - 0.5 * np.cos(np.pi * np.arange(pn) / pn)
    at = first + total
    y[at: at + len(tail)] += tail * right
    wsum[at: at + len(tail)] += right

    y = y[:new_len]
    wsum = wsum[:new_len]
    return (y / np.maximum(wsum, 1e-3)).astype(np.float32)


def ends_with_vowel(word: str) -> bool:
    """Le mot finit-il par une voyelle, courte (كَتَبَ) ou longue (هُنَا, فِي) ?
    Lu seul, la voix l'avalerait ou la raccourcirait (lecture « à la pause »)."""
    if ends_with_short_vowel(word):
        return True
    units = phonetic_units(word)
    return bool(units) and units[-1][0].startswith("L")


# --- Repérage exact des voyelles longues -------------------------------------------------
#
# La voix ne donne des repères de temps que par MOT. Astuce (validée sur la vraie voix) :
# on insère un séparateur invisible (espace de largeur nulle) autour de chaque syllabe à
# voyelle longue — « كِ|تَا|بْ ». La voix renvoie alors un repère par morceau, qui tombe
# exactement au début et à la fin de la syllabe. Cette version « sonde » se prononce de façon
# un peu hachée : on ne l'envoie jamais à l'élève. On aligne simplement ses repères sur
# l'audio normal (quasi identique) par alignement temporel dynamique (DTW).

ZWSP = "​"


def long_vowel_positions(word: str) -> list[int]:
    """Index des lettres de prolongation : ا après fatha, و après damma, ي après kasra,
    sans signe propre (les signes de la consonne peuvent être dans n'importe quel ordre)."""
    positions = []
    for j, ch in enumerate(word):
        if ch not in "اوي" or (j + 1 < len(word) and word[j + 1] in MARKS):
            continue
        k, vowel = j - 1, None
        while k >= 0 and word[k] in MARKS:
            if word[k] in SHORT_VOWELS:
                vowel = word[k]
            k -= 1
        if vowel and LONG_VOWEL_LETTER[vowel] == ch and k >= 0:
            positions.append(j)
    return positions


def probe_text(word: str) -> tuple[str, list[int]]:
    """Texte « sonde » + index des morceaux qui contiennent une voyelle longue."""
    positions = long_vowel_positions(word)
    cut_before, cut_after = set(), set()
    for j in positions:
        k = j - 1
        while k > 0 and word[k] in MARKS:
            k -= 1                                      # k = consonne qui porte la voyelle
        if k > 0:
            cut_before.add(k)
        if j < len(word) - 1:
            cut_after.add(j)
    out, piece_of_letter, piece = [], {}, 0
    for j, ch in enumerate(word):
        if j in cut_before and out and out[-1] != ZWSP:
            out.append(ZWSP)
            piece += 1
        out.append(ch)
        piece_of_letter[j] = piece
        if j in cut_after:
            out.append(ZWSP)
            piece += 1
    return "".join(out), [piece_of_letter[j] for j in positions]


def _features(x: "np.ndarray") -> "np.ndarray":
    """Empreinte spectrale toutes les 10 ms (forme du spectre, indépendante du volume)."""
    win, hop = 600, 240
    if len(x) < win:
        x = np.pad(x, (0, win - len(x)))
    frames = np.lib.stride_tricks.sliding_window_view(x, win)[::hop] * np.hanning(win)
    spec = np.abs(np.fft.rfft(frames, 1024)) ** 2
    bands = np.log(spec @ _MEL.T + 1e-8)
    bands -= bands.mean(1, keepdims=True)
    return bands / (np.linalg.norm(bands, axis=1, keepdims=True) + 1e-9)


def _mel_bank(n: int = 26, nfft: int = 1024) -> "np.ndarray":
    f = np.linspace(0, SAMPLE_RATE / 2, nfft // 2 + 1)
    to_mel = lambda h: 2595 * np.log10(1 + h / 700)
    pts = 700 * (10 ** (np.linspace(to_mel(60), to_mel(7000), n + 2) / 2595) - 1)
    bank = np.zeros((n, len(f)))
    for k in range(n):
        lo, c, hi = pts[k:k + 3]
        bank[k] = np.clip(np.minimum((f - lo) / (c - lo), (hi - f) / (hi - c)), 0, None)
    return bank


_MEL = _mel_bank() if np is not None else None


def dtw_map(src: "np.ndarray", dst: "np.ndarray") -> "np.ndarray":
    """Pour chaque trame de `src`, la trame correspondante de `dst` (alignement DTW)."""
    a, b = _features(src), _features(dst)
    cost = 1.0 - a @ b.T
    n, m = cost.shape
    acc = np.full((n + 1, m + 1), np.inf)
    acc[0, 0] = 0.0
    for i in range(1, n + 1):
        row, prev = acc[i], acc[i - 1]
        for j in range(1, m + 1):
            c = cost[i - 1, j - 1]
            row[j] = c + min(prev[j - 1], prev[j] + 0.5 * c, row[j - 1] + 0.5 * c)
    i, j, mapping = n, m, np.zeros(n)
    while i > 0 and j > 0:
        mapping[i - 1] = j - 1
        step = int(np.argmin((acc[i - 1, j - 1], acc[i - 1, j], acc[i, j - 1])))
        if step == 0:
            i, j = i - 1, j - 1
        elif step == 1:
            i -= 1
        else:
            j -= 1
    return mapping


SONORANTS = set("لمنرويه")   # consonnes « chantées » : pas de silence entre elles et la voyelle


def _frame_stats(x: "np.ndarray", a: int, b: int, win: int = 480, hop: int = 120):
    """Par trame de 20 ms entre a et b : (position, volume, part d'énergie sous 3 kHz)."""
    out = []
    freqs = np.fft.rfftfreq(1024, 1 / SAMPLE_RATE)
    low = freqs < 3000
    for pos in range(max(a, win // 2), min(b, len(x) - win // 2), hop):
        frame = x[pos - win // 2: pos + win // 2] * np.hanning(win)
        spec = np.abs(np.fft.rfft(frame, 1024)) ** 2
        total = float(spec.sum()) + 1e-12
        out.append((pos, float(np.sqrt(np.mean(frame ** 2))), float(spec[low].sum()) / total))
    return out


def _vowel_part(x: "np.ndarray", a: int, b: int, sonorant: bool = False) -> tuple[int, int] | None:
    """Dans la syllabe [a, b] (consonne + voyelle longue) : la voyelle = plus longue zone forte
    (≥ 30 % du volume max) dont l'énergie est grave (< 3 kHz) : silences, explosions et
    sifflantes sont exclus. Les 25 premières ms (fin possible de la voyelle précédente) ne
    comptent pas. Si la consonne est « chantée » (ل م ن…), la voyelle est la fin de la zone."""
    skip = int(0.025 * SAMPLE_RATE)
    rows = _frame_stats(x, a + skip, b)
    if not rows:
        return None
    top = max(r[1] for r in rows)
    good = [r[1] > 0.3 * top and r[2] > 0.85 for r in rows]
    best, cur = None, None
    for k, ok in enumerate(good):
        if ok:
            cur = (cur[0], k) if cur else (k, k)
            if not best or cur[1] - cur[0] > best[1] - best[0]:
                best = cur
        else:
            cur = None
    if not best or (best[1] - best[0]) * 120 < 0.04 * SAMPLE_RATE:
        return None
    start, end = rows[best[0]][0], rows[best[1]][0]
    if sonorant:
        start += int(0.3 * (end - start))
    return start, end


def wsola_stretch(x: "np.ndarray", intervals: list[tuple[int, int, float]]) -> "np.ndarray":
    """Allonge chaque voyelle [début, fin] de `secondes` par WSOLA (méthode de l'effet
    « atempo ») : on recopie le son par petits morceaux de 20 ms qui se chevauchent, en
    choisissant à chaque fois le morceau qui prolonge le mieux le précédent. Ailleurs, le son
    est restitué à l'identique. Fonctionne aussi sur une voix irrégulière (fin de mot)."""
    if not intervals:
        return x
    n_in = len(x)
    slope = np.ones(n_in)
    for a, b, seconds in intervals:
        a, b = max(0, a), min(n_in, b)
        length = b - a
        if length < 200:
            continue
        tau = np.arange(length, dtype=np.float64)
        ramp = np.clip(np.minimum(tau, length - tau) / (0.25 * length), 0.0, 1.0)
        bump = 0.5 - 0.5 * np.cos(np.pi * ramp)                  # montée douce, plateau, descente
        slope[a:b] += seconds * SAMPLE_RATE * bump / bump.sum()
    out_time = np.concatenate([[0.0], np.cumsum(slope)])        # temps de sortie de chaque échantillon
    n_out = int(out_time[-1])
    frame, hop, tol = 480, 240, 120
    window = 0.5 - 0.5 * np.cos(2 * np.pi * np.arange(frame) / frame)   # somme = 1 à 50 %
    padded = np.concatenate([np.zeros(frame + tol), x, np.zeros(4 * frame + 2 * tol)]).astype(np.float64)
    off = frame + tol
    y = np.zeros(n_out + 4 * frame)
    prev, prev_target = None, None
    for k in range(-hop, n_out + hop, hop):
        t_in = np.interp(k, out_time, np.arange(n_in + 1)) if k >= 0 else k   # avant 0 : identité
        target = int(round(t_in)) + off
        if prev is None or target - prev_target == hop:
            # hors voyelle (le temps avance normalement) : on recopie la suite exacte du son
            pos = target if prev is None else prev + hop
        else:
            ref = padded[prev + hop: prev + hop + frame]
            best, pos = -np.inf, target
            for cand in range(target - tol, target + tol + 1, 4):
                seg = padded[cand: cand + frame]
                score = float(np.dot(seg, ref)) / (np.linalg.norm(seg) * np.linalg.norm(ref) + 1e-9)
                if score > best:
                    best, pos = score, cand
        start = k + frame
        piece = padded[pos: pos + frame]
        if start >= 0 and len(piece) == frame:
            y[start: start + frame] += piece * window
        prev, prev_target = pos, target
    return y[frame: frame + n_out].astype(np.float32)


def stretch_at(pcm: "np.ndarray", intervals: list[tuple[int, int, float]]) -> "np.ndarray":
    return wsola_stretch(pcm, intervals)


def locate_long_vowels(final: "np.ndarray", probe: "np.ndarray", probe_marks: list,
                       word: str, end_limit: float) -> list:
    """Voyelles longues dans l'audio final, à partir des repères de la sonde."""
    _, pieces = probe_text(word)
    positions = long_vowel_positions(word)
    letters = [word[j] for j in positions]
    onsets = []
    for j in positions:
        k = j - 1
        while k > 0 and word[k] in MARKS:
            k -= 1
        onsets.append(word[k] in SONORANTS)
    starts = [m[0] + DECODER_DELAY for m in probe_marks]
    hop = 240
    probe = probe[: int(end_limit * SAMPLE_RATE)]
    mapping = dtw_map(probe, final)
    to_final = lambda pos: int(mapping[min(len(mapping) - 1, max(0, pos // hop))]) * hop
    found = []
    for piece, letter, sonorant in zip(pieces, letters, onsets):
        if piece >= len(starts):
            return []
        a = int(starts[piece] * SAMPLE_RATE)
        b = int(starts[piece + 1] * SAMPLE_RATE) if piece + 1 < len(starts) else len(probe)
        vowel = _vowel_part(probe, a, b, sonorant)
        if not vowel:
            continue
        # la syllabe dans l'audio final : on ne cherche la voyelle QU'À L'INTÉRIEUR
        syl_a, syl_b = to_final(a), to_final(b) + hop
        fa, fb = to_final(vowel[0]), to_final(vowel[1]) + hop
        lo, hi = max(syl_a, fa - 3 * hop // 2), min(syl_b, fb + 3 * hop // 2)
        refined = _vowel_part(final, lo, hi, sonorant) if hi - lo > 0.05 * SAMPLE_RATE else None
        mapped = (max(fa, syl_a), min(fb, syl_b))
        min_len = 0.04 * SAMPLE_RATE
        if not refined or refined[1] - refined[0] < 0.6 * (mapped[1] - mapped[0]):
            refined = mapped            # affinage douteux : on garde la zone donnée par l'alignement
        if refined[1] - refined[0] < min_len:
            # la voix a prononcé cette voyelle longue presque brève : on la cherche dans
            # toute la syllabe (c'est justement là que l'allongement est le plus utile)
            refined = _vowel_part(final, syl_a, syl_b, sonorant) or refined
        if refined[1] - refined[0] > min_len:
            current = (refined[1] - refined[0]) / SAMPLE_RATE
            found.append((refined[0], refined[1], max(MADD_MIN_ADD, MADD_TARGET - current)))
    # jamais deux zones qui se chevauchent
    found.sort()
    for k in range(1, len(found)):
        if found[k][0] < found[k - 1][1]:
            middle = (found[k][0] + found[k - 1][1]) // 2
            found[k - 1] = (found[k - 1][0], middle, found[k - 1][2])
            found[k] = (middle, found[k][1], found[k][2])
    return [f for f in found if f[1] - f[0] > 0.04 * SAMPLE_RATE]


# --- Fin de mot : coupe juste avant le « k » du mot témoin ------------------------------

def carrier_cut(pcm: "np.ndarray", carrier_start: float) -> int:
    """Le mot témoin « كَمْ » commence par un « k » : tenue silencieuse, puis explosion.
    Le repère de la voix peut tomber AVANT la vraie fin du mot (la dernière voyelle déborde) :
    on part de ce repère et on avance jusqu'au vrai silence du « k » (creux profond), puis
    jusqu'à son explosion ; on coupe juste avant. Tout le mot est donc conservé (validé sur
    la vraie voix, 44 mots)."""
    hop, win = SAMPLE_RATE // 200, SAMPLE_RATE // 100
    frames = np.lib.stride_tricks.sliding_window_view(pcm, win)[::hop]
    level = 10 * np.log10((frames ** 2).mean(1) + 1e-10)
    top = level.max()
    k = max(0, int((carrier_start + DECODER_DELAY - 0.03) * SAMPLE_RATE) // hop)
    limit = min(len(level) - 1, k + int(0.4 * SAMPLE_RATE) // hop)
    # 1) le silence du « k » : premier creux profond (≥ 30 dB sous le maximum)
    while k < limit and level[k] > top - 30:
        k += 1
    if k >= limit:
        return int((carrier_start + DECODER_DELAY + 0.08) * SAMPLE_RATE)   # secours
    # 2) le fond du creux, puis l'explosion (remontée de 15 dB)
    quiet = k
    while quiet + 1 < limit and level[quiet + 1] <= level[quiet] + 3 and level[quiet + 1] < top - 25:
        quiet += 1
        if level[quiet] < level[k]:
            k = quiet
    burst = k
    while burst < limit and level[burst] < level[k] + 15:
        burst += 1
    return max(k * hop + win // 2, burst * hop - int(0.008 * SAMPLE_RATE))


def silence_bounds(pcm: "np.ndarray") -> tuple[int, int]:
    """Retire le long silence que la voix ajoute avant et après le mot (jusqu'à 1 s), en gardant
    une marge : 0,05 s avant le premier son, 0,12 s après le dernier (détente des consonnes
    finales comprise : seuil très bas, -50 dB sous le maximum)."""
    hop = SAMPLE_RATE // 100
    if len(pcm) < 4 * hop:
        return 0, len(pcm)
    frames = np.lib.stride_tricks.sliding_window_view(pcm, hop)[::hop]
    level = 10 * np.log10((frames ** 2).mean(1) + 1e-12)
    loud = np.nonzero(level > level.max() - 50)[0]
    if not len(loud):
        return 0, len(pcm)
    start = max(0, loud[0] * hop - int(0.05 * SAMPLE_RATE))
    end = min(len(pcm), (loud[-1] + 1) * hop + int(0.12 * SAMPLE_RATE))
    return start, end


def _fade_out(pcm: "np.ndarray", seconds: float = FADE) -> "np.ndarray":
    n = min(len(pcm), int(seconds * SAMPLE_RATE))
    if n > 0:
        pcm = pcm.copy()
        pcm[-n:] *= (0.5 + 0.5 * np.cos(np.linspace(0, np.pi, n))).astype(np.float32)
    return pcm


async def speak_pcm(word: str, voice: str, rate: str, stretch: bool = False) -> "np.ndarray":
    """Son d'un mot, prononcé en entier (voyelle finale comprise), voyelles longues allongées
    en mode normal."""
    carrier = ends_with_vowel(word)
    suffix = f" {CARRIER_WORD}" if carrier else ""
    probe, pieces = probe_text(word)
    letters = [word[j] for j in long_vowel_positions(word)]
    want_stretch = stretch and bool(pieces) and len(letters) == len(pieces)
    last_error = None
    for candidate in dict.fromkeys((voice, DEFAULT_VOICE)):
        try:
            jobs = [_edge_audio(word + suffix, candidate, rate, word_boundary=True)]
            if want_stretch:
                jobs.append(_edge_audio(probe + suffix, candidate, rate, word_boundary=True))
            results = await asyncio.gather(*jobs)
            mp3, bounds = results[0]
            pcm = await decode_pcm(mp3)
            end_limit = len(pcm) / SAMPLE_RATE
            if carrier:
                if len(bounds) < 2:
                    raise RuntimeError("repères de mots absents")
                cut = carrier_cut(pcm, bounds[-1][0])
                end_limit = cut / SAMPLE_RATE
                pcm = _fade_out(pcm[:cut])
            # silences ajoutés par la voix, mesurés AVANT l'allongement (mêmes bornes dans les 2 modes)
            keep_from, keep_to = silence_bounds(pcm)
            tail = len(pcm) - keep_to
            if want_stretch:
                try:
                    probe_mp3, probe_bounds = results[1]
                    probe_pcm = await decode_pcm(probe_mp3)
                    probe_marks = probe_bounds[:-1] if carrier else probe_bounds
                    probe_end = carrier_cut(probe_pcm, probe_bounds[-1][0]) / SAMPLE_RATE if carrier \
                        else len(probe_pcm) / SAMPLE_RATE
                    targets = locate_long_vowels(pcm, probe_pcm, probe_marks, word, probe_end)
                    logger.info("%s : voyelles longues à %s", word,
                                [(round(a / SAMPLE_RATE, 3), round(b / SAMPLE_RATE, 3)) for a, b, _ in targets])
                    pcm = stretch_at(pcm, targets)
                except Exception:
                    logger.exception("Prolongement impossible pour %s", word)
            return pcm[keep_from: len(pcm) - tail]
        except Exception as exc:
            last_error = exc
            logger.warning("edge-tts en échec avec %s pour %s (%s)", candidate, word, exc)
    logger.warning("Repli sur gTTS pour %s (%s)", word, last_error)
    return await decode_pcm(await asyncio.to_thread(_gtts_audio, word))


async def render_audio_processed(words: list[str], voice: str, rate: str, pause: float,
                                 stretch: bool) -> tuple[bytes, str]:
    parts = await asyncio.gather(*(speak_pcm(w, voice, rate, stretch) for w in words))
    gap = np.zeros(int(pause * SAMPLE_RATE), dtype=np.float32)
    audio = parts[0]
    for part in parts[1:]:
        audio = np.concatenate([audio, gap, part])
    audio = np.concatenate([audio, np.zeros(int(END_SILENCE * SAMPLE_RATE), dtype=np.float32)])
    return await encode_pcm(audio)


async def render_audio_simple(words: list[str], voice: str, rate: str, pause: float) -> bytes:
    """Version de secours sans ffmpeg : assemblage direct des trames MP3 (pas de prolongement)."""
    segments = await asyncio.gather(*(speak(w, voice, rate) for w in words))
    formats = {mp3_format(s) for s in segments}
    if len(segments) > 1 and (len(formats) != 1 or None in formats):
        segments = [await speak(" ، ".join(words), voice, rate)]
    audio = segments[0]
    for segment in segments[1:]:
        audio += mp3_silence(audio, pause) + segment[_audio_start(segment):]
    return audio + mp3_silence(audio, END_SILENCE)


async def render_audio(words: list[str], voice: str, rate: str, pause: float,
                       stretch: bool = False) -> tuple[bytes, str]:
    """Audio final : un mot, ou une phrase mot par mot avec `pause` secondes entre les mots,
    puis END_SILENCE secondes de silence. `stretch` = voyelles longues étirées (mode normal)."""
    if FFMPEG and np is not None:
        try:
            return await render_audio_processed(words, voice, rate, pause, stretch)
        except Exception:
            logger.exception("Traitement audio impossible : version simple")
    return await render_audio_simple(words, voice, rate, pause), "dictee.mp3"


async def send_voice_note(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, words: list[str], voice: str, rate: str,
    pause: float, caption: str, reply_markup: InlineKeyboardMarkup | None = None, stretch: bool = False,
) -> None:
    await context.bot.send_chat_action(chat_id, ChatAction.RECORD_VOICE)
    audio, filename = await render_audio(words, voice, rate, pause, stretch)
    await context.bot.send_voice(
        chat_id, voice=audio, filename=filename, caption=caption,
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
    settings.pop("madd_extra", None)  # réglage d'une version précédente
    if settings["mode"] not in MODES:
        settings["mode"] = DEFAULT_SETTINGS["mode"]
    if settings["pause"] not in PAUSES:
        settings["pause"] = DEFAULT_SETTINGS["pause"]
    return settings


def audio_params(settings: dict, slow: bool = False) -> tuple[str, str, float, bool]:
    """(voix, débit, pause entre les mots, voyelles longues étirées ?) selon l'élève."""
    rate = SLOW_REPLAY_RATE if slow else SPEEDS[settings["speed"]][1]
    pause = PAUSES[settings["pause"]][1] * (1.5 if slow else 1)
    stretch = settings["mode"] == "normal"
    return settings["voice"], rate, pause, stretch


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


def item_text(item: list[dict]) -> str:
    return " ".join(w["ar"] for w in item)


def item_label(session: dict, index: int) -> str:
    unit = "Phrase" if session["mode"] == "p" else "Mot"
    return f"{unit} {index + 1}/{len(session['items'])}"


def reveal_caption(session: dict, index: int) -> str:
    item = session["items"][index]
    if len(item) == 1:
        details = f"🔤 {html.escape(spelled_letters(item[0]['ar']))}"
    else:
        details = "\n".join(
            f"• {html.escape(w['ar'])}   ({html.escape(spelled_letters(w['ar']))})" for w in item
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
    "3️⃣ /dictee : mots ou phrases, niveau normal (prolongements appuyés) ou difficile\n"
    "🎙️ /voix : choisis la voix qui te parle le mieux\n"
    "⏹ /stop : arrête la dictée en cours\n\n"
    "Je te dicte de vrais mots et, quand il n'y en a pas assez avec tes lettres, "
    "des mots inventés."
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
    if key in ("speed", "pause", "mode"):
        options = list({"speed": SPEEDS, "pause": PAUSES, "mode": MODES}[key])
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
    buttons = [[InlineKeyboardButton(label, callback_data=f"Z:{mode}:{key}")] for key, label in MODES.items()]
    await safe_edit_text(
        query,
        f"📝 <b>Dictée de {unit}</b>\nQuel niveau ?\n\n"
        "🟢 <b>Normal</b> : la voix fait durer les voyelles longues pour bien les entendre.\n"
        "🔴 <b>Difficile</b> : voix naturelle, comme une vraie dictée.",
        reply_markup=InlineKeyboardMarkup(buttons),
    )


async def on_choose_level(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    _, mode, level = query.data.split(":")
    settings_of(context)["mode"] = level
    unit = "phrases" if mode == "p" else "mots"
    buttons = [InlineKeyboardButton(f"{n} {unit if n > 1 else unit[:-1]}", callback_data=f"C:{mode}:{n}")
               for n in SESSION_SIZES[mode]]
    await safe_edit_text(query, f"📝 <b>Dictée de {unit}</b> — {MODES[level]}\nCombien ?",
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
        options = {key: label for key, (label, *_rest) in WORD_LENGTHS.items()}
        question = "Quelle longueur de mots ?"
    buttons = [InlineKeyboardButton(label, callback_data=f"G:{mode}:{count}:{key}") for key, label in options.items()]
    await safe_edit_text(query, f"📝 <b>{count} × {'phrase' if mode == 'p' else 'mot'}</b>\n{question}",
                         reply_markup=InlineKeyboardMarkup([buttons]))


async def on_choose_phrase_size(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Phrases : après le nombre de mots par phrase, choix de la longueur des mots."""
    query = update.callback_query
    await query.answer()
    _, mode, raw_count, size_key = query.data.split(":")
    if size_key not in PHRASE_LENGTHS:
        await safe_edit_text(query, "⚠️ Relance /dictee.")
        return
    buttons = [InlineKeyboardButton(label, callback_data=f"H:{mode}:{raw_count}:{size_key}:{key}")
               for key, (label, *_rest) in WORD_LENGTHS.items()]
    await safe_edit_text(
        query,
        f"📝 <b>{raw_count} × phrase de {PHRASE_LENGTHS[size_key][0]}</b>\nQuelle longueur de mots ?",
        reply_markup=InlineKeyboardMarkup([buttons]),
    )


async def on_start_session(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    parts = query.data.split(":")
    mode, count = parts[1], int(parts[2])
    size_key = parts[3] if mode == "p" else None      # H:p:<nb>:<taille phrase>:<longueur mots>
    length_key = parts[-1]                             # G:w:<nb>:<longueur mots>

    letters: set[str] = context.user_data.get("letters", set())
    problem = letters_problem(letters)
    if problem or length_key not in WORD_LENGTHS or (mode == "p" and size_key not in PHRASE_LENGTHS):
        await safe_edit_text(query, problem or "⚠️ Relance /dictee.")
        return

    settings = settings_of(context)
    recent: list[str] = context.user_data.setdefault("recent_real", [])
    if mode == "p":
        size = PHRASE_LENGTHS[size_key][1]
        taken: set[str] = set()   # aucun mot ne revient d'une phrase à l'autre
        items = [build_session_words(letters, settings, size, length_key, recent, taken) for _ in range(count)]
        intro = f"🗣️ <b>C'est parti : {count} phrase(s) de {size} mots "\
                f"({WORD_LENGTHS[length_key][0]})</b>\n" \
                f"⏸️ {PAUSES[settings['pause']][0]} de pause entre les mots (modifiable dans /reglages)\n"
    else:
        items = [[w] for w in build_session_words(letters, settings, count, length_key, recent)]
        intro = f"🎧 <b>C'est parti : {count} mots de {WORD_LENGTHS[length_key][0]}</b>\n"
    all_words = [w for item in items for w in item]
    recent.extend(w["ar"] for w in all_words if w["fr"])
    del recent[:-RECENT_REAL_MAX]

    context.user_data["session"] = {"id": secrets.token_hex(4), "mode": mode, "items": items, "index": 0}
    await safe_edit_text(
        query,
        intro + f"{MODES[settings['mode']]}\n"
        "Écoute, écris sur ta feuille, puis vérifie.",
    )
    await send_current_item(query.message.chat_id, context)


async def send_current_item(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    session = context.user_data["session"]
    index = session["index"]
    item = session["items"][index]
    voice, rate, pause, extra = audio_params(settings_of(context))
    try:
        await send_voice_note(
            context, chat_id, [w["ar"] for w in item], voice, rate, pause,
            f"🎧 <b>{item_label(session, index)}</b> — écoute et écris sur ta feuille.",
            word_keyboard(session, index, revealed=False), stretch=extra,
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
    voice, rate, pause, extra = audio_params(settings_of(context), slow=True)
    try:
        await send_voice_note(
            context, query.message.chat_id, [w["ar"] for w in session["items"][index]], voice, rate, pause,
            f"🐢 {item_label(session, index)}, au ralenti", stretch=extra,
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
    app.add_handler(CallbackQueryHandler(on_choose_level, pattern=r"^Z:[wp]:(normal|difficile)$"))
    app.add_handler(CallbackQueryHandler(on_choose_count, pattern=r"^C:[wp]:\d+$"))
    app.add_handler(CallbackQueryHandler(on_start_session, pattern=r"^G:w:\d+:\w+$"))
    app.add_handler(CallbackQueryHandler(on_choose_phrase_size, pattern=r"^G:p:\d+:\w+$"))
    app.add_handler(CallbackQueryHandler(on_start_session, pattern=r"^H:p:\d+:\w+:\w+$"))
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
