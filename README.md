# Bot Telegram — Dictée en arabe

Le bot invente des mots avec uniquement les lettres cochées par l'élève, les envoie en
note vocale, puis révèle l'écriture vocalisée sur demande.

## Contenu du dossier

| Fichier | Rôle |
|---|---|
| `bot.py` | Le programme du bot |
| `config.txt` | **À remplir** : ton token BotFather (+ voix et vitesse) |
| `requirements.txt` | Les bibliothèques Python nécessaires |
| `lancer.bat` | Windows : double-clic pour installer et lancer |
| `lancer.command` | Mac : `bash lancer.command` dans le Terminal |

Créés automatiquement au premier lancement : `.venv/` (bibliothèques), `audio_tmp/`
(audios temporaires, vidés automatiquement), `bot_data.pickle` (lettres de chaque élève).

## Démarrage rapide

1. Installe Python (python.org), en cochant « Add python.exe to PATH » sous Windows.
2. Crée ton bot avec @BotFather sur Telegram et copie le token.
3. Colle le token dans `config.txt` à la place de `COLLE_TON_TOKEN_ICI`.
4. Windows : double-clic sur `lancer.bat`. Mac : `bash lancer.command` dans le Terminal.

Le mode opératoire complet (test, hébergement 24 h/24, partage aux amis, dépannage)
est dans le guide fourni avec le bot.

## Réglages dans bot.py

| Constante | Effet |
|---|---|
| `SESSION_SIZES` | Nombres de mots proposés (3, 5, 10) |
| `WORD_LENGTHS` | Longueur des mots courts / moyens / longs, en syllabes |
| `ALLOW_INITIAL_HAMZA` | `False` si la hamza (أ / إ) n'a pas encore été vue en cours |
