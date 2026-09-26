#!/bin/bash
# Lancement du bot sur Mac (ou Linux) : bash lancer.command
cd "$(dirname "$0")" || exit 1

if [ ! -x ".venv/bin/python" ]; then
    echo "Première installation, patiente une minute…"
    if ! python3 -m venv .venv; then
        echo
        echo "[ERREUR] Python est introuvable. Installe-le depuis python.org puis relance."
        read -r -p "Appuie sur Entrée pour fermer"
        exit 1
    fi
fi

echo "Vérification des bibliothèques…"
if ! .venv/bin/python -m pip install -q --disable-pip-version-check -r requirements.txt; then
    echo "[ERREUR] Installation des bibliothèques impossible. Vérifie ta connexion internet."
    read -r -p "Appuie sur Entrée pour fermer"
    exit 1
fi

echo
.venv/bin/python bot.py
echo
read -r -p "Le bot est arrêté. Appuie sur Entrée pour fermer"
