#!/bin/bash
# Installation / mise à jour du bot sur un serveur Ubuntu, en une commande :
#   curl -fsSL https://raw.githubusercontent.com/TON_COMPTE/dictee-arabe/main/install.sh | bash -s TON_COMPTE
# Relancer la même commande met le bot à jour (le token est conservé).
set -euo pipefail

GITHUB_USER="${1:-}"
REPO_URL="https://github.com/${GITHUB_USER}/dictee-arabe.git"
APP_DIR=/opt/dictee-arabe
SERVICE=/etc/systemd/system/dictee.service

step() { echo; echo "==> $*"; }
fail() { echo; echo "[ERREUR] $*"; exit 1; }

[ "$(id -u)" -eq 0 ] || fail "Connecte-toi en root (ssh root@IP) puis relance la commande."
[ -n "$GITHUB_USER" ] || fail "Nom du compte GitHub manquant à la fin de la commande."

step "Installation des outils système (1 à 2 min)"
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq
apt-get install -y -qq git python3-venv >/dev/null

step "Téléchargement du bot depuis GitHub"
if [ -d "$APP_DIR/.git" ]; then
    git -C "$APP_DIR" pull --ff-only -q
else
    rm -rf "$APP_DIR"
    git clone -q "$REPO_URL" "$APP_DIR" || fail "Impossible de lire $REPO_URL (dépôt public ? bon nom de compte ?)"
fi
[ -f "$APP_DIR/bot.py" ] || fail "bot.py introuvable dans le dépôt : vérifie que les fichiers sont à la racine."

step "Installation des bibliothèques Python"
python3 -m venv "$APP_DIR/.venv"
"$APP_DIR/.venv/bin/pip" install -q --disable-pip-version-check -r "$APP_DIR/requirements.txt"

step "Token du bot"
LOCAL_CFG="$APP_DIR/config.local.txt"
if grep -qE '^TELEGRAM_BOT_TOKEN=[0-9]+:' "$LOCAL_CFG" 2>/dev/null; then
    echo "Token déjà enregistré : je le garde."
else
    while true; do
        read -r -p "Colle le token donné par @BotFather puis appuie sur Entrée : " TOKEN < /dev/tty
        TOKEN="$(printf '%s' "$TOKEN" | tr -d '[:space:]')"
        [[ "$TOKEN" =~ ^[0-9]+:[A-Za-z0-9_-]{30,}$ ]] && break
        echo "Ce n'est pas un token valide (format 123456789:ABC...). Réessaie."
    done
    printf 'TELEGRAM_BOT_TOKEN=%s\n' "$TOKEN" > "$LOCAL_CFG"
fi

step "Sécurisation et démarrage automatique"
id dictee >/dev/null 2>&1 || useradd --system --no-create-home --shell /usr/sbin/nologin dictee
chown root:dictee "$LOCAL_CFG"
chmod 640 "$LOCAL_CFG"   # seul le bot peut lire le token

cat > "$SERVICE" <<EOF
[Unit]
Description=Bot Telegram dictee arabe
After=network-online.target
Wants=network-online.target

[Service]
User=dictee
WorkingDirectory=$APP_DIR
Environment=DATA_DIR=/var/lib/dictee
StateDirectory=dictee
ExecStart=$APP_DIR/.venv/bin/python bot.py
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
EOF

systemctl daemon-reload
systemctl enable -q dictee
systemctl restart dictee
sleep 6

if systemctl is-active --quiet dictee; then
    echo
    echo "✅ Le bot tourne 24 h/24. Envoie /start à ton bot dans Telegram."
    echo "   Voir ses messages : journalctl -u dictee -f   (Ctrl+C pour quitter)"
else
    echo
    journalctl -u dictee -n 20 --no-pager
    fail "Le bot ne démarre pas : envoie ces lignes à Claude."
fi
