@echo off
chcp 65001 >nul
cd /d "%~dp0"
title Bot dictee arabe

if not exist ".venv\Scripts\python.exe" (
    echo Premiere installation, patiente une minute...
    py -m venv .venv 2>nul || python -m venv .venv
    if not exist ".venv\Scripts\python.exe" (
        echo.
        echo [ERREUR] Python est introuvable. Installe-le depuis python.org
        echo en cochant bien "Add python.exe to PATH", puis relance ce fichier.
        pause
        exit /b 1
    )
)

echo Verification des bibliotheques...
".venv\Scripts\python.exe" -m pip install -q --disable-pip-version-check -r requirements.txt
if errorlevel 1 (
    echo [ERREUR] Installation des bibliotheques impossible. Verifie ta connexion internet.
    pause
    exit /b 1
)

echo.
".venv\Scripts\python.exe" bot.py
echo.
echo Le bot est arrete.
pause
