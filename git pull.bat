@echo off
cd /d "%~dp0"
title Git pull
echo.
echo === Henter nyeste filer fra GitHub (starter ikke noget) ===
git config core.autocrlf true >nul 2>&1
git checkout -- .                                                       >nul 2>&1
git pull --ff-only
if errorlevel 1 (
  echo.
  echo Kunne ikke hente. Er der lavet rettelser lokalt, eller er der ingen forbindelse?
) else (
  echo.
  echo Faerdig. Intet er genstartet - brug opdater.bat naar du vil starte med de nye filer.
)
pause
