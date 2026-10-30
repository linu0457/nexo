@echo off
cd /d "%~dp0"
title Opdater Nexo-Shop
echo.
echo === Henter nyeste version fra GitHub ===
git checkout -- dashboard_3d.py dashboard_ny.py >nul 2>&1
git pull --ff-only
if errorlevel 1 (
  echo.
  echo Kunne ikke hente. Er der lavet rettelser lokalt, eller er der ingen forbindelse?
  echo Luk dette vindue, eller tryk en tast for at starte alligevel med den gamle version.
  pause
)
echo.
echo === Tjekker programmer ===
py -m pip install --quiet --disable-pip-version-check flask waitress pywebpush requests
echo.
if not exist valgt_version.txt echo dashboard_3d.py> valgt_version.txt
echo === Starter alt ===
echo (Luk det gamle vindue med start_all foerst, ellers koerer tingene to gange.)
echo.
py start_all.py
echo.
echo Stoppet.
pause
