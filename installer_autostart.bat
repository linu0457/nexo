@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo.
echo  Sætter dashboardet til at starte af sig selv, når serveren tændes.
echo.
net session >nul 2>&1
if errorlevel 1 (
  echo  FEJL: Højreklik på denne fil og vælg "Kør som administrator".
  echo.
  pause
  exit /b 1
)
echo  Du bliver bedt om din Windows-adgangskode (den du logger på VPS'en med).
echo  Den bruges kun af Windows til at starte opgaven, også når ingen er logget ind.
echo.
schtasks /create /tn "NexoShop" /tr "\"%~dp0autostart_kor.bat\"" /sc onstart /delay 0001:00 /ru "%USERNAME%" /rp * /rl highest /f
if errorlevel 1 (
  echo.
  echo  Det lykkedes ikke. Send teksten ovenfor til Claude.
  pause
  exit /b 1
)
echo.
echo  KLAR. Dashboardet starter nu automatisk 1 minut efter, at serveren er tændt.
echo  Det kører skjult. Log kan ses i filen dashboard.log.
echo  Luk de vinduer, der kører nu, hvis du vil teste ved at genstarte serveren.
echo.
pause
