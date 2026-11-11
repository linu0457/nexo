@echo off
cd /d "%~dp0"
title Restock
netstat -an | findstr "127.0.0.1:47234" | findstr "LISTENING" >nul
if %errorlevel%==0 (
  echo.
  echo  Restock KOERER allerede ^(startet af dashboardet / opdater.bat^).
  echo  Den henter selv dine nye keys inden for ca. 10 sekunder og lagger dem op,
  echo  naar lageret er under maalet. Du behoever ikke goere mere.
  echo.
  pause
  exit /b
)
echo.
echo  Restock koerer IKKE lige nu - starter den. Hold vinduet aabent.
echo  Eldorado-fejl: den holder pause 5 min og fortsaetter selv.
echo.
py offer.py auto
echo.
pause
