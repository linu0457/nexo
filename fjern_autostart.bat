@echo off
chcp 65001 >nul
net session >nul 2>&1
if errorlevel 1 (
  echo  Højreklik og vælg "Kør som administrator".
  pause
  exit /b 1
)
schtasks /delete /tn "NexoShop" /f
echo.
echo  Autostart er fjernet.
pause
