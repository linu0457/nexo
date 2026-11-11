@echo off
cd /d "%~dp0"
title Restock - lagger keys op paa Eldorado
echo.
echo  RESTOCK: tager de nye keys (keys.txt og dem du har uploadet paa hjemmesiden)
echo  og lagger dem op paa dit tilbud, indtil lageret er fyldt op.
echo  Eldorado-fejl: den holder pause 5 min og fortsaetter selv.
echo  Hold vinduet aabent. Luk det (eller Ctrl+C) for at stoppe.
echo.
py offer.py auto
echo.
echo  Hvis der staar "ALREADY running": restock koerer allerede (dashboardet startede den), og den
echo  henter selv dine nye keys inden for et par sekunder. Du behoever ikke goere mere.
echo.
pause
