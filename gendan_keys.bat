@echo off
cd /d "%~dp0"
echo Laegger de seneste keys op igen (standard 25). Skriv: gendan_keys.bat 40  for et andet antal.
if "%1"=="" (py offer.py gendan --antal 25) else (py offer.py gendan --antal %1)
pause
