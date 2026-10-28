@echo off
cd /d "%~dp0"
echo Ny udgave koerer paa http://localhost:8124 (test - den rigtige side er uroert)
start "" http://localhost:8124
py dashboard_ny.py run --preview
pause
