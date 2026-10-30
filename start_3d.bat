@echo off
cd /d "%~dp0"
start "" http://localhost:8125
py dashboard_3d.py run --preview
