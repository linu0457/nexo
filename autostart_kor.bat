@echo off
rem Started by Windows when the server turns on (made by installer_autostart.bat). Runs everything and writes to dashboard.log
cd /d "%~dp0"
set PYTHONIOENCODING=utf-8
if exist dashboard.log for %%A in (dashboard.log) do if %%~zA gtr 5000000 move /y dashboard.log dashboard.old.log >nul
echo ===== started %date% %time% ===== >> dashboard.log
py -u start_all.py >> dashboard.log 2>&1
