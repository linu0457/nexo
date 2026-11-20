@echo off
cd /d "%~dp0"
title Opret nye offers som kopi (saet paa pause)
py opret_offer.py %*
echo.
pause
