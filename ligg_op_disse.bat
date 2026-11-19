@echo off
cd /d "%~dp0"
title Ligg 25 keys op (koeres kun een gang)
if not exist ligg_op_disse.py (
  echo Denne fil er allerede koert og slettet.
  pause
  (goto) 2>nul & del "%~f0"
)
py ligg_op_disse.py %*
echo.
if not exist ligg_op_disse.py (
  echo Faerdig - filen er slettet.
  pause
  (goto) 2>nul & del "%~f0"
)
pause
