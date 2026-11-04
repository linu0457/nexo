@echo off
cd /d "%~dp0"
rem Brug: gendan_keys.bat [antal] [spring-over]   (standard: 25 keys, spring de 25 allernyeste over)
set A=%1
if "%A%"=="" set A=25
set S=%2
if "%S%"=="" set S=25
py offer.py gendan --antal %A% --spring %S%
pause
