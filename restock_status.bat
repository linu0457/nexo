@echo off
cd /d "%~dp0"
title Restock status
echo.
netstat -an | findstr "127.0.0.1:47234" | findstr "LISTENING" >nul
if %errorlevel%==0 (echo  Restock-programmet KOERER.) else (echo  Restock-programmet KOERER IKKE.)
echo.
echo  --- Lager paa Eldorado og antal keys klar ^(intet aendres^) ---
py offer.py
echo.
if exist keys.txt (for /f %%a in ('find /c /v "" ^< keys.txt') do echo  Linjer i keys.txt: %%a) else echo  keys.txt findes ikke
if exist keys_inbox.txt (for /f %%a in ('find /c /v "" ^< keys_inbox.txt') do echo  Linjer i keys_inbox.txt ^(uploadet, ikke hentet endnu^): %%a) else echo  keys_inbox.txt: tom ^(ok^)
echo.
echo  Restock laegger KUN keys op naar lageret er UNDER 100. Er lageret 100 eller mere, venter den.
echo.
pause
