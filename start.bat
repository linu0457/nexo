@echo off
cd /d C:\eldorado
start "orders" /min cmd /c "for /l %%i in (0,0,1) do (py -u order_alerts.py & timeout /t 5 >nul)"
start "stock" /min cmd /c "for /l %%i in (0,0,1) do (py -u stock_board.py & timeout /t 5 >nul)"
start "reviews" /min cmd /c "for /l %%i in (0,0,1) do (py -u review_alerts.py & timeout /t 5 >nul)"