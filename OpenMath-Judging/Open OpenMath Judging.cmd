@echo off
cd /d "%~dp0"
py -3 judging_app.py
if errorlevel 9009 python judging_app.py
