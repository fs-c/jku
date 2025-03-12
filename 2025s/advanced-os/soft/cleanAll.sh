#!/bin/bash

# Hello World
cd HelloWorld
make clean
cd ..

# Keyboard LED
cd KbdLED
make clean
cd ..

# Keyboard LED - HR timers
cd KbdLED-HR
make clean
cd ..

# Keyboard LED - Userspace
cd USLED
make clean
cd ..

# Process file system
cd procfs
make clean
cd ..

# KProbes / symbols
cd syms
make clean
cd ..

# Keylogger
cd kbd
make clean
cd ..

# TSR
cd tsr
make clean
cd ..

# Loader
cd loader
make clean
cd ..

# shortFUSE
cd shortFUSE
make clean
cd ..
