#!/bin/bash

# Hello World
cd HelloWorld
make all
cd ..

# Keyboard LED
cd KbdLED
make all
cd ..

# Keyboard LED - HR timers
cd KbdLED-HR
make all
cd ..

# Keyboard LED - Userspace
cd USLED
make all
cd ..

# Process file system
cd procfs
make all
cd ..

# KProbes / symbols
cd syms
make all
cd ..

# Keylogger
cd kbd
make all
cd ..

# TSR
cd tsr
make all
cd ..

# Loader
cd loader
make all
cd ..

# shortFUSE
cd shortFUSE
make all
cd ..
