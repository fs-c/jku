Makefile:
    - Added simulation stop time of 100ns to break endless loops

endless_branch.s / endless_branch.txt
    - Added file with example from Lecture 06_prozessoraufbau (v1.1) slide 17

endless_jump.s /endless_jump.txt
    - Added file to create example for slide from übungsstunde

riscvsingle.vhdl
    - Set instruction start index to 0x1000 (1024) to fit lecture slide
    - Added initialization function to dmem to fit lecture slide
    - Added initialization function to regfile to fit lecture slide
    - Added reset value to set pc to start address 0x1000
