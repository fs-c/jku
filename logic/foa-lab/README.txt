============================================================================

README.txt
How to run laboratory exercises with the RISCAL software.
(c) 2021, Project LogTechEdu, http://fmv.jku.at/logtechedu/

============================================================================

1. THE RISCAL SOFTWARE
----------------------
These exercises are to be executed with the RISCAL software available at
   
  https://www.risc.jku.at/research/formal/software/RISCAL
  
For the purpose of this course, RISCAL can be most easily used in one of the
following two ways:

  A. Recommended: download a virtual Linux machine with RISCAL preinstalled.
  B. Alternative: Run RISCAL on a remote server installation.

Both options are described at the end of this document in Sections A and B.


2. RUNNING THE EXERCISES
-------------------------
Each exercise is performed on the basis of a corresponding RISCAL
specification file handed out in the assignment. In detail:

1. You start the RISCAL software and load the file.
2. You edit the file, update it by the requested answers, and save it.
3. You run the denoted operations to check the correctness of your answers.
   
The result of each exercise is then the updated RISCAL file itself.

Depending on whether you run the RISCAL software in a virtual machine or on
a remote server, there are various ways to transfer a modified RISCAL file to
your own computer, see Sections A and B.

However, there is also an easy way to just copy the contents of a RISCAL 
file to your own computer, simply by "copy & paste":

1. Create a new file in an (UTF-8 capable) editor on your own computer
2. "Copy & Paste" via the sequence <Ctrl>-A, <Ctrl>-C, <Ctrl>-V (respectively
   on a German keyboard <Strg>-A, <Strg>-C, <Strg>-V) the contents of the file 
   from RISCAL to your editor.
3. Save the file in your editor (make sure that the file is encoded in UTF-8).


3. EDITING RISCAL FILES
-----------------------
RISCAL specification files are plain text files in UTF-8 format (they may
also contain Unicode characters that are not in the ASCII standard); these
files are typically only edited within the RISCAL software itself.

In a RISCAL specification file you may edit arbitrary text within the
comments marked as /*...* / or // ... (displayed in green). Outside these 
comments, the file contains formal material that may be only edited as 
indicated by the description of the corresponding exercise.

After a file modification, press in the "File" panel of the RISCAL software
the button "Save" to save the file. Alternatively, you may type <Ctrl>-S
respectively <Strg>-S.

YOU HAVE TO SAVE THE FILE BEFORE YOU MAY RUN ANY OPERATION OF THE RISCAL
SOFTWARE ON THIS FILE.


4. THE RISCAL FORMULA SYNTAX
----------------------------
In the RISCAL software, logical operators (connectives and quantifiers) can
be either entered as ASCII strings or as Unicode symbols. You get the
Unicode symbol if you type first the ASCII string and then <Ctrl>-#
respectively <Strg>-# (if this does not work, insert an empty space
character before the ASCII string, place the text cursor immediately after
the ASCII string and type <Ctrl>-# respectively <Strg>-# again). In
particular, we have the following operators:

                   ASCII   Unicode  ASCII Example       Unicode Example
   * true:         true    ⊤        true                ⊤
   * false:        false   ⊥        false               ⊥
   * negation:     ~       ¬        (~p(x))             (¬p(x))
   * conjunction:  /\      ∧        (p(x) /\ q(x))      (p(x) ∧ q(x))
   * disjunction:  \/      ∨        (p(x) \/ q(x))      (p(x) ∨ q(x))
   * implication:  =>      ⇒        (p(x) => q(x))      (p(x) ⇒ q(x))
   * equivalence:  <=>     ⇔        (p(x) <=> q(x))     (p(x) ⇔ q(x))
   * forall:       forall  ∀        (forall x:D. p(x))  (∀x:D. p(x))
   * exists:       exists  ∃        (exists x:D. p(x))  (∃x:D. p(x))

Operators are listed in order of decreasing binding power (negation binds
strongest); by considering this, many parentheses may be omitted.

Please note that implication is denoted by the double arrow "=>" (rather
than by the single arrow "->"). Furthermore, a quantified formula is written
as "∀x:D. p(x)" (rather than "∀x: p(x)"), also note the period "." before
the body of the formula (here a variable declaration "x:D" indicates that
variable x ranges over values from domain D).


4. RUNNING RISCAL OPERATIONS
----------------------------
After having saved a RISCAL specification file, you can select from the
"Analysis" panel by the menu "Operation: ..." some of the operations
(function, predicate, theorem) you have specified in the file.

Then you may (or you may not) select the option "Execution: Silent"
which will suppress verbose output when running the operation.

Then you can press the "Start Execution" button (labeled by a green arrow)
to run the operation; the panel below shows the output of the operation;
if a message "ERROR ..." appears, then the execution has given an error
(e.g., a supposed theorem is actually not true).

You can copy and paste text from the output panel to any editor. Pressing
the button "Clear Output" (labeled by a yellow broom) clears the output.


5. MAKING A SCREENSHOT OF A RISCAL SESSION
------------------------------------------
You can make on your own computer a screenshot of a RISCAL session with
the software that your computer provides.

Typically you select with your mouse the window of which you want to make a
screenshot, then press <Alt>+<Prnt> (on a German keyboard: <Alt>+<Druck>),
and finally paste the window in some graphics program running on your
computer from where you can save it as an image file.

If you run RISCAL in a virtual machine, you may make a screenshot of the
window in which the user interface of the virtual machine is displayed. If
you run RISCAL on a remote server, you may make a screenshot of the window
in which the remote session is displayed.


A. RUNNING RISCAL IN A VIRTUAL MACHINE
--------------------------------------
Follow the instructions given on the Moodle page in order to

* install the VirtualBox software on your computer,
* download the virtual Linux machine with an installation of RISCAL,
* import the virtual machine into VirtualBox,
* configure a directory on your computer (the “host”) that is shared with 
  the virtual machine (the “guest”) such that you can exchange files 
  between guest and host.
  
Then login into the virtual machine as user “guest” and open a terminal.
Your current working directory is now the home directory of “guest”. Here
you execute the commands

  mkdir RISCAL-Logic
  cd RISCAL-Logic
  wget <URL>
  tar zxf RISCAL-Logic.tgz
  ls -la

where <URL> is to be replaced by 

  https://www.risc.jku.at/people/schreine/courses/software/RISCAL-Logic.tgz
    
This downloads the RISCAL exercise files from a web server into a directory
"RISCAL-Logic". You may then execute

  RISCAL <filename>.txt &

to start the RISCAL software and load any file with name <filename>.txt
from that directory. When you have modified the file, you can transfer
it to the directory shared with your host computer by executing

  cp <filename>.txt ~/host/.

However, you may also just copy file contents from the editor of the
RISCAL software to an editor of your host computer by "copy & paste".


B. RUNNING RISCAL ON THE REMOTE SERVER
--------------------------------------
To use the server installation of RISCAL, first install an X2Go client 
(available for MS Windows, MacOS and GNU Linux) from

  https://wiki.x2go.org

on your computer. Then start the client and create under "Sitzung"
("Session") a "Neue Sitzung" ("New Session") with the following data:

  Host:         rat.risc.jku.at
  Login:        riscal
  Session type: Published Applications 
  (Sitzungsart: Veröffentlichte Anwendungen)

Having created the session, click on the session button and enter the
password handed out in the course (use it only for the purpose of this
course and do not distribute it to others).

If a window pops up that asks to select an existing session, this is due to
another user who currently runs a session. Do *not* stop the existing session
but press "New" to create a new session. As soon as the session status is
shown as "active", press the disc-like button on the left bottom of the
window and select "Education/Bildung" and then "RISCAL" to start RISCAL.

For your convenience, you will find in the home directory already the RISCAL
files of the various exercises which you may overwrite with your results.
Just open these files (menu entry "File/Open"), modify them, and save them.

When you are done, you may terminate RISCAL. You will be then asked for
an email address to which the content of the server directory (including
your updated file) will be sent.

ALL FILES ARE DISCARDED WHEN YOU LOGOUT; SO BE SURE TO ENTER A VALID EMAIL
ADDRESS TO WHICH THE FILES ARE SENT. FURTHERMORE IT IS A GOOD IDEA TO
REGULARLY COPY&PASTE THE CONTENT OF A MODIFIED FILE TO YOUR OWN COMPUTER
(IF THE NETWORK CONNECTION IS INTERRUPTED, YOU LOOSE YOUR MODIFICATIONS).

After having finished, quit RISCAL, close the "Published Applications"
window, and terminate the X2Go session by clicking at the "Power Off" button
at the bottom right of the X2Go window. When you have returned to the login
screen, you can close the X2Go client.

PLEASE TERMINATE THE X2GO SESSION AS DESCRIBED ABOVE IN AN ORDERLY WAY. IF
YOU JUST CLOSE THE X2GO CLIENT, THE SESSION MAY NOT BE PROPERLY TERMINATED.


============================================================================
end of file
============================================================================
