from EmulatorGUI import GPIO
from time import sleep
import logging
# setup logging
logger = logging.getLogger(__name__)
logging.basicConfig(level="INFO")

# set GPIO Mode 
GPIO.setmode(GPIO.BCM)
# setup GPIO pins
GPIO.setup(18, GPIO.IN, pull_up_down=GPIO.PUD_UP)
GPIO.setup(24, GPIO.OUT)
GPIO.setup(25, GPIO.OUT)
GPIO.output(24, False)
GPIO.output(25, False)

pin=24

try:
   while True:
      button_state = GPIO.input(18)
      logger.info("button state is %s (pressed=%s)",button_state,not bool(button_state))
      if button_state == False:
           pin=24
      else: 
           pin=25
      GPIO.output(pin, True)
      sleep(1)
      GPIO.output(pin, False)
      sleep(1)
except KeyboardInterrupt: 
    logger.info("cleaning up ...")         
    GPIO.cleanup()