from EmulatorGUI import GPIO
import time
GPIO.setmode(GPIO.BCM)
import threading
import logging
# setup logging
logger = logging.getLogger(__name__)
logging.basicConfig(level="INFO")


led_pin=24

class Button():
    def __init__(self, channel):
        self.channel = channel
        self._thread=threading.Thread(name='button',target=self.run)
        self._thread.deamon = True
        self._thread_active = True
        self._thread.start()

    def run(self):
        logger.info("button thread started")
        previous = 1
        current = 0
        while self._thread_active:
            time.sleep(0.01)
            current = GPIO.input(self.channel)
            logger.debug("current %s previous %s",current,previous)
            if current==1 and previous==0:
                  logger.info("button was pressed and released")
                  self.onButtonPress()
            previous = current

    def onButtonPress(self):
        global led_pin
        if led_pin==24:
            led_pin=25
        else: 
            led_pin=24
        GPIO.output(24, False)
        GPIO.output(25, False)
    def stop(self):
        logger.debug("stopping thread")
        self._thread_active = False

try:
  # setup gpio
  GPIO.setup(18, GPIO.IN, pull_up_down=GPIO.PUD_UP)
  button=Button(18)
  GPIO.setup(24, GPIO.OUT)
  GPIO.setup(25, GPIO.OUT)
  GPIO.output(24, False)
  GPIO.output(25, False)


  while True:
      # toggle gpio
      GPIO.output(led_pin, True)
      time.sleep(1)
      GPIO.output(led_pin, False)
      time.sleep(1)
except KeyboardInterrupt:     
    button.stop()
    logger.info("stopping ...")     
    time.sleep(1)
    GPIO.cleanup()                 
