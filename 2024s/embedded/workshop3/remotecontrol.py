#!/usr/bin/python

from __future__ import division
import time
import paho.mqtt.client as mqtt
import logging
from EmulatorGUI import GPIO
from at.jku.pervasive.eps.mymqttmessages.mymqttmessages_pb2 import *

# setup logging

logger = logging.getLogger(__name__)
logging.basicConfig(level="INFO")

# setup gpio
GPIO.setmode(GPIO.BCM)
LED_RED=25
LED_GREEN=24
GPIO.setup(LED_RED, GPIO.OUT)
GPIO.setup(LED_GREEN, GPIO.OUT)
GPIO.output(LED_RED, False)
GPIO.output(LED_GREEN, False) 

# mqtt connect callback function
def on_connect(client, userdata, flags, rc):
	logger.info('Connected with result code %s',str(rc))
	# Subscribing in on_connect() means that if we lose the connection and
	# reconnect then subscriptions will be renewed.
	client.subscribe("K11804751", qos=0)


# mqtt message received callback function
def on_message(client, userdata, msg):
	commandString=str(msg.payload)
	proto_msg = PBMessage()
	try:
		proto_msg.ParseFromString(msg.payload)
	 
		if proto_msg.HasField('ledControl'):
			logger.debug('got message at %s with content %s',str(msg.topic),commandString)
			logger.info('got message from %s (with target %s)',proto_msg.source,proto_msg.target)
			logger.info('ledControl numberic %s %s %s',proto_msg.ledControl.action,proto_msg.ledControl.led,proto_msg.ledControl.toggleRateHz)
			logger.info('ledControl Info %s %s %s',LedAction.Name(proto_msg.ledControl.action),Led.Name(proto_msg.ledControl.led),proto_msg.ledControl.toggleRateHz)
			led_pin=-1

			# Set pin
			if Led.Value('RED')==proto_msg.ledControl.led:
				led_pin=LED_RED
			elif Led.Value('GREEN')==proto_msg.ledControl.led:
				led_pin=LED_GREEN
			else: 
				logger.error('cannot map led %s to pin',Led.Name(proto_msg.ledControl.led))
				return 
			# Set action
			# TODO: Read action from message and control LED
			if proto_msg.ledControl.action==LedAction.Value('ON'):
				GPIO.output(led_pin,1)
			else:
				GPIO.output(led_pin,0)
			# end of ledControl processing
		else:
			logger.warn('got message at %s with content %s',str(msg.topic),commandString)
	except:
		logger.warning('Unable to decode message: No valid ProtoBuf Msg received')
# setup mqtt
client = mqtt.Client()
client.on_connect = on_connect
client.on_message = on_message

# connect mqtt
client.connect("broker.hivemq.com", 1883, 60)
try:
	client.loop_forever()
except (KeyboardInterrupt, SystemExit): 
	logger.info('disconnecting ...')
	client.disconnect()
	time.sleep(1)
	GPIO.cleanup()