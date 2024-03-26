from sense_hat import SenseHat
import time

sense = SenseHat()
sense.clear()

round_digits = 2

while True:
    acceleration = sense.get_accelerometer_raw()
    acc_x = acceleration['x']
    acc_y = acceleration['y']
    acc_z = acceleration['z']

    gyroscope = sense.get_gyroscope_raw()
    gyr_x = gyroscope['x']
    gyr_y = gyroscope['y']
    gyr_z = gyroscope['z']

    magnetometer = sense.get_compass_raw()
    mag_x = magnetometer['x']
    mag_y = magnetometer['y']
    mag_z = magnetometer['z']

    gyr_x = round(gyr_x, round_digits)
    gyr_y = round(gyr_y, round_digits)
    gyr_z = round(gyr_z, round_digits)

    acc_x = round(acc_x, round_digits)
    acc_y = round(acc_y, round_digits)
    acc_z = round(acc_z, round_digits)

    mag_x = round(mag_x, round_digits)
    mag_y = round(mag_y, round_digits)
    mag_z = round(mag_z, round_digits)

    print(
        "{},{:7.2f},{:7.2f},{:7.2f},{:7.2f},{:7.2f},{:7.2f},{:7.2f},{:7.2f},{:7.2f}".
        format(
            int(round(time.time() * 1000)), acc_x, acc_y, acc_z, gyr_x, gyr_y,
            gyr_z, mag_x, mag_y, mag_z))

    time.sleep(0.5)