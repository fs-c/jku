## 1.1

we expect x and y to be close to zero g and z to be close to 1 g (because it is at rest, and affected by gravity)

## 1.2

time acc x acc y acc z gyr x gyr y gyr z mag x mag y mag z

1710510287225, 0.01, 0.09, 0.94, 0.00, 0.00, 0.00, -9.76, -27.29, 16.92
1710510287765, -0.01, -0.00, 0.97, 0.03, -0.05, 0.01, -15.39, -44.25, 26.25
1710510288307, 0.06, 0.02, 0.96, 0.05, -0.08, 0.01, -16.91, -52.01, 31.04
1710510288846, 0.05, 0.01, 0.97, -0.06, 0.09, -0.01, -17.94, -56.20, 33.49
1710510289389, 0.08, 0.02, 0.95, -0.08, 0.12, -0.02, -17.58, -57.48, 34.31
1710510289928, 0.13, 0.05, 1.01, 0.10, -0.12, 0.08, -16.54, -57.01, 35.34
1710510290471, 0.27, 0.13, 0.97, 0.04, -0.50, -0.13, -13.15, -53.37, 33.13
1710510291017, 0.33, 0.11, 0.86, 0.13, -0.08, 0.06, -8.03, -49.43, 29.82
1710510291560, 0.38, 0.09, 0.85, -0.07, 0.17, 0.00, -5.01, -47.85, 27.32
1710510292103, 0.35, 0.10, 0.91, -0.05, -0.04, 0.04, -3.89, -47.59, 26.18

we expected the values to be more steady

## 1.3

todo

## 2a

if z is below some threshold (tbd experimentally) then we consider the sensor to be falling

## 2b

todo

## 2c

if abs(acc_x) > 0.5 or abs(acc_y) > 0.5 or abs(acc_z) > 1.5:
