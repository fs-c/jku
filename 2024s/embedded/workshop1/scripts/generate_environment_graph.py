import os
import csv
import matplotlib.pyplot as plt

# Function to read data from the CSV file
def read_data(filename):
    time = []
    temp = []
    humidity = []
    pressure = []
    with open(filename, 'r') as file:
        reader = csv.reader(file)
        next(reader)  # Skip header row if exists
        for row in reader:
            time.append(float(row[0]))
            temp.append(float(row[1]))
            humidity.append(float(row[2]))
            pressure.append(float(row[3]))
    return time, temp, humidity, pressure

# Function to plot environmental data
def plot_environmental_data(time, temp, humidity, pressure, filename):
    fig = plt.figure(figsize=(10, 6))
    
    plt.subplot(3, 1, 1)
    plt.plot(time, temp, color='r')
    plt.title('Temperature over Time')
    plt.xlabel('Time')
    plt.ylabel('Temperature (°C)')

    plt.subplot(3, 1, 2)
    plt.plot(time, humidity, color='g')
    plt.title('Humidity over Time')
    plt.xlabel('Time')
    plt.ylabel('Humidity (%)')

    plt.subplot(3, 1, 3)
    plt.plot(time, pressure, color='b')
    plt.title('Pressure over Time')
    plt.xlabel('Time')
    plt.ylabel('Pressure (hPa)')

    plt.tight_layout()

    plt.show()
    
    output_filename = os.path.splitext(filename)[0] + '.png'
    fig.savefig(output_filename)
    print(f"figure saved as {output_filename}")

# Main function
def main():
    filename = 'environment1.csv'
    time, temp, humidity, pressure = read_data(filename)
    plot_environmental_data(time, temp, humidity, pressure, filename)

if __name__ == "__main__":
    main()