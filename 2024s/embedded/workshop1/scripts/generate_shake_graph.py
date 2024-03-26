import os
import csv
import matplotlib.pyplot as plt

# Function to read data from the CSV file
def read_data(filename):
    time = []
    acc_x = []
    acc_y = []
    acc_z = []
    with open(filename, 'r') as file:
        reader = csv.reader(file)
        next(reader)  # Skip header row if exists
        for row in reader:
            time.append(float(row[0]))
            acc_x.append(float(row[1]))
            acc_y.append(float(row[2]))
            acc_z.append(float(row[3]))
    return time, acc_x, acc_y, acc_z

# Function to plot accelerometer data
def plot_accelerometer_data(time, acc_x, acc_y, acc_z, filename):
    fig = plt.figure(figsize=(10, 6))
    
    plt.subplot(3, 1, 1)
    plt.plot(time, acc_x, color='r')
    plt.title('Accelerometer X over Time')
    plt.xlabel('Time')
    plt.ylabel('Acc X')

    plt.subplot(3, 1, 2)
    plt.plot(time, acc_y, color='g')
    plt.title('Accelerometer Y over Time')
    plt.xlabel('Time')
    plt.ylabel('Acc Y')

    plt.subplot(3, 1, 3)
    plt.plot(time, acc_z, color='b')
    plt.title('Accelerometer Z over Time')
    plt.xlabel('Time')
    plt.ylabel('Acc Z')

    plt.tight_layout()

    plt.show()

    output_filename = os.path.splitext(filename)[0] + '.png'
    fig.savefig(output_filename)
    print(f"figure saved as {output_filename}")

# Main function
def main():
    filename = 'shake1.csv'
    time, acc_x, acc_y, acc_z = read_data(filename)
    plot_accelerometer_data(time, acc_x, acc_y, acc_z, filename)

if __name__ == "__main__":
    main()