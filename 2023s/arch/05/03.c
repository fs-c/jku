float f0 = 3.0;
float f1 = 0.046875;

int main() {
    float f2 = 5.0;
    float f3 = 2.0;

    do {
        f2 += 2;
        f0 /= 5.0;
    } while ((f0 * f2) >= f1);
}
