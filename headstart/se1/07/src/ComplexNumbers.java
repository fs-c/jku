class ComplexNumbers {
    public static void main(String[] args) {
        Complex c1 = new Complex();
        Complex c2 = new Complex(0, 0);
        Complex c3 = new Complex(1, -2);

        Out.format("c1: %s, c2: %s, c3: %s%n", c1, c2, c3);
        Out.format("c1 == c2, %s%n", c1 == c2 ? "true" : "false");
        Out.format("c2 == c3, %s%n", c2 == c3 ? "true" : "false");
        Out.format("c1 + c2 = %s%n", c1.add(c2));
        Out.format("c2 + c3 = %s%n", c2.add(c3));
    }
}

class Complex {
    final float real;
    final float imag;

    Complex() {
        this(0.0f, 0.0f);
    }

    Complex(float real, float imag) {
        this.real = real;
        this.imag = imag;
    }

    Complex add(Complex summand) {
        return new Complex(this.real + summand.real, this.imag + summand.imag);
    }

    @Override
    public String toString() {
        boolean neg = this.imag < 0;

        return String.format("%f %s %fi", this.real, neg ? "-" : "+",
            (neg ? -1.0f : 1.0f) * this.imag);
    }

    @Override
    public boolean equals(Object otherObject) {
        Complex other = (Complex)otherObject;

        return this.real == other.real && this.imag == other.imag;
    }
}