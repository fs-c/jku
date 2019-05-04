class ComplexNumbers {
    public static void main(String[] args) {

    }
}

class Complex {
    final float real;
    final float imag;

    Complex() {
        this.real = 0.0f;
        this.imag = 0.0f;
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
        return String.format("%f + %fi", this.real, this.imag);
    }

    @Override
    public boolean equals(Object otherObject) {
        Complex other = (Complex)otherObject;

        return this.real == other.real && this.imag == other.imag;
    }
}