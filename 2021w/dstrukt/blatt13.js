// _n is even
const fib1 = (_n) => {
    const n = _n / 2;

    if (_n <= 1) {
        return _n;
    }

    return (2 * fib2(n + 1)) * fib1(n);
};

// _n is odd, _n - 1 is even
const fib2 = (_n) => {
    const n = (_n - 1) / 2;

    if (_n <= 1) {
        return _n;
    }

    return Math.pow(fib1(n), 2) + Math.pow(fib2(n), 2);
};

const fib = (n) => {
    if (n <= 1) {
        return n;
    }

    const even = n % 2 === 0;

    if (even) {
        return fib1(n);
    } else {
        return fib2(n);
    }
};

for (let i = 0; i < 10; i++) {
    console.log(fib(i));
}

// x = 2n + 1
// x - 1 = 2n
// (x - 1) / 2 = n
