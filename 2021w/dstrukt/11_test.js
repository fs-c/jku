const occ = [];

const gen = (b0, b1, b2, b3) => {
    return b0 + b1 + 2 * b2 + 4 * b3;
};

for (let i = 0; i < 1000000; i++) {
    const val = gen(
        Math.round(Math.random()),
        Math.round(Math.random()),
        Math.round(Math.random()),
        Math.round(Math.random())
    );

    occ[val] = occ[val] ? occ[val] + 1 : 1;
}

for (let i = 0; i < 10; i++) {
    occ[i] /= 1000000;
}


console.log(occ);
