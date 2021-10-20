//  1  2  3  4
//  5  6  7  8
//  9 10 11 12
// 13 14 15 16

// Each field is associated with four variables indicating its value (1 - 4). 
// This is analogous to graph coloring, except that conceptually, we're dealing 
// with numbers instead of colors.
// We will name the variables "field_value". So 1_2 means field 1 has value 2. 

const fields = [];

for (let f = 1; f <= 16; f++) {
    const variables = [];

    for (let v = 1; v <= 4; v++) {
        variables.push(`${f}_${v}`);
    }

    fields.push(variables);
}

let formula = '';

// 1. Each field has a value.

formula += fields.map((f) => `(${f.join(' | ')})`).join(' & ');

// 2. Each field has at most one value.

formula += '\n&\n';

formula += fields.map((f) => (
    f.flatMap((v, i, a) => a.slice(i + 1).map((e) => `(!${v} | !${e})`))
        .join(' & ')
)).join(' & ');

// 3. "Connected" fields have different values.

// [ 1, 2 ]   [ 1, 3, 5 ]
// [ 3, 4 ] > [ 2, 4, 6 ]
// [ 5, 6 ]
const transpose = (array) => array.reduce(
    (acc, row) => row.map((_, i) => [ ...(acc[i] || []), row[i] ]), []
);

// 3.a Fields in the same row have different values.

for (let row = 0; row < 4; row++) {
    formula += '\n&\n' + transpose(fields.slice(row * 4, 4 + (row * 4)))
        .map((row) => (
            row.flatMap((v, i, a) => a.slice(i + 1).map((e) => `(!${v} | !${e})`))
                .join(' & ')
        )).join(' & ');
}

// 3.b Fields in the same column have different values.

for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
        const col = [];

        for (let k = 0; k < 4; k++) {
            col.push(fields[(k * 4) + i][j]);
        }

        formula += '\n&\n' + col.flatMap((v, i, a) => a.slice(i + 1)
            .map((e) => `(!${v} | !${e})`)).join(' & ');
    }
}

// 3.c Fields in the same square have different values.

// Top left of all squares
const indices = [ 0, 2, 8, 10 ];

for (const i of indices) {
    const square = [ fields[i], fields[i + 1], fields[i  + 4], fields[i + 5] ];

    formula += '\n&\n' + transpose(square).map((e) => (
        e.flatMap((v, i, a) => a.slice(i + 1)
            .map((e) => `(!${v} | !${e})`)).join(' & ')
    )).join(' & ');
}

console.log(formula + (process.argv[2] || ''));
