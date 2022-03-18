import * as readline from 'node:readline';

const drawSudoku = (values) => {
    for (let i = 0; i < 4; i++) {
        const row = [];
        
        for (let j = 0; j < 4; j++) {
            row.push(values[j + (i * 4)]);
        }

        console.log(row.join(' '));
    }
};

const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: false,
});

const lines = [];

rl.on('line', (input) => {
    if (!input.startsWith('%')) {
        lines.push(input);
    }
});

rl.on('close', () => {
    const values = [];

    for (const line of lines) {
        const [ variable, truth ] = line.split(' = ');

        if (truth == '0') {
            continue;
        }

        const [ index, value ] = variable.split('_');

        if (values[index - 1]) {
            console.error('warning: invalid input', line);
        }

        values[index - 1] = value;
    }

    drawSudoku(values);
});
