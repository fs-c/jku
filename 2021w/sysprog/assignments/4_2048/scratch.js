const size = 4;
const cells = [];

// Fill cells
for (let i = 0; i < size; i++) {
    cells[i] = [];

    for (let j = 0; j < size; j++) {
        cells[i][j] = 0;
    }
}

const printCells = (cells) => {
    for (const row of cells) {
        console.log(row);
    }

    console.log();
}

cells[0][0] = 16;
cells[0][1] = 8;
cells[0][2] = 8;
cells[0][3] = 16;

cells[1][0] = 16;
cells[1][2] = 8;
cells[1][3] = 8;

cells[2][0] = 32;

cells[3][0] = 64;

printCells(cells);

const cellEmpty = (cells, y, x) => {
    return cells[y][x] === 0;
};

const moveCell = (cells, fixed, index, offset) => {
    if (cells[fixed][index] === 0) {
        cells[fixed][index] = cells[fixed][index + offset];
        cells[fixed][index + offset] = 0;
    } else if (cells[fixed][index] === cells[fixed][index + offset]) {
        cells[fixed][index] = cells[fixed][index] * 2;
        cells[fixed][index + offset] = 0;
    }
};

// [ 0, 2, 2, 0 ] to [ 4, 0, 0, 0 ]
const moveLeft = (cells) => {
    for (let row = 0; row < cells.length; row++) {
        for (let i = 1; i < cells[row].length; i++) {
            if (cells[row][i] === 0) {
                continue;
            }

            // Let the value "bubble" to the left and combine it with same values
            // on the way
            for (let j = i - 1; j >= 0; j--) {
                moveCell(cells, row, j, 1);
            }
        }
    }

    return cells;
};

// [ 0, 2, 2, 0 ] to [ 0, 0, 0, 2 ]
const moveRight = (cells) => {
    for (let row = 0; row < cells.length; row++) {
        for (let i = cells[row].length - 2; i >= 0; i--) {
            if (cells[row][i] === 0) {
                continue;
            }

            // Let the value "bubble" to the right and combine it with same values
            // on the way
            for (let j = i + 1; j < cells[row].length; j++) {
                moveCell(cells, row, j, -1);
            }
        }
    }

    return cells;
};

const move = (cells, direction) => {
    const reverse = direction === 'down' || direction === 'right';    
    const horizontal = direction === 'left' || direction === 'right';

    console.log({ reverse, horizontal });

    // Represents the row for left/right and col for up/down
    for (let fixed = 0; fixed < cells.length; fixed++) {
        // Start from the back when moving in reverse
        let i = reverse ? cells.length - 2 : 1;
        for (; reverse ? i >= 0 : i < cells.length; reverse ? i-- : i++) {
            if (horizontal ? cells[fixed][i] === 0 : cells[i][fixed] === 0) {
                continue;
            }

            // We will now let cells[fixed][i] bubble to its proper position by
            // continuously switching it with empty cells and merging it with cells 
            // of equal value. 

            // This is the movement direction starting from `i`.
            const offset = reverse ? 1 : -1;

            for (let j = i + offset; reverse ? j < cells.length : j >= 0; j += offset) {
                
            }

            // for (let j = i - offset; reverse ? j < cells.length : j >= 0; j -= offset) {
            //     if (horizontal) {
            //         moveCell(cells, fixed, j, offset);
            //     } else {
            //         moveCell(cells, j, fixed, offset);
            //     }
            // }
        }
    }

    return cells;
};

const moveUp = (cells) => {
    for (let col = 0; col < cells.length; col++) {
        for (let i = 1; i < cells.length; i++) {
            if (cells[i][col] === 0) {
                continue;
            }

            // Let the value "bubble" to the top and combine it with same values
            // on the way
            for (let j = i - 1; j >= 0; j--) {
                moveCell(cells, j, col, 1);
            }
        }
    }

    return cells;
};

const moveDown = (cells) => {
    for (let col = 0; col < cells.length; col++) {
        for (let i = cells.length - 2; i >= 0; i--) {
            if (cells[i][col] === 0) {
                continue;
            }

            // Let the value "bubble" to the bottom and combine it with same values
            // on the way
            for (let j = i + 1; j < cells.length; j++) {
                moveCell(cells, j, col, -1);
            }
        }
    }

    return cells;
};

console.log(move(cells, 'left'));

// printCells(moveDown(cells));

// printCells(moveLeft(cells));
// printCells(move(cells, 'left'));

// printCells(moveRight(cells));
// printCells(move(cells, 'right'));

// printCells(moveUp(cells));
// printCells(move(cells, 'up'));

// printCells(moveDown(cells));
// printCells(move(cells, 'down'));
