/**
 * Converts raw "box-game" input into limboole syntax.
 */

 import { EOL } from 'os';
 import fs from 'fs/promises';

const inputFilePath = 'input.txt';
const outputFilePath = 'encoding51.boole';

const convert = (input) => {
    const clauses = [];
    const inputLines = input.split(EOL);

    for (const line of inputLines) {
        const clause = [];
        const atoms = line.split(' ');

        for (const atom of atoms) {
            const lowerAtom = atom.toLowerCase();

            clause.push(atom === lowerAtom ? atom : '!' + lowerAtom);
        }

        clauses.push(clause.join('|'));
    }

    return clauses.map((clause) => '(' + clause + ')').join('&');
};

(async () => {
    const input = await fs.readFile(inputFilePath, 'utf-8');

    await fs.writeFile(outputFilePath, await convert(input));
})().then().catch(console.error);
