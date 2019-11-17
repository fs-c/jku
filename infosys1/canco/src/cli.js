#!/usr/bin/env node

const { stringToDeps, setToString } = require('./utils');
const { attributeClosure, canonicalCover } = require('./canco');

const [ ,, ...args ] = process.argv;

if (args[0] === 'closure') {
    const deps = stringToDeps(args[2]);
    const attrs = new Set(args[1].split(','));

    console.log(setToString(attributeClosure(deps, attrs)));
} else {
    const deps = stringToDeps(args[0]);

    console.log(canonicalCover(deps));
}
