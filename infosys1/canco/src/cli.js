#!/usr/bin/env node

const { stringToDeps, setToString } = require('./utils');
const { attributeClosure, canonicalCover } = require('./canco');

const [ ,, ...args ] = process.argv;

if ([ '--help', '-h' ].includes(args[0])) {
    console.log(`
Usage:

    canco --help/-h
        Outputs this help message

    canco [functional dependencies]
        Outputs the canonical cover for the given set of functional dependencies 
        (A-B,B-CD,D-A)

    canco closure [attributes] [functional dependencies]
        Outputs the closure of the given set of attributes (A,B,C,...) for the 
        given set of functional dependencies (A-B,B-CD,D-A).

Set notation:

    Sets are comma (but not space!) delimited strings: A,B,C is recognized but 
    A, B, C is not
    `);
} if (args[0] === 'closure') {
    const deps = stringToDeps(args[2]);
    const attrs = new Set(args[1].split(','));

    console.log(setToString(attributeClosure(deps, attrs)));
} else {
    const deps = stringToDeps(args[0]);

    console.log(canonicalCover(deps));
}
