#!/usr/bin/env node

const { stringToDeps, setToString } = require('./utils');
const { attributeClosure, canonicalCover } = require('./canco');

const [ ,, ...args ] = process.argv;

const printHelp = () => console.log(`
Usage:

    canco --help/-h
        Outputs this help message

    canco [functional dependencies] [-s/--short]
        Outputs the canonical cover for the given set of functional dependencies 
        (Default: Aa.Bb-Cc,Cc-Dd, short form: AB-C,C-D)

    canco closure [attributes] [functional dependencies] [-s/--short]
        Outputs the closure of the given set of attributes (A,B,C,...) for the 
        given set of functional dependencies (see above for an example).

Options:

    -s/--short
        Enables short form parsing, limits attribute names to a single character 
        but removes the need for attribute seperators (A-B,B-CD,D-A)

Set notation:

    Sets are comma (but not space!) delimited strings: A,B,C is recognized but 
    A, B, C is not
`);

if (!args.length || [ '-', '--help' ].includes(args[0])) {
    return printHelp();
}

const short = args.includes('-s') || args.includes('--short');

if (args[0] === 'closure') {
    const deps = stringToDeps(args[2], { short });
    const attrs = new Set(args[1].split(','));

    console.log(setToString(attributeClosure(deps, attrs)));
} else {
    const deps = stringToDeps(args[0], { short });

    console.log(canonicalCover(deps));
}
