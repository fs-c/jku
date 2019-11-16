const { stringToDeps, setToString, union, difference, isSubset,
    areEqualSets } = require('./utils');

const inputDeps = stringToDeps(process.argv[2]);

const attributeClosure = (dependencies, attributes) => {
    let result = attributes;

    while (true) {
        let prev = result;

        for (const { alpha, beta } of dependencies) {
            if (isSubset(alpha, result)) {

                result = union(result, beta);
            }
        }

        if (areEqualSets(result, prev))
            return result;
    }
};

const canonicalCover = (dependencies) => {
    for (const dep of dependencies) {
        const { alpha, beta } = dep;

        for (const A of alpha) {
            const attrs = difference(alpha, new Set([ A ]));

            if (!attrs.size)
                continue;

            const closure = attributeClosure(dependencies, attrs);

            if (isSubset(beta, closure)) {
                dep.alpha = attrs;
            }
        }
    }

    for (const dep of dependencies) {
        const { alpha, beta } = dep;

        for (const B of beta) {
            const bset = new Set([B]);

            const deps = union(
                difference(dependencies, new Set([{ alpha, beta }])),
                new Set([{ alpha, beta: difference(beta, bset) }]),
            );

            if (!deps.size)
                continue;

            const closure = attributeClosure(deps, alpha);

            if (isSubset(bset, closure)) {
                dep.beta = difference(beta, bset);
            }
        }
    }

    const actual = {};

    for (const { alpha, beta } of dependencies) {
        const string = setToString(alpha).split('').sort().join('');
        actual[string] = union(actual[string] || new Set([]), beta);
    }

    for (const a in actual)
        actual[a] = setToString(actual[a]).split('').sort().join('');

    return actual;
};

console.log(canonicalCover(inputDeps));
