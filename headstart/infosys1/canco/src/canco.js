const { setToString, union, difference, isSubset,
    areEqualSets } = require('./utils');

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
        for (const A of dep.alpha) {
            const attrs = difference(dep.alpha, new Set([ A ]));

            if (!attrs.size)
                continue;

            const closure = attributeClosure(dependencies, attrs);

            if (isSubset(dep.beta, closure)) {
                dep.alpha = attrs;
            }
        }
    }

    for (const dep of dependencies) {
        for (const B of dep.beta) {
            const bset = new Set([B]);

            const deps = union(
                difference(dependencies, new Set([dep])),
                new Set([{ alpha: dep.alpha, beta: difference(dep.beta, bset) }]),
            );

            if (!deps.size)
                continue;

            const closure = attributeClosure(deps, dep.alpha);

            if (isSubset(bset, closure)) {
                dep.beta = difference(dep.beta, bset);
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

module.exports = {
    attributeClosure, canonicalCover,
};
