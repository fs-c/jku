const stringToDeps = (string) => string.split(';')
    .map((sub) => {
        const [ alpha, beta ] = sub.split('-');

        return { alpha: new Set(alpha.split(',')),
            beta: new Set(beta.split(',')) };
    });

const setToString = (set) => {
    let string = '';

    for (const el of set)
        string += el;
    
    return string.split('').sort().join('');
}

const union = (a, b) => new Set([...a, ...b]);
const difference = (a, b) => new Set([...a].filter((el) => !b.has(el)));

const isSubset = (sub, sup) => [...sub].every((el) => sup.has(el));
const areEqualSets = (a, b) => a.size === b.size && isSubset(a, b);

module.exports = {
    stringToDeps, setToString,
    union, difference,
    isSubset, areEqualSets,
};
