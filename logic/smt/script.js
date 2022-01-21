const file = require('fs').readFileSync('51.limboole', 'utf8');
const lines = file.split('\n');

for (let i = 0; i < lines.length; i++) {
    const label = 'l' + (i + 1);
    const content = lines[i].slice(lines[i].indexOf('(') + 1, lines[i].lastIndexOf(')'));

    if (!content) {
        continue;
    }

    const literals = content.split('&').map((e) => e.trim())
        .map((l) => `(!${label} | ${l})`)
        .join(' & ');

    console.log(literals);     
}

