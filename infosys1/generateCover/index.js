const HummusRecipe = require('hummus-recipe');
const pdfDoc = new HummusRecipe(__dirname + '/plain_cover.pdf', 'output.pdf');

const to = process.argv[3];
const from = process.argv[2];

const textHeight = 215;
const explHeight = 351;
const textOptions = {
    size: 11,
    color: '#000000',
};

pdfDoc.editPage(1);

pdfDoc
    .text('11804751', 80, textHeight, textOptions)
    .text('Laurenz Weixlbaumer', 165, textHeight, textOptions)
    .text('990', 485, textHeight, textOptions)
    .text('X', 73, 284, textOptions);

pdfDoc
    .text(from, 172, explHeight, textOptions)
    .text(to, 244, explHeight, textOptions);

pdfDoc.endPage();
pdfDoc.endPDF();