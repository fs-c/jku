const HummusRecipe = require('hummus-recipe');
const pdfDoc = new HummusRecipe(process.argv[2], 'output.pdf');

const textHeight = 221;
const textOptions = {
    size: 11,
    color: '#000000',
};

pdfDoc.editPage(1);

pdfDoc
    .text('Laurenz Weixlbaumer', 98, textHeight, textOptions)
    .text('11804751', 442, textHeight, textOptions)

pdfDoc.endPage();
pdfDoc.endPDF();