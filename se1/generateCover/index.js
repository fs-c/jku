const HummusRecipe = require('hummus-recipe');
const pdfDoc = new HummusRecipe(process.argv[2], 'output.pdf');

const textHeight = 221;
const textOptions = {
    size: 11,
    color: '#000000',
};

// const lineOptions = {
//     lineWidth: 1,
//     color: '#000000',
// };

// const drawCross = (x, y) => {
//     pdfDoc.line([[ x, y ], [ x + 4, y + 4 ]], lineOptions);
//     pdfDoc.line([[ x, y + 4 ], [ x + 4, y ]], lineOptions);
// };

pdfDoc.editPage(1);

pdfDoc
    .text('Laurenz Weixlbaumer', 98, textHeight, textOptions)
    .text('11804751', 442, textHeight, textOptions)

pdfDoc.endPage();
pdfDoc.endPDF();