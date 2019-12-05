const { PDFDocument, StandardFonts } = require('pdf-lib');

const existingPDF = require('fs').readFileSync(__dirname + '/plain_cover.pdf');

const to = process.argv[3];
const from = process.argv[2];

const textHeight = 620;
const explHeight = 482;

(async () => {
    const pdfDoc = await PDFDocument.load(existingPDF);
    const helveticaFont = await pdfDoc.embedFont(StandardFonts.Helvetica);

    const textOptions = {
        size: 11,
        font: helveticaFont,
    }

    const firstPage = pdfDoc.getPages()[0];

    firstPage.drawText('11804751', {
        y: textHeight,
        x: 80,
        ...textOptions,
    });

    firstPage.drawText('Laurenz Weixlbaumer', {
        y: textHeight,
        x: 165,
        ...textOptions,
    });

    firstPage.drawText('990', {
        y: textHeight,
        x: 480,
        ...textOptions,
    });

    firstPage.drawText('X', {
        y: 549,
        x: 73,
        ...textOptions,
    });

    firstPage.drawText(from, {
        y: explHeight,
        x: 172,
        ...textOptions,
    });

    firstPage.drawText(to, {
        y: explHeight,
        x: 244,
        ...textOptions,
    });

    const pdfBytes = await pdfDoc.save()

    require('fs').writeFileSync('./output.pdf', pdfBytes);
})();
