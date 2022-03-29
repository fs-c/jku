package jku.tk.mms.quotedprintableSS22;
import static org.junit.Assert.assertEquals;
import org.junit.Test;

public class QuotedPrintableCodecTest {

	private final String[]	PLAIN	= new String[] {
			"Hätten Hüte ein ß im Namen, wären sie möglicherweise keine Hüte mehr, sondern Hüße.",
			"Keine Umlaute",
			"Träume sind Schäume",
			"In der Schule saß ich rum, verfluchte das Curriculum, da ich von Bio und von Mathe keinen blassen Schimmer hatte.",
			"Mühe machte mir Geschichte, weil ich meist im Trüben fischte. Auch in Physik und in Chemie verpeilte ich die Theorie."
			};
	
	private final String[]	QUOTED	= new String[] {
			"H=E4tten H=FCte ein =DF im Namen, w=E4ren sie m=F6glicherweise keine H=FCte mehr, sondern H=FC=DFe.",
			"Keine Umlaute",
			"Tr=E4ume sind Sch=E4ume",
			"In der Schule sa=DF ich rum, verfluchte das Curriculum, da ich von Bio und von Mathe keinen blassen Schimmer hatte.",
			"M=FChe machte mir Geschichte, weil ich meist im Tr=FCben fischte. Auch in Physik und in Chemie verpeilte ich die Theorie."
			};
	
	@Test
	public void testUmlautsEncode() {
		QuotedPrintableCodec c = new QuotedPrintableCodec();
		for (int i = 0; i < PLAIN.length; i++) {
			String q = c.encode(PLAIN[i]);
			assertEquals(QUOTED[i], q);
		}
	}
	
	@Test
	public void testUmlautsDecode() {
		QuotedPrintableCodec c = new QuotedPrintableCodec();
		for (int i = 0; i < QUOTED.length; i++) {
			String p = c.decode(QUOTED[i]);
			assertEquals(PLAIN[i], p);
		}
	}
}