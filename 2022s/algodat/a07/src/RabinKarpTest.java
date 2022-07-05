

import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

public class RabinKarpTest {
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpNullPattern() {
		Exception exCaught = null;
		try {
			RabinKarp.search(null, "falsdfjsdlkf");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertTrue(exCaught instanceof IllegalArgumentException || exCaught instanceof NullPointerException, "RabinKarp.search() with null pattern should raise an IllegalArgumentException but raised: "+exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpNullText() {
		Exception exCaught = null;
		try {
			RabinKarp.search("falsdfjsd",null);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertTrue(exCaught instanceof IllegalArgumentException || exCaught instanceof NullPointerException, "RabinKarp.search() with null text should raise an IllegalArgumentException but raised: "+exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpEmpty() {		
		ArrayList<Integer> result = null;
		final String strPattern = "aaa";
		final String strText = "abcdexxxunbexxxkeaa";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		try {
			result = RabinKarp.search(strPattern, strText);
		} catch (Exception ex){
			assertNull(ex, errMsg + " raised an: " + ex);
		}

		assertNotNull(result, errMsg + " should not return null!");
		assertEquals(0, result.size(), errMsg + ": Pattern should not be found but found " + result.size() + " time(s) at idx " + printArrayList(result) + ".");
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpEmpty2() {		
		final String strPattern = "aaa";
		final String strText = "";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
		} catch (Exception ex){
			assertNull(ex, errMsg + " raised an: " + ex);
		}

		assertNotNull(result, errMsg + " should not return null!");
		assertEquals(0, result.size(), errMsg + ": Pattern should not be found but found " + result.size() + " time(s) at idx " + printArrayList(result) + ".");
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpShort() {
		final String strPattern = "xxx";
		final String strText = "abcdexxxunbxxxke";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}

		try {
			assertEquals(2, result.size(), errMsg+" returned wrong result.size(): ");
		
			Integer[] occurrences = {5,11};
			
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpSpecial() {
		final String strPattern = "xxx";
		final String strText = "xxxxxA";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
		try {
			assertEquals(3, result.size(), errMsg+" returned wrong result.count: ");
		
			Integer[] occurrences = {0,1,2};
			
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpSpecial2() {
		final String strPattern = "xxx";
		final String strText = "xxxxflkaxxxxA";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
		try {
			assertEquals(4, result.size(), errMsg+" returned wrong result.count: ");
		
			Integer[] occurrences = {0,1,8,9};
								
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpSpecial3() {
		final String strPattern = "xyxy";
		final String strText = "xxyxyxyflkaxyxxyxyA";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
		try {
			assertEquals(3, result.size(), errMsg+" returned wrong result.count: ");
		
			Integer[] occurrences = {1,3,14};
			
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpLong() {
		final String strPattern = "is";
		final String strText = "Compares two strings lexicographically. The comparison is based on the Unicode value of each character in the strings. The character sequence represented by this String object is compared lexicographically to the character sequence represented by the argument string. The result is a negative integer if this String object lexicographically precedes the argument string. The result is a positive integer if this String object lexicographically follows the argument string. The result is zero if the strings are equal; compareTo returns 0 exactly when the equals(Object) method would return true.";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
		try {
			assertEquals(9, result.size(), errMsg+" returned wrong result.count: ");
		
			Integer[] occurrences = {50, 55, 159, 176, 279, 306, 382, 409, 484};
			
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpLongPattern() {
		final String strPattern = "ijK lmnop";
		final String strText = "abcdefghijK lmnopqrstuvwxyz, abcdefghijK lmnopqrstuvwxyz.ijk lmnopqr";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
		try {
			assertEquals(2, result.size(), errMsg+" returned wrong result.count: ");
		
			Integer[] occurrences = {8,37};
			
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
	}

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpVeryLong() {
		final String strPattern = "Lorem ips";
		final String strText = "Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod "
				+ "tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo "
				+ "dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum "
				+ "dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam "
				+ "erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea "
				+ "takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam "
				+ "nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et "
				+ "justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. "
				+ "Duis autem vel eum iriure dolor in hendrerit in vulputate velit esse molestie consequat, vel illum dolore eu feugiat "
				+ "nulla facilisis at vero eros et accumsan et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue "
				+ "duis dolore te feugait nulla facilisi. Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy "
				+ "nibh euismod tincidunt ut laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud "
				+ "exerci tation ullamcorper suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor "
				+ "in hendrerit in vulputate velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et "
				+ "accumsan et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla "
				+ "facilisi. Nam liber tempor cum soluta nobis eleifend option congue nihil imperdiet doming id quod mazim placerat facer "
				+ "possim assum. Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut "
				+ "laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper "
				+ "suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor in hendrerit in vulputate "
				+ "velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis. At vero eos et accusam et justo duo dolores "
				+ "et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit "
				+ "amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed "
				+ "diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata "
				+ "sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, At accusam aliquyam "
				+ "diam diam dolore dolores duo eirmod eos erat, et nonumy sed tempor et et invidunt justo labore Stet clita ea et "
				+ "gubergren, kasd magna no rebum. sanctus sea sed takimata ut vero voluptua. est Lorem ipsum dolor sit amet. Lorem ipsum "
				+ "dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam "
				+ "erat. Consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed "
				+ "diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata "
				+ "sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod "
				+ "tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores "
				+ "et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit "
				+ "amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed "
				+ "diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata "
				+ "sanctus. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et "
				+ "dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita "
				+ "kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur "
				+ "sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. "
				+ "At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem "
				+ "ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt "
				+ "ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. "
				+ "Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Duis autem vel eum iriure dolor in"
				+ " hendrerit in vulputate velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et "
				+ "accumsan et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla "
				+ "facilisi. Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut "
				+ "laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper "
				+ "suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor in hendrerit in vulputate "
				+ "velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et accumsan et iusto odio "
				+ "dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla facilisi. Nam liber tempor "
				+ "cum soluta nobis eleifend option congue nihil imperdiet doming id quod mazim placerat facer possim assum. Lorem ipsum "
				+ "dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut laoreet dolore magna aliquam "
				+ "erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper suscipit lobortis nisl ut aliquip "
				+ "ex ea commodo "
				+ "Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod "
				+ "tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo "
				+ "dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum "
				+ "dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam "
				+ "erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea "
				+ "takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam "
				+ "nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et "
				+ "justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. "
				+ "Duis autem vel eum iriure dolor in hendrerit in vulputate velit esse molestie consequat, vel illum dolore eu feugiat "
				+ "nulla facilisis at vero eros et accumsan et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue "
				+ "duis dolore te feugait nulla facilisi. Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy "
				+ "nibh euismod tincidunt ut laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud "
				+ "exerci tation ullamcorper suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor "
				+ "in hendrerit in vulputate velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et "
				+ "accumsan et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla "
				+ "facilisi. Nam liber tempor cum soluta nobis eleifend option congue nihil imperdiet doming id quod mazim placerat facer "
				+ "possim assum. Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut "
				+ "laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper "
				+ "suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor in hendrerit in vulputate "
				+ "velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis. At vero eos et accusam et justo duo dolores "
				+ "et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit "
				+ "amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed "
				+ "diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata "
				+ "sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, At accusam aliquyam "
				+ "diam diam dolore dolores duo eirmod eos erat, et nonumy sed tempor et et invidunt justo labore Stet clita ea et "
				+ "gubergren, kasd magna no rebum. sanctus sea sed takimata ut vero voluptua. est Lorem ipsum dolor sit amet. Lorem ipsum "
				+ "dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam "
				+ "erat. Consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed "
				+ "diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata "
				+ "sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod "
				+ "tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores "
				+ "et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit "
				+ "amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed "
				+ "diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata "
				+ "sanctus. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et "
				+ "dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita "
				+ "kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur "
				+ "sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. "
				+ "At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem "
				+ "ipsum dolor sit amet. Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt "
				+ "ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. "
				+ "Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet. Duis autem vel eum iriure dolor in"
				+ " hendrerit in vulputate velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et "
				+ "accumsan et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla "
				+ "facilisi. Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut "
				+ "laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper "
				+ "suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor in hendrerit in vulputate "
				+ "velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et accumsan et iusto odio "
				+ "dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla facilisi. Nam liber tempor "
				+ "cum soluta nobis eleifend option congue nihil imperdiet doming id quod mazim placerat facer possim assum. Lorem ipsum "
				+ "dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut laoreet dolore magna aliquam "
				+ "erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper suscipit lobortis nisl ut aliquip "
				+ "ex ea commodo.";
		final String errMsg = "RabinKarp.search() with input pattern \""+strPattern+"\" and input text \""+strText+"\"";
		ArrayList<Integer> result = null;
		
		try {
			result = RabinKarp.search(strPattern, strText);
			assertNotNull(result, errMsg + " should not return null!");
		} catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
		
		try {
			assertEquals(52, result.size(), errMsg+" returned wrong result.count: ");
		
			Integer[] occurrences = {0, 268, 296, 564, 592, 860, 1159, 1826, 2345, 2373, 2641, 2669, 2937, 2965, 3342, 3370, 3638, 3666, 3931, 4199, 4227, 4495, 4523, 4791, 5090, 5757, 6019, 6287, 6315, 6583, 6611, 6879, 7178, 7845, 8364, 8392, 8660, 8688, 8956, 8984, 9361, 9389, 9657, 9685, 9950, 10218, 10246, 10514, 10542, 10810, 11109, 11776};
							
			for (Integer i : occurrences) {
				assertTrue(result.contains(i), errMsg+": Occurrence at idx "+i+" was not found! (Expected indices: "+printArray(occurrences)+" / your indices: "+printArrayList(result)+")");
			}
			
		}catch (Exception ex) {
			assertNull(ex, errMsg + " raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpHashOfPattern() {
		final String strPattern = "ef";
		try {
			long hashPattern = RabinKarp.getRollingHashValue(strPattern.toCharArray(), '\u0000', -1);
			// for base 31: 3233
			assertEquals(3031,hashPattern, "RabinKarp.getRollingHashValue(): Calculating the single hash value for the pattern \""+strPattern+"\" returned wrong result: ");
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input pattern \"" + strPattern + "\", lastCharacter = '\u0000' and previous hash code = 0 raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpHashOfTextSequences() {
		final String strText = "abcdef";
		final String errMsg = "RabinKarp.getRollingHashValue():Calculating the rolling hash values (input text: \""+strText+"\") for ";
		long hash = -1;
		
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(0, 2).toCharArray(), '\0', hash);
			// for base 31:3105 
			assertEquals(2911, tmphash, errMsg+"substring \""+strText.substring(0, 2)+"\", lastCharacter = '\\0' and previous hash value = <0> returned wrong new hash value: ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\", current substring \"" + strText.substring(0, 2) + "\", lastCharacter = '\\0' and previous hash code = <0> raised an: " + ex);
		}
		
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(1, 3).toCharArray(), strText.charAt(0), hash);
			// for base 31: 3137
			assertEquals(2941,tmphash, errMsg+"substring \""+strText.substring(1, 3)+"\", lastCharacter = '"+strText.charAt(0)+"' and previous hash value = <"+hash+"> returned wrong new hash value: ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\", current substring \"" + strText.substring(1, 3) + "\", lastCharacter = '" + strText.charAt(0) + "' and previous hash code = <" + hash + "> raised an: " + ex);
		}
		
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(2, 4).toCharArray(), strText.charAt(1), hash);
			// for base 31: 3169
			assertEquals(2971,tmphash, errMsg+"substring \""+strText.substring(2, 4)+"\", lastCharacter = '"+strText.charAt(1)+"' and previous hash value = <"+hash+"> returned wrong new hash value: ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\", current substring \"" + strText.substring(2, 4) + "\", lastCharacter = '" + strText.charAt(1) + "' and previous hash code = <" + hash + "> raised an: " + ex);
		}
		
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(3, 5).toCharArray(), strText.charAt(2), hash);
			// for base 31: 3201
			assertEquals(3001,tmphash, errMsg+"substring \""+strText.substring(3, 5)+"\", lastCharacter = '"+strText.charAt(2)+"' and previous hash value = <"+hash+"> returned wrong new hash value: ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\", current substring \"" + strText.substring(3, 5) + "\", lastCharacter = '" + strText.charAt(2) + "' and previous hash code = <" + hash + "> raised an: " + ex);
		}
		
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(4, 6).toCharArray(), strText.charAt(3), hash);
			// for base 31: 3233
			assertEquals(3031,tmphash, errMsg+"substring \""+strText.substring(4, 6)+"\", lastCharacter = '"+strText.charAt(3)+"' and previous hash value = <"+hash+"> returned wrong new hash value: ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\", current substring \"" + strText.substring(4, 6) + "\", lastCharacter = '" + strText.charAt(3) + "' and previous hash code = <" + hash + "> raised an: " + ex);
		}
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRabinKarpHashOfTextSequencesGeneric() {
		final String strText = "abcdef";
		final String errMsg = "RabinKarp.getRollingHashValue(): Calculating the rolling hash values (input text: \""+strText+"\") for ";
		long hash = -1;
				
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(0, 2).toCharArray(), '\0', hash);
			hash = tmphash;
			
			// 1st rolling hash iteration
			tmphash = RabinKarp.getRollingHashValue(strText.substring(1, 3).toCharArray(), strText.charAt(0), hash);
			long directHash = RabinKarp.getRollingHashValue(strText.substring(1, 3).toCharArray(), '\0', -1);
			
			assertEquals(directHash, tmphash, errMsg+"substring \""+strText.substring(1, 3)+"\" was different when comparing it to direct hash calculation (using lastCharacter = '\\0' and previous hash value = <0>): ");
			hash = tmphash;
			
			
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\" and current substring \"" + strText.substring(1, 3) + "\" raised an exception in the 1st rolling hash iteration: " + ex);
		}
		
		// 2nd rolling hash iteration
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(2, 4).toCharArray(), strText.charAt(1), hash);
			long directHash = RabinKarp.getRollingHashValue(strText.substring(2, 4).toCharArray(), '\0', -1);
			
			assertEquals(directHash, tmphash, errMsg+"substring \""+strText.substring(2, 4)+"\" was different when comparing it to direct hash calculation (using lastCharacter = '\0' and previous hash value = <0>): ");
			hash = tmphash;
			
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\" and current substring \"" + strText.substring(2, 4) + "\" raised an exception in the 2nd rolling hash iteration: " + ex);
		}
		
		// 3rd rolling hash iteration
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(3, 5).toCharArray(), strText.charAt(2), hash);
			long directHash = RabinKarp.getRollingHashValue(strText.substring(3, 5).toCharArray(), '\0', -1);
			
			assertEquals(directHash, tmphash, errMsg+"substring \""+strText.substring(3, 5)+"\" was different when comparing it to direct hash calculation (using lastCharacter = '\0' and previous hash value = <0>): ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\" and current substring \"" + strText.substring(3, 5) + "\" raised an exception in the 3rd rolling hash iteration: " + ex);
		}
		
		// 4th rolling hash iteration
		try {
			long tmphash = RabinKarp.getRollingHashValue(strText.substring(4, 6).toCharArray(), strText.charAt(3), hash);
			long directHash = RabinKarp.getRollingHashValue(strText.substring(4, 6).toCharArray(), '\0', -1);
			
			assertEquals(directHash, tmphash, errMsg+"substring \""+strText.substring(4, 6)+"\" was different when comparing it to direct hash calculation (using lastCharacter = '\0' and previous hash value = <0>): ");
			hash = tmphash;
		}catch(Exception ex) {
			assertNull(ex, "RabinKarp.getRollingHashValue() with input text \"" + strText + "\" and current substring \"" + strText.substring(4, 6) + "\" raised an exception in the 4th rolling hash iteration: " + ex);
		}
	}
	
	
	private String printArray(Integer[] arr) {
		if(arr.length > 0) {
			StringBuilder sb = new StringBuilder();
			sb.append("{");
			
			for(Integer i : arr) {
				sb.append(i+",");
			}
			
			if(sb.length()>0) sb.replace(sb.lastIndexOf(","), sb.lastIndexOf(",")+1, "}");
			return sb.toString();
		} else return "{array empty}";
	}
	
	private String printArrayList(ArrayList<Integer> arr) {
		if(arr.size() > 0) {
			StringBuilder sb = new StringBuilder();
			sb.append("{");
			
			for(Integer i : arr) {
				sb.append(i+",");
			}
			
			if(sb.length()>0) sb.replace(sb.lastIndexOf(","), sb.lastIndexOf(",")+1, "}");
			return sb.toString();
		} else return "{ArrayList empty}";
	}

}