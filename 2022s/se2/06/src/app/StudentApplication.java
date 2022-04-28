package app;

import inout.Out;
import list.List;
import map.KeyValuePair;
import map.Map;
import map.SimpleMap;
import students.Student;

import java.util.Arrays;
import java.util.Iterator;
import java.util.Objects;
import java.util.Optional;

public class StudentApplication {
    public static void main(String[] args) {
        Out.println("===========================================");
        Out.println("=== JKU KUSSS Backend Super System 3000 ===");
        Out.println("===========================================");

        Map<Integer, Student> students = new SimpleMap<>();
        students.put(16804242, new Student("Herbert Posthofer",
                "Computer Science",
                Student.Degree.PHD));
        students.put(11255667, new Student("Markus Mehringer",
                "History of Memes",
                Student.Degree.PHD));
        students.put(11255668, new Student("Andreas Schörgenhummer",
                "Artificial Intelligence",
                Student.Degree.PHD));
        students.put(11266779, new Student("Gabe Doginger",
                "History of Memes",
                Student.Degree.MSC));
        students.put(11355555, new Student("Itis Wednesday",
                "Contemporary Music",
                Student.Degree.BSC));
        students.put(11410001, new Student("Raffael Moossahner",
                "Artificial Intelligence",
                Student.Degree.PHD));
        students.put(11410002, new Student("Sebastian Hofkloiber",
                "Digital Transformation in Industry 4.0",
                Student.Degree.MSC));
        students.put(11598765, new Student("Lucas Macor",
                "Computer Science",
                Student.Degree.MSC));
        students.put(11898765, new Student("Katrin Korn",
                "Digital Art",
                Student.Degree.BSC));
        students.put(12001447, new Student("Gandalf der Gelbe",
                "Literature",
                Student.Degree.PHD));

        boolean putSuccess = students.putIfAbsent(11234567, () -> new Student("Randy Random", "Game Design", Student.Degree.BSC)); /* TODO: putIfAbsent for student ID 11234567 and Student("Randy Random", "Game Design", Student.Degree.BSC) */
        System.out.printf("1st putIfAbsent successful for student ID 11234567: %b%n", putSuccess);
        putSuccess = students.putIfAbsent(11234567, () -> new Student("Rudolphine Ruby", "Game Design", Student.Degree.BSC)); /* TODO: putIfAbsent for student ID 11234567 and Student("Rudolphine Ruby", "Game Design", Student.Degree.BSC)) */
        System.out.printf("2nd putIfAbsent successful for student ID 11234567: %b%n", putSuccess);

        Map<Integer, Student> phds = students.filter((k, v) -> v.degree == Student.Degree.PHD); /* TODO: Filter all students that have degree == Student.Degree.PHD */
        System.out.println("PHDs:");
        print(phds);

        Map<Integer, Student> computerScientists = students.filter((k, v) -> Objects.equals(v.subject, "Computer Science")); /* TODO: Filter all students that study the subject "Computer Science" */
        System.out.println("Computer Scientists:");
        print(computerScientists);

        Map<Integer, String> initials = students.mapValues((k, v) -> (
                Arrays.stream(v.name.split(" ")).reduce("", (acc, cur) -> acc += cur.charAt(0))
        )); /* TODO: Map all students to their initials. Student "Gabe Doginger" should be mapped to the String "GD", student "Gandalf der Gelbe" to "GdG" */
        System.out.println("Initials:");
        print(initials);
		
		Map<Integer, Integer> startYears = students.mapValues((k, v) -> (k - 10000000) / 100000); /* TODO: Map all students to their study start year (digit 2 and digit 3 of the key). For example, 11598765 started in year 15, 11266779 in year 12. */
        System.out.println("Start years:");
        print(startYears);

        Optional<KeyValuePair<Integer, Student>> studentWithThreePartName = students.find((p) -> p.getValue().name.split(" ").length == 3); /* TODO: Use find() to potentially find a student that has three words in his/her name */
        System.out.println("Entry for student with three-part name: " + studentWithThreePartName.map(x -> x.getValue().toString()).orElse("no such student"));

        Optional<KeyValuePair<Integer, Student>> studentWithFourPartName = students.find((p) -> p.getValue().name.split(" ").length == 4); /* TODO: Use find() to potentially find a student that has four words in his/her name */
        System.out.println("Entry for student with four-part name: " + studentWithFourPartName.map(x -> x.getValue().toString()).orElse("no such student"));

        boolean allStudentIdsStartWithOne = students.all((p) -> Integer.toString(p.getKey()).charAt(0) == '1'); /* TODO: Find out if all student IDs start with the digit 1 */
        System.out.println("All student IDs start with 1: " + allStudentIdsStartWithOne);

        boolean noStudentNameStartsWithX = students.none((p) -> p.getValue().name.charAt(0) == 'X') /* TODO: Find out if no student starts with the letter 'X' */;
        System.out.println("No student name starts with X: " + noStudentNameStartsWithX);

        boolean someStudentStudiesMedicine = students.some((p) -> Objects.equals(p.getValue().subject, "Medicine")); /* TODO: Find out if some student studies the subject "Medicine" */
        System.out.println("Some student(s) studies/study medicine: " + someStudentStudiesMedicine);

        /* TODO: Submit this output as part of you assignment */
    }

    static <K, V> void print(Map<K, V> map) {
        if (map == null) {
            System.out.println("map is null");
            return;
        }
        for (KeyValuePair<K, V> entry : map) {
            System.out.printf("%s\t->\t%s%n", entry.getKey().toString(), entry.getValue().toString());
        }
    }
}