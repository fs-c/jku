package app;

import inout.In;
import inout.Out;
import map.KeyValuePair;
import map.SimpleMap;
import map.SortedMap;
import students.Student;

import java.util.Iterator;

public class StudentApplication {
    public static void main(String[] args) {
        Out.println("===========================================");
        Out.println("=== JKU KUSSS Backend Super System 3000 ===");
        Out.println("===========================================");

        SortedMap<Integer, Student> list = new SortedMap<>();

        String input;
        do {
            Out.println("Which operation do you want to perform?");
            Out.println("1 - Add student");
            Out.println("2 - Check if student with given student ID exists");
            Out.println("3 - Print student based on student ID");
            Out.println("4 - Print student count");
            Out.println("5 - Remove student");
            Out.println("6 - List all student IDs");
            Out.println("7 - List all student names");
            Out.println("8 - List all student IDs + student names");
            Out.println("X - Exit application");
            input = In.readLine();

            int studentId;
            switch (input) {
                case "1":
                    Out.println("Enter student ID");
                    studentId = In.readInt();
                    // To remove \n
                    In.readLine();
                    Out.println("Enter student name");
                    String studentName = In.readLine();
                    list.put(studentId, new Student(studentName));
                    break;
                case "2":
                    Out.println("Enter student ID");
                    studentId = In.readInt();
                    // To remove \n
                    In.readLine();
                    // check if student is contained in map and print
                    if (list.contains(studentId)) {
                        Out.println("Student exists");
                    } else {
                        Out.println("Student doesn't exist");
                    }
                    break;
                case "3":
                    Out.println("Enter student ID");
                    studentId = In.readInt();
                    // To remove \n
                    In.readLine();
                    // get student from map and print
                    Out.println(list.get(studentId).name);
                    break;
                case "4":
                    // print amount of students
                    Out.println(list.size());
                    break;
                case "5":
                    Out.println("Enter student ID");
                    studentId = In.readInt();
                    // To remove \n
                    In.readLine();
                    // remove students and print whether remove was successful
                    if (list.remove(studentId)) {
                        Out.println("Removed student");
                    } else {
                        Out.println("Couldn't remove student");
                    }
                    break;
                case "6":
                    // use keyIterator to print
                    for (Iterator<Integer> it = list.keyIterator(); it.hasNext(); ) {
                        int key = it.next();

                        Out.println(key);
                    }
                    break;
                case "7":
                    // use valueIterator to print
                    for (Iterator<Student> it = list.valueIterator(); it.hasNext(); ) {
                        String value = it.next().name;

                        Out.println(value);
                    }
                    break;
                case "8":
                    for (KeyValuePair<Integer, Student> node : list) {
                        System.out.format("%d : %s\n", node.getKey(), node.getValue().name);
                    }
                    break;
                case "X":
                    return;
                default:
                    Out.println("Unknown operation");
            }
        } while (!input.equals("X"));
    }
}
