package schedule.app;

import java.util.List;

import inout.Out;

import schedule.Lesson;
import schedule.School;
import schedule.SchoolClass;
import schedule.Teacher;

import static schedule.Day.*;
import static schedule.School.*;
import static schedule.Subject.*;
import static schedule.Unit.*;

public class SchoolApp {

	public static void main(String[] args) {

        School school = new School();

		Teacher maier = new Teacher("Maier", German, English);
		Teacher auer = new Teacher("Auer", Bio, Geo);
		Teacher reisner = new Teacher("Reisner", Math, Chemistry);
		Teacher ebner = new Teacher("Ebner", Math, Physics);
		Teacher fischer = new Teacher("Fischer", Sports, History);
        school.defineTeachers(maier, auer, reisner, ebner, fischer);

        SchoolClass a1 = new SchoolClass("1A", English, German, Math, Physics, Sports);
        SchoolClass a2 = new SchoolClass("2A", English, German, Math, Chemistry, Sports);
        school.defineClasses(a1, a2);

        a1.defTeacher(English, fischer);
        a1.defTeacher(German, maier);
        a1.defTeacher(Math, ebner);
        a1.defTeacher(Physics, ebner);
        a1.defTeacher(Sports, fischer);

        a2.defTeacher(English, fischer);
        a2.defTeacher(German, maier);
        a2.defTeacher(Math, reisner);
        a2.defTeacher(Chemistry, reisner);
        a2.defTeacher(Sports, fischer);

        a1.defineLesson(Mon1, Math);
        a1.defineLesson(Mon2, Math);
        a1.defineLesson(Mon3, German);
        a1.defineLesson(Mon4, English);

        a1.defineLesson(Tue1, English);
        a1.defineLesson(Tue2, Physics);
        a1.defineLesson(Tue3, Physics);
        a1.defineLesson(Tue4, Sports);
        a1.defineLesson(Tue5, Sports);

        a2.defineLesson(Mon1, German);
        a2.defineLesson(Mon2, English);
        a2.defineLesson(Mon3, Math);
        a2.defineLesson(Mon4, Math);

        a2.defineLesson(Tue1, Math);
        a2.defineLesson(Tue2, Sports);
        a2.defineLesson(Tue3, Sports);
        a2.defineLesson(Tue4, Chemistry);
        a2.defineLesson(Tue5, Chemistry);

        List<Lesson> a1Mon = school.getLessons(forClass(a1).and(onDay(MON)));
        Out.println("\nUnterrichtstunden 1A, Montag");
        for (Lesson lesson: a1Mon) {
            Out.println(lesson);
        }

        List<Lesson> a2MonOrTue = school.getLessons(forClass(a2).and(onDay(MON).or(onDay(TUE))));
        Out.println("\nUnterrichtstunden 2A, Montag und Dienstag");
        for (Lesson lesson: a2MonOrTue) {
            Out.println(lesson);
        }

        List<Lesson> a1LessonsSubjects = school.getLessons(forClass(a1), sortedBySubject);
        Out.println("\n1A, Unterrichtsstunden für Gegenstände");
        for (Lesson lesson: a1LessonsSubjects) {
            Out.println(lesson);
        }

        // TODO: 3 more queries
    }

}
