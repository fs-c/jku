package schedule;

import util.Util;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class School {
    private Set<Teacher> teachers = new HashSet<>();
    private Set<SchoolClass> schoolClasses = new HashSet<>();

    public School() {
        // TODO
    }

    public void defineTeachers(Teacher...teachers) {
        // TODO

        this.teachers = Set.of(teachers);
    }

    public void defineClasses(SchoolClass...classes) {
        // TODO

        this.schoolClasses = Set.of(classes);
    }

    // Queries

    public List<Lesson> getLessons(Predicate<? super Lesson> filter) {
        return getLessons(filter, null);
    }

    public List<Lesson> getLessons(Predicate<? super Lesson> filter, Comparator<Lesson> sorting) {
        return Util.filter(
                schoolClasses.stream().flatMap((c) -> c.getLessons().stream())
                        .sorted(sorting).collect(Collectors.toList())
                , filter
        );
    }

    public static Predicate<Lesson> forClass(SchoolClass schoolClass) {
        return (l) -> l.schoolClass().equals(schoolClass);
    }

    public static Predicate<Lesson> onDay(Day day) {
        return (l) -> l.unit().getDay().equals(day);
    }

    public static Predicate<Lesson> forSubject(Subject subject) {
        return (l) -> l.subject().equals(subject);
    }

    public static Predicate<Lesson> withTeacher(Teacher teacher) {
        return (l) -> ;
    }

    public final static Comparator<Lesson> sortedByClass = null; // TODO

    public final static Comparator<Lesson> sortedByTeacher = null; // TODO

    public final static Comparator<Lesson> sortedBySubject = null; // TODO
}
