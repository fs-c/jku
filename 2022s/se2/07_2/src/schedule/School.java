package schedule;

import util.Util;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class School {
    private Set<Teacher> teachers = new HashSet<>();
    private Set<SchoolClass> schoolClasses = new HashSet<>();

    public School() {
    }

    public void defineTeachers(Teacher...teachers) {
        this.teachers = Set.of(teachers);
    }

    public void defineClasses(SchoolClass...classes) {
        this.schoolClasses = Set.of(classes);
    }

    // Queries

    public List<Lesson> getLessons(Predicate<? super Lesson> filter) {
        return getLessons(filter, null);
    }

    public List<Lesson> getLessons(Predicate<? super Lesson> filter, Comparator<Lesson> sorting) {
        final var list = Util.filter(
                schoolClasses.stream().flatMap((c) -> c.getLessons().stream())
                        .collect(Collectors.toList())
                , filter
        );

        list.sort(sorting == null ? Lesson::compareTo : sorting);

        return list;
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
        return (l) -> l.teacher().equals(teacher);
    }

    public final static Comparator<Lesson> sortedByClass = Comparator.comparing((Lesson l) -> l.schoolClass().getId());

    public final static Comparator<Lesson> sortedByTeacher = Comparator.comparing((Lesson l) -> l.teacher().getName());

    public final static Comparator<Lesson> sortedBySubject = Comparator.comparing(Lesson::subject);
}