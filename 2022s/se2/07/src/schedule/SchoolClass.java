package schedule;

import util.Util;

import java.util.*;

public class SchoolClass {

    private final String id;
    private final Set<Subject> subjects;

    private final Map<Subject, Teacher> subjectTeacherMap = new TreeMap<>();
    private final SortedMap<Unit, Lesson> lessons = new TreeMap<>();

    public SchoolClass(String id, Subject...subjects) {
        this.id = id;
        this.subjects = Set.of(subjects);
    }

    public String getId() {
        return id;
    }

    public Collection<Lesson> getLessons() {
        return lessons.values();
    }

    public void defTeacher(Subject subject, Teacher teacher) {
        if (!subjects.contains(subject)) {
            throw new IllegalArgumentException("invalid subject");
        }

        subjectTeacherMap.put(subject, teacher);
    }

    public void defineLesson(Unit unit, Subject subject) {
        if (!subjects.contains(subject)) {
            throw new IllegalArgumentException("invalid subject");
        }

        if (lessons.get(unit) != null) {
            throw new IllegalArgumentException("unit is already booked");
        }

        Teacher teacher = subjectTeacherMap.get(subject);

        if (teacher == null) {
            throw new IllegalArgumentException("no teacher assigned to subject");
        }

        if (Util.find(teacher.getLessons(), (l) -> l.unit().equals(unit)).isPresent()) {
            throw new IllegalArgumentException("teacher is already booked for this unit");
        }

        lessons.put(unit, new Lesson(unit, subject, this, teacher));
    }

    @Override
    public String toString() {
        return id;
    }

    // We are again assuming that id is unique for equals/hashCode

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SchoolClass that = (SchoolClass) o;
        return Objects.equals(id, that.id);
    }

    @Override
    public int hashCode() {
        return Objects.hash(id);
    }
}