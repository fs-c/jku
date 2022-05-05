package schedule;

import java.util.*;

public class Teacher {
    private final String name;
    private final Set<Subject> subjects;

    private Set<Lesson> lessons = new TreeSet<>();

    public Teacher(String name, Subject... subjects) {
        this.name = name;
        this.subjects = Set.of(subjects);
    }

    public void assignLesson(Lesson lesson) {
        lessons.add(lesson);
    }

    public Set<Lesson> getLessons() {
        return Collections.unmodifiableSet(lessons);
    }

    // We are assuming that the name is unique, so we only care about the name
    // when checking equality and getting the hashcode.

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Teacher teacher = (Teacher) o;
        return Objects.equals(name, teacher.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }
}
