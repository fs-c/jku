package schedule;

import java.util.Objects;

public record Lesson(
        Unit unit, Subject subject, SchoolClass schoolClass, Teacher teacher
) implements Comparable<Lesson> {
    @Override
    public int compareTo(Lesson o) {
        final int unitComp = this.unit().compareTo(o.unit());

        if (unitComp != 0) {
            return unitComp;
        }

        final int nameComp = this.schoolClass().getId().compareTo(o.schoolClass().getId());

        if (nameComp != 0) {
            return unitComp;
        }

        return this.subject().compareTo(o.subject());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Lesson lesson = (Lesson) o;
        return unit == lesson.unit && subject == lesson.subject && Objects.equals(schoolClass, lesson.schoolClass);
    }

    @Override
    public int hashCode() {
        return Objects.hash(unit, subject, schoolClass);
    }
}