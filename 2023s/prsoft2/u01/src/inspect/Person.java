package inspect;

import java.util.ArrayList;
import java.util.List;

public class Person {
    public String name;
    private int age;
    public Person partner;

    @InspectionBoundary
    public List<Person> children;

    public Person(String name, int age, Person partner) {
        this.name = name;
        this.partner = partner;
        this.age = age;
        this.children = new ArrayList<Person>();
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getAge() {
        return age;
    }

    public void setAge(int age) {
        this.age = age;
    }

    public Person getPartner() {
        return partner;
    }

    public void setPartner(Person partner) {
        this.partner = partner;
    }

    public List<Person> getChildren() {
        return children;
    }

    public void setChildren(List<Person> children) {
        this.children = children;
    }

    public void addChild(Person child) {
        this.children.add(child);
    }

    @Override
    public String toString() {
        return name + ": " + age + " years";
    }

    public void divorce() {
        if (partner != null) {
            partner.setPartner(null);
        }
        partner = null;
    }
}
