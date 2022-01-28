public class Person {
    private /*@ spec_public @*/ String name;
    private /*@ spec_public @*/ int weight;

    /*@ public invariant !name.equals("") && weight >= 0; @*/

    /*@ ensures \result != null;
    @*/
    public String getString() {
        return "Person(\"" + name + "\","
                + weight + ")";
    }

    //@ ensures \result == weight;
    public int getWeight() {
        return weight;
    }

    /*@ requires kgs >= 0;
    @ requires weight + kgs >= 0;
    @ requires (weight + kgs) < Integer.MAX_VALUE;
    @ ensures weight == \old(weight + kgs);
    @*/
    public void addKgs(int kgs) {
        if (kgs >= 0) {
            weight += kgs;
        } else {
            throw new IllegalArgumentException();
        }
    }

    /*@ requires n != null && !n.equals("");
    @ ensures n.equals(name) && weight == 0; @*/
    public Person(String n) {
        name = n; weight = 0;
    }
}
