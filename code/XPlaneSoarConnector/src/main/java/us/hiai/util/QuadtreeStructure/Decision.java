package us.hiai.util.QuadtreeStructure;

/**
 * Stores previous decisions and their values
 */
public class Decision {
    String decision;
    Integer value;
    Decision(String decision, Integer value) {
        this.decision = decision;
        this.value = value;
    }
    public String getDecision() {return decision;}
    public Integer getValue() {return value;}
}
