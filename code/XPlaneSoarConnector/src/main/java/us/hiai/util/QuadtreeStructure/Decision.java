package us.hiai.util.QuadtreeStructure;

public class Decision {
    int pointIndex;
    String decision;
    Decision(int pointIndex, String decision) {
        this.pointIndex = pointIndex;
        this.decision = decision;
    }
    public int getPoint() {return pointIndex;}
    public String getDecision() {return decision;}
}
