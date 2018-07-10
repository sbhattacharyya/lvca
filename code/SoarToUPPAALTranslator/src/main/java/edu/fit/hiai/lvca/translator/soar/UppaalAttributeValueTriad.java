package edu.fit.hiai.lvca.translator.soar;

public class UppaalAttributeValueTriad {
    private String name;
    private int numValues;
    private String attribute;
    private String operator;

    UppaalAttributeValueTriad() {}

    UppaalAttributeValueTriad(String _name, String _operator) {
        name = _name;
        operator = _operator;
    }

    UppaalAttributeValueTriad(String _name, int _numValues, String _attribute, String _operator) {
        this(_name, _operator);
        numValues = _numValues;
        attribute = _attribute;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getNumValues() {
        return numValues;
    }

    public void setNumValues(int numValues) {
        this.numValues = numValues;
    }

    public String getAttributeIndex() {
        return attribute;
    }

    public void setAttributeIndex(String attribute) {
        this.attribute = attribute;
    }

    public String getOperatorIndex() {
        return operator;
    }


}
