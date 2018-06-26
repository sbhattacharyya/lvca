package edu.fit.hiai.lvca.translator.soar;

public class UppaalAttributeValueTriad {
    private String name;
    private int numValues;
    private int attributeIndex;
    private int operatorIndex;

    UppaalAttributeValueTriad() {}

    UppaalAttributeValueTriad(String _name, int _operatorIndex) {
        name = _name;
        operatorIndex = _operatorIndex;
    }

    UppaalAttributeValueTriad(String _name, int _numValues, int _attributeIndex, int _operatorIndex) {
        this(_name, _operatorIndex);
        numValues = _numValues;
        attributeIndex = _attributeIndex;
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

    public int getAttributeIndex() {
        return attributeIndex;
    }

    public void setAttributeIndex(int attributeIndex) {
        this.attributeIndex = attributeIndex;
    }

    public int getOperatorIndex() {
        return operatorIndex;
    }

    public void setOperatorIndex(int operatorIndex) {
        this.operatorIndex = operatorIndex;
    }


}
