package edu.fit.hiai.lvca.translator.soar;

public class Attribute_Value_Wrapper {

    final private int numValues;
    final private int attributeIndex;
    final private int operatorId;

    Attribute_Value_Wrapper(int _numValues, int _attributeIndex, int _operatorId) {
        numValues = _numValues;
        attributeIndex = _attributeIndex;
        operatorId = _operatorId;
    }

    public int getNumValues() {
        return numValues;
    }

    public int getAttributeIndex() {
        return attributeIndex;
    }

    public int getOperatorId() {
        return operatorId;
    }
}
