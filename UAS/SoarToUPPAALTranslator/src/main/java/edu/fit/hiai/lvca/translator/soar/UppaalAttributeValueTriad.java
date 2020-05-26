package edu.fit.hiai.lvca.translator.soar;

/**
 * Created by Daniel Griessler Summer 2018
 * Data structure to store the information needed by the templates in Uppaal for the AV Templates
 */

public class UppaalAttributeValueTriad {
    private String name;
    private int numValues;
    private String attribute;
    private String operator;

    /**
     * Creates a new UppaalAttributeValueTriad with the provided name and operator
     * @param _name Name that will be used by the AV template. Comes from its path in Soar
     * @param _operator Which identifier the attribute is attached to
     */
    UppaalAttributeValueTriad(String _name, String _operator) {
        name = _name;
        operator = _operator;
    }

    /**
     * Creates a new UppaalAttributeValueTriad with the provided name, number of values, attribute, and operator
     * @param _name Name that will be used by the AV template. Comes from its path in Soar
     * @param _numValues How many values are associated with the given attribute
     * @param _attribute Which attribute the _operator has
     * @param _operator Which identifier the attribute is attached to
     */
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
