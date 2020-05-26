package edu.fit.hiai.lvca.translator.soar;

/**
 * Created by Daniel Griessler Summer 2018
 * Used by SymbolVisitor and UppaalSemanticVisitor. Contains shared methods that both need
 */

public class UtilityForVisitors {

    /**
     * Gives the String representation of the character preference provided
     * @param prefChar Preference
     * @param isUnary Distinguish if the preference is unary or binary
     * @return String that the preference represents
     */
    public static String unaryOrBinaryToString(char prefChar, boolean isUnary) {
        String prefString = null;
        String betterString;
        String worseString;
        String unaryOrBinaryIndifferentString;
        if (isUnary) {
            betterString = "isBest";
            worseString = "isWorst";
            unaryOrBinaryIndifferentString = "isUnaryIndifferent";
        } else {
            betterString = "isBetterTo";
            worseString = "isWorseTo";
            unaryOrBinaryIndifferentString = "isUnaryOrBinaryIndifferentTo";
        }
        switch (prefChar) {
            case '>':
                prefString = betterString;
                break;
            case '<':
                prefString = worseString;
                break;
            case '=':
                prefString = unaryOrBinaryIndifferentString;
                break;
            default:
                break;
        }
        return prefString;
    }

    /**
     * Gives the String representation of the character preference provided
     * @param prefChar Preference
     * @return String that the preference represents
     */
    public static String unaryToString(char prefChar) {
        String isWhat = null;
        switch(prefChar) {
            case '+': isWhat = "isAcceptable";
                      break;
            case '-': isWhat = "isRejected";
                      break;
            case '!': isWhat = "isRequired";
                      break;
            case '~': isWhat = "isProhibited";
                      break;
            default: break;
        }
        return isWhat;
    }

    /**
     * Gives the String representation of the String relation provided
     * @param relation Soar relation
     * @return String representation of the provided relation
     */
    public static String relationToText(String relation) {
        String relationText;
        switch(relation) {
            case "<>": relationText = "isNotEqualTo";
                break;
            case "<": relationText = "isLessThan";
                break;
            case ">": relationText = "isGreaterThan";
                break;
            case "<=": relationText = "isLessThanOrEqualTo";
                break;
            case ">=": relationText = "isGreaterThanOrEqualTo";
                break;
            case "<=>": relationText = "isSameTypeAs";
                break;
            default:
                relationText = null;
                break;
        }
        return relationText;
    }
}
