package edu.fit.hiai.lvca.translator.soar;

public class UtilityForVisitors {

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
}
