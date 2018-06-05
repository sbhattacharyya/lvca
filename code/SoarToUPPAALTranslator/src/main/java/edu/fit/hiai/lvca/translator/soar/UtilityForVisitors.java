package edu.fit.hiai.lvca.translator.soar;

public class UtilityForVisitors {

    public static String unaryOrBinaryToString(char prefChar) {
        String prefString = null;
        switch (prefChar) {
            case '>':
                prefString = "isBetterTo";
                break;
            case '<':
                prefString = "isWorseTo";
                break;
            case '=':
                prefString = "isUnaryOrBinaryIndifferentTo";
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
            case '>': isWhat = "isBest";
                      break;
            case '<': isWhat = "isWorst";
                      break;
            case '=': isWhat = "isUnaryIndifferent";
                      break;
            default: break;
        }
        return isWhat;
    }
}
