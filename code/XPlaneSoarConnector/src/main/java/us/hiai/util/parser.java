package us.hiai.util;
import java.math.RoundingMode;
import java.text.DecimalFormat;
import java.util.ArrayList;

/**
 * Daniel Griessler Sprint 2019
 * Created to parse html input from SkyVector's navlog in order to directly import into GPS_Intersection instructions
 * To add your own: modify input variable in main to include the one line of html from navlog that includes all of the GPS coordinates
 * Note: input can be split into multiple string arrays if java complains that the input constant string is too long.  Make sure the first GPS coordinate
 * on each new string array of input starts with :\"> if you do split it
 */
public class parser {

    public static ArrayList<String> extractCoords(String[][] inputs) {
        int size = 0;
        for (int i = 0; i < inputs.length; i++) {
            size += inputs[i].length;
        }
        ArrayList<String> returnList = new ArrayList<>(size);
        for (int i = 0; i < inputs.length; i++) {
            for (int j = 0; j < inputs[i].length; j++) {
                if (inputs[i][j].length() > 1) {
                    char direction = inputs[i][j].charAt(1);
                    if (inputs[i][j].charAt(2) == ' ' && (direction == 'N' || direction == 'S' || direction == 'W' || direction == 'E')) {
                        int index = 2;
                        while (inputs[i][j].charAt(index) != '<') {
                            index++;
                        }
                        returnList.add(inputs[i][j].substring(1, index));
                    }
                }
            }
        }
        return returnList;
    }

    public static void main(String[] args) {
        //.split(";\\\"");
        String[] input = ";\">N    32°06.33'</div><div style=\"left: 175px; top: 430.567px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(1.07658e-16);\">W 096°43.36'</div><div style=\"left: 175px; top: 462.233px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(2.07761e-16);\">N    32°05.59'</div><div style=\"left: 175px; top: 470.567px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(1.07658e-16);\">W 096°44.02'</div><div style=\"left: 175px; top: 502.233px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(2.07761e-16);\">N    32°04.68'</div><div style=\"left: 175px; top: 510.567px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(1.07658e-16);\">W 096°43.07'</div><div style=\"left: 175px; top: 542.233px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(2.07761e-16);\">N    32°05.45'</div><div style=\"left: 175px; top: 550.567px; font-size: 8.33333px; font-family: sans-serif; transform: scaleX(1.07658e-16);\">W 096°41.89'</div>".split(";\\\"");
        ArrayList<String> tester = extractCoords(new String[][]{input});

        DecimalFormat df = new DecimalFormat("#.#####");
        df.setRoundingMode(RoundingMode.CEILING);
        String[] output = new String[tester.size() / 2];
        int outputIndex = 0;
        for (int i = 0; i < tester.size(); i++) {
            int index = 0;
            while (!Character.isDigit(tester.get(i).charAt(index))) {
                index++;
            }
            int degreeIndex = index;
            while (tester.get(i).charAt(degreeIndex) != '°') {
                degreeIndex++;
            }
            double top = Double.parseDouble(tester.get(i).substring(index, degreeIndex));
            double bottom = Double.parseDouble(tester.get(i).substring(degreeIndex + 1, tester.get(i).length() - 1));
            double total = top + bottom / 60;
            if (tester.get(i).charAt(0) == 'W' || tester.get(i).charAt(0) == 'S') {
                total *= -1;
            }
            if (i % 2 == 0) {
                output[outputIndex] = "polygon_lat_long_pairs.add(\"" + df.format(total);
            } else {
                output[outputIndex] = output[outputIndex] + ", " + df.format(total) + "\");";
                outputIndex++;
            }
        }

        for (int i = 0; i < output.length; i++) {
            System.out.println(output[i]);
        }
    }
}
