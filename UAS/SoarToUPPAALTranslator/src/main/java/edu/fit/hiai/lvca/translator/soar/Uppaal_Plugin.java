package edu.fit.hiai.lvca.translator.soar;

import java.util.*;

/**
 * Formulates queries for Uppaal user.  Look into making more robust or possibly adding plugin for Uppaal
 */
public class Uppaal_Plugin {
    private Map<String, Integer> AVToNumValues = new HashMap<>();
    private String stringedAVs;

    Uppaal_Plugin(LinkedList<UppaalAttributeValueTriad> AVCollection) {
        StringBuilder allAVNames = new StringBuilder();
        for (UppaalAttributeValueTriad nextAV : AVCollection) {
            AVToNumValues.put(nextAV.getName(), nextAV.getNumValues());
            if (allAVNames.length() > 0) {
                allAVNames.append("\n");
            }
            allAVNames.append(nextAV.getName());
        }
        stringedAVs = allAVNames.toString();
        run();
    }

    public int getNumValues(String AV) {
        Integer numValues = -1;
        for (String nextAV : AVToNumValues.keySet()) {
            if (nextAV.equals(AV)) {
                numValues = AVToNumValues.get(nextAV);
            }
        }
        return numValues;
    }

    public static void getQuery(LinkedList<String> queries, LinkedList<String> revisedQueryPieces, Map<String, Integer> indexToCurrentIterations, Map<String, Integer> indexToMaxIterations, Map<Character, String> charToAVs) {
        StringBuilder output = new StringBuilder();
        if (output.length() > 0) {
            output.append(" && ");
        }
        for (String nextPiece : revisedQueryPieces) {
            output.append(nextPiece);
            Integer nextIteration = indexToCurrentIterations.get(nextPiece);
            if (nextIteration != null) {
                output.append(".values[").append(nextIteration).append("]");
            }
        }
        output.append(" || ");
        boolean first = true;
        for (String nextAV : charToAVs.values()) {
            if (!first) {
                output.append(" || ");
            }
            output.append(nextAV).append(".valuesIndex < ").append(indexToCurrentIterations.get(nextAV) + 1);
            first = false;
        }
        queries.add(output.toString());
    }

    public static void generateQueries(Map<String, Integer> indexToMaxIterations, Map<String, Integer> indexToCurrentIterations, LinkedList<String> revisedQueryPieces, int indexOfIterations, Map<Character, String> charToAVs, LinkedList<String> queries) {
        if (indexOfIterations == indexToMaxIterations.size() - 1) {
            String AV;
            do {
                getQuery(queries, revisedQueryPieces, indexToCurrentIterations, indexToMaxIterations, charToAVs);
                AV = charToAVs.get((char)('A' + indexOfIterations));
                indexToCurrentIterations.put(AV, indexToCurrentIterations.get(AV) + 1);
                if (indexToCurrentIterations.get(AV) == indexToMaxIterations.get(AV)) {
                    indexToCurrentIterations.put(AV, 0);
                }
            } while(indexToCurrentIterations.get(AV) != 0);
        } else {
            String AV;
            do {
                generateQueries(indexToMaxIterations, indexToCurrentIterations, revisedQueryPieces, indexOfIterations + 1, charToAVs, queries);
                AV = charToAVs.get((char)('A' + indexOfIterations));
                indexToCurrentIterations.put(AV, indexToCurrentIterations.get(AV) + 1);
                if (indexToCurrentIterations.get(AV) == indexToMaxIterations.get(AV)) {
                    indexToCurrentIterations.put(AV, 0);
                }
            } while(indexToCurrentIterations.get(AV) != 0);
        }
    }

    public LinkedList<String> getOutput(String query, Map<Character, String> charToAVs) {
        LinkedList<String> revisedQueryPieces = getRevisiedQuery(query, charToAVs);
        LinkedList<String> invalidAVs = new LinkedList<>();

        Map<String, Integer> indexToCurrentIterations = new HashMap<>();
        Map<String, Integer> indexToMaxIterations = new HashMap<>();
        for (String nextAV : charToAVs.values()) {
            indexToCurrentIterations.put(nextAV, 0);
            int numValues = getNumValues(nextAV);
            if (numValues == -1) {
                invalidAVs.add(nextAV);
            }
            indexToMaxIterations.put(nextAV, numValues);
        }
        if (invalidAVs.size() == 0) {
            LinkedList<String> queries = new LinkedList<>();
            generateQueries(indexToMaxIterations, indexToCurrentIterations, revisedQueryPieces, 0, charToAVs, queries);
            return queries;
        } else {
            invalidAVs.addFirst("INVALID");
            return invalidAVs;
        }

    }

    public static void printQueries(LinkedList<String> queries) {
        for (String nextQuery : queries) {
            System.out.println(nextQuery);
        }
    }

//2,AV_state_right_bank_2_missionaries,AV_state_right_bank_2_cannibals,A > 0 --> B <= A
    public static LinkedList<String> getRevisiedQuery(String query, Map<Character, String> charToAVs) {
        LinkedList<String> revisedQueryPieces = new LinkedList<>();
        StringBuilder piece = new StringBuilder();
        for (int i = 0; i < query.length(); i++) {
            if (Character.isAlphabetic(query.charAt(i))) {
                if (piece.length() > 0) {
                    revisedQueryPieces.add(piece.toString());
                    piece.replace(0, piece.length(), "");
                }
                revisedQueryPieces.add(charToAVs.get(query.charAt(i)));
            } else {
                piece.append(query.charAt(i));
            }
        }
        if (piece.length() > 0) {
            revisedQueryPieces.add(piece.toString());
        }
        return revisedQueryPieces;
    }

    private static String instructions = "This is an Uppaal Plugin for making queries using this translator.\n" +
            "The translator stores Soar memory inside AV templates.\n" +
            "The values are stored in arrays so any query you want to make has to be valid for all values in the array.\n" +
            "To run this plugin, provide the number of AV templates that are involved in your query followed by the AV templates.\n" +
            "The first AV you provide will be assigned to the character A, the second to B and so on.\n" +
            "Next, provide your Query as you would want to place it in Uppaal, but use the corresponding letters instead of AV templates.\n" +
            "Example input: 2, AV_state_num, AV_state_max_num, A > 0 --> A <= B\n" +
            "For help (don't add the quotes): \"AV?\", \"Query?\", \"Instructions?\"\n" +
            "To exit (don't add the quotes): \"exit\"";

    public void run() {
        Scanner in = new Scanner(System.in);
        System.out.println(instructions);
        System.out.println("Input \"Number of AVs, AV*, Query\"");
        input:
        while(in.hasNextLine()) {
            String nextLine = in.nextLine();
            switch (nextLine) {
                case "exit": break input;
                case "Instructions?": System.out.println(instructions);
                                      break;
                case "AV?": System.out.println(stringedAVs);
                            break;
                case "Query?": System.out.println("Please refer to Uppaal to the Help -> Language Reference -> Requirement Specification -> Semantics for possible queries.");
                               break;
                default:
                    String[] avAndQuery = nextLine.split(",");
                    Map<Character, String> charToAVs = new HashMap<>();
                    Character start = 'A';
                    for (int i = 1; i < avAndQuery.length - 1; i++) {
                        charToAVs.put(start++, avAndQuery[i]);
                    }
                    LinkedList<String> output = getOutput(avAndQuery[avAndQuery.length - 1], charToAVs);
                    if (output.peek().equals("INVALID")) {
                        System.out.println("INVALID ENTRY");
                        System.out.println("The following AVs are not valid:");
                        output.removeFirst();
                    }
                    printQueries(output);
                    break;
            }
        }
        in.close();
    }
}
