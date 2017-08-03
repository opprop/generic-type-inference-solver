package util;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Map;

import javax.lang.model.element.AnnotationMirror;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;

import checkers.inference.InferenceMain;
import util.StatisticPrinter.StatisticKey;

public class PrintUtils {

    /**
     * print result from sat solver for testing.
     *
     * @param result
     */
    public static void printResult(Map<Integer, AnnotationMirror> result) {

        final int maxLength = String.valueOf(InferenceMain.getInstance().getSlotManager().getNumberOfSlots()).length();
        StringBuilder printResult = new StringBuilder();
        System.out.println("/***********************results****************************/");
        for (Integer j : result.keySet()) {
            printResult.append("SlotID: ");
            printResult.append(String.valueOf(j));
            for (int i = 0; i < maxLength + 2 - String.valueOf(j).length(); i++) {
                printResult.append(" ");
            }
            printResult.append("Annotation: ");
            printResult.append(result.get(j).toString());
            printResult.append("\n");
        }
        System.out.println(printResult.toString());
        System.out.flush();
        System.out.println("/**********************************************************/");
    }

    public static void printStatistic(Map<StatisticKey, Long> statistic) {
        System.out.println("/***********************statistic start*************************/");
        for (StatisticKey j : statistic.keySet()) {
            if (statistic.get(j) != (long) 0) {
                System.out.println(j.toString().toLowerCase() + ": " + statistic.get(j));
            }
        }
        System.out.flush();
        System.out.println("/**********************statistic end****************************/");
    }

    public static void writeStatistic(Map<StatisticKey, Long> statistic) {
    	JsonObject obj = new JsonObject();
    	Gson gson = new GsonBuilder().setPrettyPrinting().create();
        String writePath = new File(new File("").getAbsolutePath()).toString() + File.separator + "solver-statistic.json";
        for (StatisticKey j : statistic.keySet()) {
            if (statistic.get(j) != (long) 0) {
                obj.addProperty(j.toString().toLowerCase(), statistic.get(j));
            }
        }
        try {
            PrintWriter pw = new PrintWriter(writePath);
            pw.write(gson.toJson(obj));
            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    
    public static void writeResult(Map<Integer, AnnotationMirror> result) {
        StringBuilder printResult = new StringBuilder();
        final int maxLength = String.valueOf(InferenceMain.getInstance().getSlotManager().getNumberOfSlots())
                .length();

        for (Integer j : result.keySet()) {
            printResult.append("SlotID: ");
            printResult.append(String.valueOf(j));
            for (int i = 0; i < maxLength + 2 - String.valueOf(j).length(); i++) {
                printResult.append(" ");
            }
            printResult.append("Annotation: ");
            printResult.append(result.get(j).toString());
            printResult.append("\n");
        }

        File CNFData = new File(new File("").getAbsolutePath());
        String writePath = CNFData.getAbsolutePath() + "/result" + ".txt";
        File f = new File(writePath);
        PrintWriter pw;
        try {
            pw = new PrintWriter(f);
            pw.write(printResult.toString());
            pw.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
        printResult = null;
    }

}
