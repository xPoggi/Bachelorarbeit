package Bachelorarbeit;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.*;

import java.io.*;
import java.util.*;

/**
 * Created by Poggi on 19.04.2017.
 * Planning-program for FH-Luebeck
 */

public class Main{
    public static void main(String[] args) throws Z3Exception, IOException, TestFailedException, addFailExeption{
        //Start des Programms speichern, um die Laufzeit zu berechnen.
        long start = new Date().getTime();
        //Read Data.
        String testdataNoSplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\nosplit\\";
        String testdataTwoSplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\twosplit\\";
        String testdataTreeSplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\treesplit\\";
        String testDataTwoTreeSplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\two_treesplit\\";
        String dataPath = testDataTwoTreeSplit;

        List<Klausur> klausuren = readFilesKlausur(dataPath + args[0]);
        List<Raum> raeume = readFilesRaume(dataPath + args[2]);
        List<Termin> termine = readFilesTermin(dataPath + args[1], raeume);

        //Z3 Context erstellen um SAT-Solver Nutzen zu können.
        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("Model", "true");
        Context ctx = new Context(cfg);
        //Z3 Ausgabe umstellen.(nicht mehr SMT sondern einfache Variablen mit deren boolischen Werten)
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL);

        System.out.println("Versuche " + klausuren.size() + " Klausuren, " + raeume.size() + " Räume und " + termine.size() + " Termine zu planen!");

        //Einen möglichen Plan suchen.
        Model plan = KlausurPlanning(klausuren, termine, raeume, ctx);
        //Falls ein Plan existiert, diesen von Z3 zu einem Plan übersetzen.
        mkPlan(plan, klausuren, termine, raeume);
        //Die Laufzeit des Programmes berechnen.
        long runningTime = new Date().getTime() - start;
        System.out.println("Das Planen hat: " + (int)(runningTime/1000/60) + " Sekunden gedauert!");
    }

    private static Model KlausurPlanning (List<Klausur> allKlausur, List<Termin> allTermin, List<Raum> allRaeume, Context ctx)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        BoolExpr[][][] all_literals = new BoolExpr[allKlausur.size()][allTermin.size()][allRaeume.size()];
        Model retmodel;
        //---------------Declaration end---------------------------

        //---------------Creating or-literals----------------------
        for(int k = 0; k < allKlausur.size(); k++){
            for(int t = 0; t < allTermin.size(); t++){
                for(int r = 0; r < allRaeume.size(); r++){
                    all_literals[k][t][r] = ctx.mkBoolConst(allKlausur.get(k).getKlausurnummer()+"_"+allTermin.get(t).getName()+"_"+allRaeume.get(r).getName());
                }
            }
        }
        Raum r1 = null;
        Raum r2 = null;
        Klausur tempKlausur = searchBiggestKlausur(allKlausur);
        for(Raum r : allRaeume){
            if(r1 == null || r.getKapazitaet() > r1.getKapazitaet()){
                r1 = r;
            }
        }

        int wunschtermine = 0;
        for(Klausur k : allKlausur){
            if(!k.getWunschTermin().isEmpty()){
                wunschtermine += 1;
            }
        }
        while(wunschtermine >= 0){
            if(tempKlausur.getTeilnehmer() <= r1.getKapazitaet()){
                retmodel = noSplit(all_literals, allKlausur, allTermin, allRaeume, ctx);
                if(retmodel != null){
                    return retmodel;
                }
            }else{
                for(Raum r : allRaeume){
                    if(( r2 == null || r.getKapazitaet() > r2.getKapazitaet() ) && r1 != r){
                        r2 = r;
                    }
                }
                if(tempKlausur.getTeilnehmer() <= r1.getKapazitaet() + r2.getKapazitaet()){
                    retmodel = splitTwoNoSplit(all_literals, allKlausur, allTermin, allRaeume, ctx);
                    if(retmodel != null){
                        return retmodel;
                    }
                }else{
                    retmodel = splitTwoSplitTreeNoSplit(all_literals, allKlausur, allTermin, allRaeume, ctx);
                    if(retmodel != null){
                        return retmodel;
                    }
                }
            }
            setWunschTermin(allKlausur);
            wunschtermine -= 1;
        }
        throw new TestFailedException();
    }

    private static List<BoolExpr> mkMerge(BoolExpr[][][] allLiterals, List<Klausur> allKlausur, List<Termin> allTermin, List<Raum> allRaeume, Context ctx, HashMap <Integer, Integer> klausurenSplitingMap)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        //List<Klausur> already_planted = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        Set<String> klausur_studiengaenge = new TreeSet<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.

        for(int k = 0; k < allKlausur.size(); k++) {
            if (klausurenSplitingMap.get(k) == 4){
                for (int t = 0; t < allTermin.size(); t++) {
                    for (int r = 0; r < allRaeume.size(); r++) {
                        for(int k_2 = 0; k_2 < allKlausur.size(); k_2++){
                            if( k_2 != k && allKlausur.get(k).getTeilnehmer() + allKlausur.get(k_2).getTeilnehmer() <= allRaeume.get(r).getKapazitaet() && !allTermin.get(t).getRaum().contains(allRaeume.get(r)) && !allRaeume.get(r).getNummer().contains("AM2")) {
                                BoolExpr temp = ctx.mkAnd(allLiterals[k][t][r], allLiterals[k_2][t][r]);
                                klausur_is_written_once.add(temp);
                                for (int t_index = 0; t_index < allTermin.size(); t_index++) {
                                    for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                        if (t != t_index || r != r_index) {
                                            implication_list.add(allLiterals[k][t_index][r_index]);
                                            implication_list.add(allLiterals[k_2][t_index][r_index]);
                                        }
                                    }
                                }
                                for (int k_index = 0; k_index < allKlausur.size(); k_index++) {
                                    if (k != k_index && k_2 != k_index) {
                                        implication_list.add(allLiterals[k_index][t][r]);
                                        klausur_studiengaenge.clear();
                                        klausur_studiengaenge.addAll(allKlausur.get(k).getStudiengang());
                                        klausur_studiengaenge.addAll(allKlausur.get(k_2).getStudiengang());
                                        klausur_studiengaenge.retainAll(allKlausur.get(k_index).getStudiengang());
                                        if(!klausur_studiengaenge.isEmpty()){
                                            for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                                if(r != r_index){
                                                    implication_list.add(allLiterals[k_index][t][r_index]);
                                                }
                                            }
                                        }
                                    }
                                }
                                temp_array = new BoolExpr[implication_list.size()];
                                temp_array = implication_list.toArray(temp_array);
                                ret.add(ctx.mkImplies(temp, ctx.mkNot(ctx.mkOr(temp_array))));
                                implication_list.clear();
                                //break;
                            }
                        }
                    }
                }
                temp_array = new BoolExpr[klausur_is_written_once.size()];
                temp_array = klausur_is_written_once.toArray(temp_array);
                ret.add(ctx.mkOr(temp_array));
                klausur_is_written_once.clear();
            }
        }
        return ret;
    }

    private static List<BoolExpr> mkNoKlausurSplit (BoolExpr[][][] allLiterals, List<Klausur> allKlausur, List<Termin> allTermin, List<Raum> allRaeume, Context ctx, HashMap <Integer, Integer> klausurenSplitingMap)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        //List<Klausur> already_planted = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for(int k = 0; k < allKlausur.size(); k++) {
            if (klausurenSplitingMap.get(k) == 1){
                for (int t = 0; t < allTermin.size(); t++) {
                    if((!allKlausur.get(k).getWunschTermin().isEmpty() || !allKlausur.get(k).getMussTermin().isEmpty()) &&
                        !(allKlausur.get(k).getWunschTermin().contains(allTermin.get(t).getName()) || allKlausur.get(k).getMussTermin().contains(allTermin.get(t).getName()))){
                        continue;
                    }
                    for (int r = 0; r < allRaeume.size(); r++) {
                        if (allKlausur.get(k).getTeilnehmer() <= allRaeume.get(r).getKapazitaet() && !allTermin.get(t).getRaum().contains(allRaeume.get(r))) {
                            klausur_is_written_once.add(allLiterals[k][t][r]);
                            for (int t_index = 0; t_index < allTermin.size(); t_index++) {
                                for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                    if (t != t_index || r != r_index) {
                                        implication_list.add(allLiterals[k][t_index][r_index]);
                                    }
                                }
                            }
                            for (int k_index = 0; k_index < allKlausur.size(); k_index++) {
                                if (k != k_index) {
                                    implication_list.add(allLiterals[k_index][t][r]);
                                    if(checkStudiengang(allKlausur.get(k), allKlausur.get(k_index))){
                                        for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                            if(r != r_index){
                                                implication_list.add(allLiterals[k_index][t][r_index]);
                                            }
                                        }
                                    }
                                }
                            }
                            temp_array = new BoolExpr[implication_list.size()];
                            temp_array = implication_list.toArray(temp_array);
                            ret.add(ctx.mkImplies(allLiterals[k][t][r], ctx.mkNot(ctx.mkOr(temp_array))));
                            implication_list.clear();
                        }
                    }
                }
                temp_array = new BoolExpr[klausur_is_written_once.size()];
                temp_array = klausur_is_written_once.toArray(temp_array);
                ret.add(ctx.mkOr(temp_array));
                klausur_is_written_once.clear();
            }
        }
        return ret;
    }

    private static List<BoolExpr> mkKlausurSplitTwoRooms (BoolExpr[][][] allLiterals, List<Klausur> allKlausur, List<Termin> allTermin, List<Raum> allRaeume, Context ctx, HashMap <Integer, Integer> klausurenSplitingMap)throws TestFailedException, Z3Exception {
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for (int k = 0; k < allKlausur.size(); k++) {
            if (klausurenSplitingMap.get(k) == 2){
                for (int t = 0; t < allTermin.size(); t++) {
                    if((!allKlausur.get(k).getWunschTermin().isEmpty() || !allKlausur.get(k).getMussTermin().isEmpty()) &&
                        !(allKlausur.get(k).getWunschTermin().contains(allTermin.get(t).getName()) || allKlausur.get(k).getMussTermin().contains(allTermin.get(t).getName()))){
                        continue;
                    }
                    for (int r_1 = 0; r_1 < allRaeume.size(); r_1++) {
                        if (allKlausur.get(k).getTeilnehmer() >= allRaeume.get(r_1).getKapazitaet() && !allTermin.get(t).getRaum().contains(allRaeume.get(r_1))) {
                            for (int r_2 = 0; r_2 < allRaeume.size(); r_2++) {
                                if (r_1 != r_2 && allKlausur.get(k).getTeilnehmer() <= allRaeume.get(r_1).getKapazitaet() + allRaeume.get(r_2).getKapazitaet() && !allTermin.get(t).getRaum().contains(allRaeume.get(r_2))) {
                                    BoolExpr temp = ctx.mkAnd(allLiterals[k][t][r_1], allLiterals[k][t][r_2]);
                                    klausur_is_written_once.add(temp);
                                    for (int t_index = 0; t_index < allTermin.size(); t_index++) {
                                        for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                            if (t != t_index || (r_1 != r_index && r_2 != r_index)) {
                                                implication_list.add(allLiterals[k][t_index][r_index]);
                                            }
                                        }
                                    }
                                    for (int k_index = 0; k_index < allKlausur.size(); k_index++) {
                                        if (k != k_index) {
                                            implication_list.add(allLiterals[k_index][t][r_2]);
                                            implication_list.add(allLiterals[k_index][t][r_1]);
                                            if(checkStudiengang(allKlausur.get(k), allKlausur.get(k_index))){
                                                for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                                    if(r_1 != r_index && r_2 != r_index){
                                                        implication_list.add(allLiterals[k_index][t][r_index]);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    temp_array = new BoolExpr[implication_list.size()];
                                    temp_array = implication_list.toArray(temp_array);
                                    ret.add(ctx.mkImplies(temp, ctx.mkNot(ctx.mkOr(temp_array))));
                                    implication_list.clear();
                                }
                            }
                        }
                    }
                }
                temp_array = new BoolExpr[klausur_is_written_once.size()];
                temp_array = klausur_is_written_once.toArray(temp_array);
                ret.add(ctx.mkOr(temp_array));
                klausur_is_written_once.clear();
            }
        }
        return ret;
    }

    private static List<BoolExpr> mkKlausurSplitTreeRooms (BoolExpr[][][] allLiterals, List<Klausur> allKlausur, List<Termin> allTermine, List<Raum> allRaeume, Context ctx, HashMap <Integer, Integer> klausurenSplitingMap)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for(int k = 0; k < allKlausur.size(); k++){
            if (klausurenSplitingMap.get(k) == 3){
                for (int t = 0; t < allTermine.size(); t++) {
                    if((!allKlausur.get(k).getWunschTermin().isEmpty() || !allKlausur.get(k).getMussTermin().isEmpty()) &&
                        !(allKlausur.get(k).getWunschTermin().contains(allTermine.get(t).getName()) || allKlausur.get(k).getMussTermin().contains(allTermine.get(t).getName()))){
                        continue;
                    }
                    for (int r_1 = 0; r_1 < allRaeume.size(); r_1++) {
                        if (allKlausur.get(k).getTeilnehmer() >= allRaeume.get(r_1).getKapazitaet() && !allTermine.get(t).getRaum().contains(allRaeume.get(r_1))) {
                            for (int r_2 = 0; r_2 < allRaeume.size(); r_2++) {
                                if (r_1 != r_2 && allKlausur.get(k).getTeilnehmer() >= allRaeume.get(r_1).getKapazitaet() + allRaeume.get(r_2).getKapazitaet() && !allTermine.get(t).getRaum().contains(allRaeume.get(r_2))) {
                                    for (int r_3 = 0; r_3 < allRaeume.size(); r_3++) {
                                        if (r_1 != r_2 && r_2 != r_3 && r_1 != r_3 && allKlausur.get(k).getTeilnehmer() <= allRaeume.get(r_1).getKapazitaet() + allRaeume.get(r_2).getKapazitaet() + allRaeume.get(r_3).getKapazitaet()
                                                && !allTermine.get(t).getRaum().contains(allRaeume.get(r_3))) {
                                            BoolExpr temp = ctx.mkAnd(allLiterals[k][t][r_1], allLiterals[k][t][r_2], allLiterals[k][t][r_3]);
                                            klausur_is_written_once.add(temp);
                                            for (int t_index = 0; t_index < allTermine.size(); t_index++) {
                                                for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                                    if (t != t_index || (r_1 != r_index && r_2 != r_index && r_3 != r_index)) {
                                                        implication_list.add(allLiterals[k][t_index][r_index]);
                                                    }
                                                }
                                            }
                                            for (int k_index = 0; k_index < allKlausur.size(); k_index++) {
                                                if (k != k_index) {
                                                    implication_list.add(allLiterals[k_index][t][r_1]);
                                                    implication_list.add(allLiterals[k_index][t][r_2]);
                                                    implication_list.add(allLiterals[k_index][t][r_3]);
                                                    if(checkStudiengang(allKlausur.get(k), allKlausur.get(k_index))){
                                                        for (int r_index = 0; r_index < allRaeume.size(); r_index++) {
                                                            if(r_1 != r_index && r_2 != r_index && r_3 != r_index){
                                                                implication_list.add(allLiterals[k_index][t][r_index]);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            temp_array = new BoolExpr[implication_list.size()];
                                            temp_array = implication_list.toArray(temp_array);
                                            ret.add(ctx.mkImplies(temp, ctx.mkNot(ctx.mkOr(temp_array))));
                                            implication_list.clear();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                temp_array = new BoolExpr[klausur_is_written_once.size()];
                temp_array = klausur_is_written_once.toArray(temp_array);
                ret.add(ctx.mkOr(temp_array));
                klausur_is_written_once.clear();
            }
        }
        return ret;
    }

    private static Model noSplit(BoolExpr[][][] allLiterals, List<Klausur> allKlausuren, List<Termin> allTermin, List<Raum> allRaum, Context ctx)throws TestFailedException, Z3Exception{
        List<BoolExpr> formulas = new LinkedList<>();
        List<BoolExpr> part_formulas;
        List<Klausur> klausur_not_split = new LinkedList<>();
        List<Klausur> klausur_must_merg = new LinkedList<>();
        Solver s = ctx.mkSolver();
        HashMap <Integer, Integer> klausuren_spliting_map = new HashMap<>();

        for(Klausur k : allKlausuren){
            if(k.getTeilnehmer() <= 5){
                klausur_must_merg.add(k);
            }else{
                klausur_not_split.add(k);
            }
        }
        if(klausur_must_merg.size() % 2 != 0){
            Klausur biggestKlausur = searchBiggestKlausur(klausur_must_merg);
            klausur_not_split.add(biggestKlausur);
        }
        klausur_not_split.removeAll(klausur_must_merg);

        for(int k = 0; k < allKlausuren.size(); k++){
            if(klausur_must_merg.contains(allKlausuren.get(k))){
                klausuren_spliting_map.put(k, 4);
            }else if(klausur_not_split.contains(allKlausuren.get(k))){
                klausuren_spliting_map.put(k, 1);
            }
        }

        part_formulas = mkMerge(allLiterals, allKlausuren, allTermin, allRaum, ctx, klausuren_spliting_map);
        formulas.addAll(part_formulas);
        part_formulas = mkNoKlausurSplit(allLiterals, allKlausuren, allTermin, allRaum, ctx, klausuren_spliting_map);
        formulas.addAll(part_formulas);
        for(BoolExpr b : formulas){
            s.add(b);
        }
        System.out.println("Versuche auf keinen Raum zu spliten.");
        if(s.check() != Status.UNSATISFIABLE){
            System.out.println("GESCHAFFT!");
            return s.getModel();
        }
        return null;
    }

    private static Model splitTwoNoSplit(BoolExpr[][][] allLiterals, List<Klausur> allKlausuren, List<Termin> allTermin, List<Raum> allRaeume, Context ctx)throws TestFailedException, Z3Exception{
        List<BoolExpr> formulas = new LinkedList<>();
        List<BoolExpr> part_formulas = new LinkedList<>();
        List<Klausur> klausur_not_split = new LinkedList<>();
        klausur_not_split.addAll(allKlausuren);
        List<Klausur> klausur_must_split_two = new LinkedList<>();
        List<Klausur> klausur_must_merg = new LinkedList<>();
        Solver s = ctx.mkSolver();
        boolean end = false;
        HashMap <Integer, Integer> klausuren_spliting_map = new HashMap<>();
        Klausur biggestKlausur;
        Random ran = new Random();

        for(Klausur k : klausur_not_split){
            if(k.getTeilnehmer() <= 5){
                klausur_must_merg.add(k);
            }
        }
        int x = 0;
        if(!klausur_must_merg.isEmpty()) {
            x = ran.nextInt(klausur_must_merg.size());
        }
        if(!(klausur_must_merg.size() % 2 == 0) && !klausur_must_merg.isEmpty()){
            klausur_must_merg.remove(x);
        }
        klausur_not_split.removeAll(klausur_must_merg);

        System.out.println("Versuche auf keinen oder zwei Räume zu spliten.");
        int wer = 0;
        while(!end){
            wer += 1;
            System.out.println(wer);
            klausuren_spliting_map.clear();
            formulas.clear();
            biggestKlausur = searchBiggestKlausur(klausur_not_split);
            klausur_must_split_two.add(biggestKlausur);
            klausur_not_split.remove(biggestKlausur);
            for(int k = 0; k < allKlausuren.size(); k++){
                if(klausur_must_split_two.contains(allKlausuren.get(k))){
                    klausuren_spliting_map.put(k, 2);
                }else if(klausur_not_split.contains(allKlausuren.get(k))){
                    klausuren_spliting_map.put(k, 1);
                }else{
                    klausuren_spliting_map.put(k, 4);
                }
            }
            part_formulas = mkMerge(allLiterals, allKlausuren, allTermin, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkNoKlausurSplit(allLiterals, allKlausuren, allTermin, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkKlausurSplitTwoRooms(allLiterals, allKlausuren, allTermin, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            s.reset();
            for(BoolExpr b : formulas){
                s.add(b);
            }
            if (s.check() != Status.UNSATISFIABLE) {
                System.out.println("GESCHAFFT!");
                return s.getModel();
            }else if(klausur_not_split.isEmpty()){
                end = true;
            }
        }
        return null;
    }

    private static Model splitTwoSplitTreeNoSplit(BoolExpr[][][] allLiterals, List<Klausur> allKlausuren, List<Termin> allTermine, List<Raum> allRaeume, Context ctx)throws TestFailedException, Z3Exception{
        List<BoolExpr> formulas = new LinkedList<>();
        List<BoolExpr> part_formulas = new LinkedList<>();
        List<Klausur> klausur_must_merg = new LinkedList<>();
        List<Klausur> klausur_must_no_split = new LinkedList<>();
        List<Klausur> klausur_must_split_two = new LinkedList<>();
        List<Klausur> klausur_must_split_tree = new LinkedList<>();
        Solver s = ctx.mkSolver();
        boolean end = false;
        HashMap<Integer, Integer> klausuren_spliting_map = new HashMap<>();
        Klausur biggestKlausur;
        Random ran = new Random();

        for(Klausur k : allKlausuren){
            if(k.getTeilnehmer() <= 5){
                klausur_must_merg.add(k);
            }else if(k.getTeilnehmer() <= 25){
                klausur_must_no_split.add(k);
            }else{
                klausur_must_split_two.add(k);
            }
        }

        int x = 0;
        if(!klausur_must_merg.isEmpty()) {
            x = ran.nextInt(klausur_must_merg.size());
        }
        if(!(klausur_must_merg.size() % 2 == 0) && !klausur_must_merg.isEmpty()){
            klausur_must_merg.remove(x);
        }
        klausur_must_no_split.removeAll(klausur_must_merg);

        System.out.println("Versuche auf keinen, zwei oder Drei zu spliten.");
        int dbug = 0;
        while (!end) {
            dbug += 1;
            System.out.println(dbug);
            klausuren_spliting_map.clear();
            formulas.clear();
            biggestKlausur = searchBiggestKlausur(klausur_must_split_two);
            if(biggestKlausur != null){
                klausur_must_split_tree.add(biggestKlausur);
                klausur_must_split_two.remove(biggestKlausur);
            }
            for (int k = 0; k < allKlausuren.size(); k++) {
                if(klausur_must_split_tree.contains(allKlausuren.get(k))){
                    klausuren_spliting_map.put(k, 3);
                }else if(klausur_must_split_two.contains(allKlausuren.get(k))){
                    klausuren_spliting_map.put(k, 2);
                }else if(klausur_must_no_split.contains(allKlausuren.get(k))){
                    klausuren_spliting_map.put(k, 1);
                }else{
                    klausuren_spliting_map.put(k, 4);
                }
            }
            part_formulas = mkMerge(allLiterals, allKlausuren, allTermine, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkNoKlausurSplit(allLiterals, allKlausuren, allTermine, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkKlausurSplitTwoRooms(allLiterals, allKlausuren, allTermine, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkKlausurSplitTreeRooms(allLiterals, allKlausuren, allTermine, allRaeume, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            s.reset();
            for(BoolExpr b : formulas){
                s.add(b);
            }
            if (s.check() != Status.UNSATISFIABLE) {
                System.out.println("GESCHAFFT!");
                return s.getModel();
            }else if(klausur_must_no_split.size() + klausur_must_split_two.size() + klausur_must_split_tree.size() == allKlausuren.size()){
                end = true;
            }
        }
        return null;
    }

    private static List<Klausur> readFilesKlausur(String file) throws IOException{
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        int nummer = 1;
        List<Klausur> ret = new LinkedList<>();
        r.readLine();
        String temp = r.readLine();
        while(temp != null){
            String klausurnummer = "K"+nummer;
            line = temp.split("[,]");
            String name = line[0];
            int dauer = Integer.parseInt(line[1]);
            int teilnehmer = Integer.parseInt(line[2]);
            String[] datum = line[3].split("[.]");
            String[] zeit = line[4].split(":");
            //Date date = null;
            String[] studiengang = null;
            if(line.length > 5){
                studiengang = line[5].split("[ ]");
            }
            String[] wunschTermin = null;
            if(line.length > 6){
                wunschTermin = line[6].split("[ ]");
            }
            String[] mussTermin = null;
            if(line.length > 7){
                mussTermin = line[7].split("[ ]");
            }
            String[] SBnummer = null;
            if(line.length > 8){
                SBnummer = line[8].split("[ ]");
            }
            Date date = new Date(Integer.parseInt(datum[2]),Integer.parseInt(datum[1]),Integer.parseInt(datum[0]),
                   Integer.parseInt(zeit[0]),Integer.parseInt(zeit[1]));
            Klausur klausur = new Klausur(klausurnummer, name, dauer, teilnehmer, date);
            if(studiengang != null){
                for(String s : studiengang){
                    klausur.addStudiengang(s);
                }
            }
            if(wunschTermin != null){
                for(String s : wunschTermin){
                    if(!s.equals(""))
                    klausur.addWunschTermin(s);
                }
            }
            if(mussTermin != null){
                for(String s : mussTermin){
                    if(!s.equals(""))
                        klausur.addMussTermin(s);
                }
            }
            if(SBnummer != null){
                for(String s : SBnummer){
                    if(!s.equals(""))
                        klausur.addSBnummer(s);
                }
            }
            ret.add(klausur);
            temp = r.readLine();
            nummer += 1;
        }
        return ret;
    }

    private static List<Raum> readFilesRaume(String file) throws IOException{
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        List<Raum> ret = new LinkedList<>();
        r.readLine();
        String temp = r.readLine();
        while(temp != null){
            line = temp.split(",");
            String name = line[0];
            String nummer = line[1];
            int kapazitaet = Integer.parseInt(line[2]);
            Raum raum = new Raum(name, nummer, kapazitaet);
            ret.add(raum);
            temp = r.readLine();
        }
        return ret;
    }

    private static List<Termin> readFilesTermin(String file, List<Raum> raeume) throws IOException{
        List<Termin> ret = new LinkedList<>();
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        r.readLine();
        String temp = r.readLine();
        while(temp != null){
            line = temp.split(",");
            String[] raumname = null;
            String name = line[0];
            if(line.length > 1){
                raumname = line[1].split(" ");
            }
            Termin termin = new Termin(name);
            if(raumname != null){
                for (Raum ra : raeume){
                    for(int r_index = 0; r_index < raumname.length; r_index++){
                        if(ra.getName().contains(raumname[r_index])){
                            termin.addRaum(ra);
                        }
                    }
                }
            }
            ret.add(termin);
            temp = r.readLine();
        }
        return ret;
    }

    private static Klausur searchBiggestKlausur(List<Klausur> allKlausuren){
        Klausur ret = null;
        for(Klausur k : allKlausuren){
            if(ret != null){
                if(ret.getTeilnehmer() < k.getTeilnehmer()){
                    ret = k;
                }
            }else{
                ret = k;
            }
        }
        return ret;
    }

    private static Boolean checkStudiengang(Klausur k1, Klausur k2){
        Set<String> check = new TreeSet<>();
        check.addAll(k1.getStudiengang());
        check.retainAll(k2.getStudiengang());
        if(!check.isEmpty()){
            return true;
        }else{
            return false;
        }
    }

    private static void setWunschTermin(List<Klausur> allKlausuren){
        for(Klausur k : allKlausuren){
            if(!k.getWunschTermin().isEmpty()){
                k.getWunschTermin().remove(0);
                System.err.println("Wunschtermin wurde entfernt.");
                break;
            }
        }
        return;
    }

    private static void mkPlan(Model model, List<Klausur> allKlausur, List<Termin> all_termine, List<Raum> all_raeume){
        String plan = "";
        String [] klausurenplan;
        for(String s : model.toString().split("\n")){
            if(s.contains("-> true")){
                plan += s;
            }
        }
        plan = plan.replaceAll("-> true", "");
        klausurenplan = plan.split(" ");
        for(String s : klausurenplan){
            Klausur planklausur = null;
            Termin plantermin = null;
            List<Raum> planraum = new LinkedList<>();
            String[] temp = s.split("_");
            for(Klausur k : allKlausur){
                if(k.getKlausurnummer().equals(temp[0])){
                    planklausur = k;
                    break;
                }
            }
            for(Termin t : all_termine){
                if(t.getName().equals(temp[1])){
                    plantermin = t;
                    break;
                }
            }
            for(Raum r : all_raeume){
                if(r.getName().equals(temp[2])){
                    planraum.add(r);
                }
            }
            if(planklausur != null && plantermin != null){
                for(Raum r : planraum){
                 if(planklausur.getTerminmap().get(plantermin) != null){
                        planklausur.addRaum(plantermin, r);
                 }else{
                        planklausur.addTermin(plantermin);
                        planklausur.addRaum(plantermin, r);
                 }
                }
            }
        }
        String[][] klausurplan = new String[allKlausur.size()+1][all_termine.size()+1];
        for(int k = 0; k < allKlausur.size(); k++){
            klausurplan[k+1][0] = allKlausur.get(k).getName();
        }
        for(int t = 0; t < all_termine.size(); t++){
            klausurplan[0][t+1] = all_termine.get(t).getName();
        }

        for(int k = 0; k < allKlausur.size(); k++){
            HashMap<Termin, List<Raum>> temp = allKlausur.get(k).getTerminmap();
            for(Termin t : temp.keySet()){
                for(int t_2 = 0; t_2 < all_termine.size(); t_2++){
                    if(t.equals(all_termine.get(t_2))){
                        for(Raum r : temp.get(t)){
                            klausurplan[k+1][t_2+1] += r.getName() + " ";
                            System.out.println(allKlausur.get(k).getKlausurnummer() + " findet im Raum " + r.getName() + " zum Termin " + t.getName() + " Statt.");
                        }
                    }
                }
            }
        }
        try
        {
            FileWriter fw = new FileWriter("Plan.csv");
            BufferedWriter bw = new BufferedWriter(fw);
            for(int row = 0; row < klausurplan[0].length; row ++){
                for(int column = 0; column < klausurplan.length; column ++){
                    if(klausurplan[column][row] == null){
                        bw.write(",");
                    }else{
                        bw.write(klausurplan[column][row].replace("null", "") + ",");
                    }
                }
                bw.write("\n");
            }
            bw.close();
            fw.close();
        }catch ( IOException e){
            System.err.println(e);
        };
        return;
    }
}