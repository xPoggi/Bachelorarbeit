package Bachelorarbeit;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.*;
import org.w3c.dom.Entity;

import java.io.*;
import java.util.*;

/**
 * Created by Poggi on 19.04.2017.
 * Planning-program for FH-Luebeck
 */

public class Main{
    public static void main(String[] args) throws Z3Exception, IOException, TestFailedException, addFailExeption{
        //Read Data.
        String testdata_nosplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\nosplit\\";
        String testdata_twosplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\twosplit\\";
        String testdata_treesplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\treesplit\\";
        String testdata_two_treesplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\two_treesplit\\";
        List<Klausur> klausuren = readFilesKlausur(testdata_nosplit+args[0]);
        List<Raum> raume = readFilesRaume(testdata_nosplit+args[2]);
        List<Termin> termin = readFilesTermin(testdata_nosplit+args[1], raume);

        //Z3 Context erstellen um SAT-Solver Nutzen zu können.
        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("Model", "true");
        Context ctx = new Context(cfg);
        //Z3 Ausgabe umstellen.(nicht mehr SMT sondern einfache Variablen mit deren boolischen Werten)
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL);

        String result [] = KlausurPlanning(klausuren, termin, raume, ctx).toString().split("\n");
        for(String s : result){
            if(s.contains("true")){
                System.out.println(s);
            }
        }
    }

    private static Model KlausurPlanning (List<Klausur> klausur, List<Termin> termin, List<Raum> raum, Context ctx)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> planningFormula = new LinkedList<>();
        List<BoolExpr> temp;
        List<Klausur> klausur_must_no_split = new LinkedList<>();
        klausur_must_no_split.addAll(klausur);
        List<Klausur> klausur_must_split_two = new LinkedList<>();
        List<Klausur> klausur_must_split_tree = new LinkedList<>();
        BoolExpr[][][] all_literals = new BoolExpr[klausur.size()][termin.size()][raum.size()];
        Solver s = ctx.mkSolver();
        s.reset();
        Klausur biggestKlausur;
        List<Integer> klausuren_indexe_two = new LinkedList<>();
        List<Integer> klausuren_indexe_tree = new LinkedList<>();
        //---------------Declaration end---------------------------

        //---------------Creating or-literals----------------------
        for(int k = 0; k < klausur.size(); k++){
            for(int t = 0; t < termin.size(); t++){
                //-------------creating no split---------------------
                for(int r = 0; r < raum.size(); r++){
                    all_literals[k][t][r] = ctx.mkBoolConst(klausur.get(k).getName()+"_"+termin.get(t).getName()+"_"+raum.get(r).getName());
                }
            }
        }
        planningFormula = mkNoKlausurSplit(all_literals, klausur_must_no_split, termin, raum, ctx, klausuren_indexe_two, klausuren_indexe_tree);
        for(BoolExpr b : planningFormula){
            s.add(b);
        }
        System.out.println("Versuche nicht zu spliten.");
        if(s.check() != Status.UNSATISFIABLE){
            System.out.println("GESCHAFFT!");
            return s.getModel();
        }else {
            boolean split_two_no_split = true;
            boolean split_tree_no_split = false;
            boolean split_two_split_tree = false;
            boolean split_two_split_tree_no_split = false;
            boolean end = false;
            while(!end){
                klausur_must_no_split.clear();
                klausur_must_no_split.addAll(klausur);
                System.out.println("Versuche auf keinen oder zwei Räume zu spliten.");
                while(split_two_no_split){
                    klausuren_indexe_two.clear();
                    s.reset();
                    planningFormula.clear();
                    biggestKlausur = searchBiggestKlausur(klausur_must_no_split);
                    klausur_must_split_two.add(biggestKlausur);
                    klausur_must_no_split.remove(biggestKlausur);
                    for(int k = 0; k < klausur.size(); k++) {
                        for (int k_2 = 0; k_2 < klausur_must_split_two.size(); k_2++) {
                            if (klausur.get(k).equals(klausur_must_split_two.get(k_2))) {
                                klausuren_indexe_two.add(k);
                            }
                        }
                    }
                    temp = mkNoKlausurSplit(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two, klausuren_indexe_tree);
                    planningFormula.addAll(temp);
                    temp = mkKlausurSplitTwoRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two);
                    planningFormula.addAll(temp);
                    for(BoolExpr b : planningFormula){
                        s.add(b);
                    }
                    if (s.check() != Status.UNSATISFIABLE) {
                        System.out.println("GESCHAFFT!");
                        return s.getModel();
                    }else if(klausur_must_no_split.isEmpty() && klausur_must_split_two.size() == klausur.size()){
                        split_two_no_split = false;
                        split_tree_no_split = true;
                    }
                }
                klausur_must_no_split.clear();
                klausur_must_split_two.clear();
                klausuren_indexe_two.clear();
                klausur_must_no_split.addAll(klausur);
                System.out.println("Versuche auf keinen oder drei Räume zu spliten.");
                while(split_tree_no_split){
                    klausuren_indexe_tree.clear();
                    planningFormula.clear();
                    s.reset();
                    biggestKlausur = searchBiggestKlausur(klausur_must_no_split);
                    klausur_must_split_tree.add(biggestKlausur);
                    klausur_must_no_split.remove(biggestKlausur);
                    for(int k = 0; k < klausur.size(); k++) {
                        for (int k_2 = 0; k_2 < klausur_must_split_tree.size(); k_2++) {
                            if (klausur.get(k).equals(klausur_must_split_tree.get(k_2))) {
                                klausuren_indexe_tree.add(k);
                            }
                        }
                    }
                    temp = mkNoKlausurSplit(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two, klausuren_indexe_tree);
                    planningFormula.addAll(temp);
                    temp = mkKlausurSplitTreeRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_tree);
                    planningFormula.addAll(temp);
                    for(BoolExpr b : planningFormula){
                        s.add(b);
                    }
                    if (s.check() != Status.UNSATISFIABLE) {
                        System.out.println("GESCHAFFT!");
                        return s.getModel();
                    }else if(klausur_must_no_split.isEmpty() && klausur_must_split_tree.size() == klausur.size()){
                        split_tree_no_split = false;
                        split_two_split_tree = true;
                    }
                }
                klausur_must_split_two.clear();
                klausur_must_split_tree.clear();
                klausuren_indexe_tree.clear();
                klausur_must_split_two.addAll(klausur);
                System.out.println("Versuche auf zwei oder drei Räume zu spliten.");
                while(split_two_split_tree){
                    planningFormula.clear();
                    klausuren_indexe_tree.clear();
                    klausuren_indexe_two.clear();
                    biggestKlausur = searchBiggestKlausur(klausur_must_split_two);
                    klausur_must_split_tree.add(biggestKlausur);
                    klausur_must_split_two.remove(biggestKlausur);
                    for(int k = 0; k < klausur.size(); k++) {
                        for (int k_2 = 0; k_2 < klausur_must_split_tree.size(); k_2++) {
                            if (klausur.get(k).equals(klausur_must_split_tree.get(k_2))) {
                                klausuren_indexe_tree.add(k);
                            }
                        }
                        for(int k_2 = 0; k_2 < klausur_must_split_two.size(); k_2++){
                            if (klausur.get(k).equals(klausur_must_split_two.get(k_2))) {
                                klausuren_indexe_two.add(k);
                            }
                        }
                    }
                    temp = mkKlausurSplitTwoRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two);
                    planningFormula.addAll(temp);
                    temp = mkKlausurSplitTreeRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_tree);
                    planningFormula.addAll(temp);
                    for(BoolExpr b : planningFormula){
                        s.add(b);
                    }
                    if (s.check() != Status.UNSATISFIABLE) {
                        System.out.println("GESCHAFFT!");
                        return s.getModel();
                    }else if(klausur_must_split_two.isEmpty() && klausur_must_split_tree.size() == klausur.size()){
                        split_two_split_tree = false;
                        split_two_split_tree_no_split = true;
                    }
                }
                klausur_must_no_split.clear();
                klausur_must_split_two.clear();
                klausur_must_split_tree.clear();
                klausur_must_split_two.addAll(klausur);
                System.out.println("Versuche auf keinen, zwei oder drei Räume zu spliten.");
                while(split_two_split_tree_no_split){
                    planningFormula.clear();
                    klausuren_indexe_two.clear();
                    klausuren_indexe_tree.clear();
                    for(Klausur k : klausur_must_split_two){
                        if(k.getTeilnehmer() <= 25){
                            klausur_must_no_split.add(k);
                        }
                    }
                    biggestKlausur = searchBiggestKlausur(klausur_must_split_two);
                    klausur_must_split_tree.add(biggestKlausur);
                    klausur_must_split_two.removeAll(klausur_must_split_tree);
                    klausur_must_split_two.removeAll(klausur_must_no_split);
                    for(int k = 0; k < klausur.size(); k++) {
                        for (int k_2 = 0; k_2 < klausur_must_split_tree.size(); k_2++) {
                            if (klausur.get(k).equals(klausur_must_split_tree.get(k_2))) {
                                klausuren_indexe_tree.add(k);
                            }
                        }
                        for(int k_2 = 0; k_2 < klausur_must_split_two.size(); k_2++){
                            if (klausur.get(k).equals(klausur_must_split_two.get(k_2))) {
                                klausuren_indexe_two.add(k);
                            }
                        }
                    }
                    temp = mkNoKlausurSplit(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two, klausuren_indexe_tree);
                    planningFormula.addAll(temp);
                    temp = mkKlausurSplitTwoRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two);
                    planningFormula.addAll(temp);
                    temp = mkKlausurSplitTreeRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_tree);
                    planningFormula.addAll(temp);
                    for(BoolExpr b : planningFormula){
                        s.add(b);
                    }
                    if (s.check() != Status.UNSATISFIABLE) {
                        System.out.println("GESCHAFFT!");
                        return s.getModel();
                    }else if(klausur_must_split_two.isEmpty() && klausur_must_no_split.size()+klausur_must_split_tree.size() == klausur.size()){
                        split_two_split_tree_no_split
                                 = false;
                        end = true;
                    }
                }
            }
        throw new TestFailedException();
        }
//            boolean klausuren_split_two = true;
//            boolean klausuren_split_tree = false;
//            boolean klausuren_split_tree_with_no_split = false;
//            boolean klausuren_split_two_with_klausuren_split_tree_and_no_split = false;
//            while(klausur_must_split_tree.size() != klausur.size()){
//                klausuren_indexe_two.clear();
//                klausuren_indexe_tree.clear();
//                planningFormula.clear();
////                biggestKlausur = searchBiggestKlausur(klausuren);
////                klausur_must_split_two.add(biggestKlausur);
////                klausuren.remove(biggestKlausur);
//                if(klausuren_split_tree_with_no_split){
//                    biggestKlausur = searchBiggestKlausur(klausur_must_no_split);
//                    klausur_must_no_split.remove(biggestKlausur);
//                    klausur_must_split_tree.add(biggestKlausur);
//                }
//                if(klausuren_split_tree){
//                    biggestKlausur = searchBiggestKlausur(klausur_must_split_two);
//                    klausur_must_split_tree.add(biggestKlausur);
//                    klausur_must_split_two.remove(biggestKlausur);
//                }
//                if(klausuren_split_two){
//                    biggestKlausur = searchBiggestKlausur(klausur_must_no_split);
//                    klausur_must_split_two.add(biggestKlausur);
//                    klausur_must_no_split.remove(biggestKlausur);
//                }
//                if(klausuren_split_two_with_klausuren_split_tree_and_no_split){
//                    biggestKlausur = searchBiggestKlausur(klausur_must_split_two);
//                    klausur_must_split_tree.add(biggestKlausur);
//                    klausur_must_split_two.remove(biggestKlausur);
//                    for(Klausur k : klausur_must_split_two){
//                        if(k.getTeilnehmer() <= 25){
//                            klausur_must_no_split.add(k);
//                        }
//                    }
//                    klausur_must_split_two.removeAll(klausur_must_no_split);
//                }
//                for(int k = 0; k < klausur.size(); k++){
//                    for(int k_2 = 0; k_2 < klausur_must_split_two.size(); k_2++){
//                        if(klausur.get(k).equals(klausur_must_split_two.get(k_2))){
//                            klausuren_indexe_two.add(k);
//                        }
//                    }
//                    for(int k_2 = 0; k_2 < klausur_must_split_tree.size(); k_2++){
//                        if(klausur.get(k).equals(klausur_must_split_tree.get(k_2))){
//                            klausuren_indexe_tree.add(k);
//                        }
//                    }
//                }
//                temp = mkNoKlausurSplit(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two, klausuren_indexe_tree);
//                planningFormula.addAll(temp);
//                temp = mkKlausurSplitTwoRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_two);
//                planningFormula.addAll(temp);
//                temp = mkKlausurSplitTreeRooms(all_literals, klausur, termin, raum, ctx, klausuren_indexe_tree);
//                planningFormula.addAll(temp);
//                s.reset();
//                for (BoolExpr b : planningFormula) {
//                    s.add(b);
//                }
//                if (s.check() != Status.UNSATISFIABLE) {
//                    System.out.println("mkKlausurSplitTwoRooms");
//                    return s.getModel();
//                }
//                if(klausur_must_split_two.size() >= klausur.size()){
//                    klausuren_split_two = false;
//                    klausuren_split_tree = true;
//                }
//                if(klausuren_split_tree && klausur_must_split_tree.size() == klausur.size()){
//                    klausur_must_split_tree.clear();
//                    klausur_must_split_two.clear();
//                    klausur_must_split_two.addAll(klausur);
//                    klausur_must_no_split.clear();
//                    klausuren_split_two_with_klausuren_split_tree_and_no_split = true;
//                    klausuren_split_tree = false;
//                    klausuren_split_two = false;
//                    klausuren_split_tree_with_no_split = false;
//                }
//                if(klausuren_split_tree && klausur_must_split_two.size() == 0){
//                    klausur_must_split_tree.clear();
//                    klausuren_split_tree_with_no_split = true;
//                    klausuren_split_tree = false;
//                    klausur_must_no_split.clear();
//                    klausur_must_no_split.addAll(klausur);
//                }
//            }
//        }
//        System.err.println("Es konnte kein Plan erstellt werden!");
//        throw new TestFailedException();
    }

    private static List<BoolExpr> mkNoKlausurSplit (BoolExpr[][][] all_literals, List<Klausur> klausur, List<Termin> termin, List<Raum> raum, Context ctx, List<Integer> klausuren_indexe,List<Integer> klausuren_indexe_tree)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for(int k = 0; k < klausur.size(); k++) {
            if (!klausuren_indexe.contains(k) && !klausuren_indexe_tree.contains(k)){
                for (int t = 0; t < termin.size(); t++) {
                    for (int r = 0; r < raum.size(); r++) {
                        if (klausur.get(k).getTeilnehmer() <= raum.get(r).getKapazitaet() && raum.get(r) != termin.get(t).getRaum()) {
                            boolean two_klausur_in_one_room = false;
                            for (int k_2 = 0; k_2 < klausur.size(); k_2++) {
                                if (k != k_2 && klausur.get(k).getTeilnehmer() + klausur.get(k_2).getTeilnehmer() <= raum.get(r).getKapazitaet() && !raum.get(r).getNummer().contains("AM2")) {
                                    BoolExpr temp = ctx.mkAnd(all_literals[k][t][r], all_literals[k_2][t][r]);
                                    klausur_is_written_once.add(temp);
                                    for (int t_index = 0; t_index < termin.size(); t_index++) {
                                        for (int r_index = 0; r_index < raum.size(); r_index++) {
                                            if (t != t_index || r != r_index) {
                                                implication_list.add(all_literals[k][t_index][r_index]);
                                                implication_list.add(all_literals[k_2][t_index][r_index]);
                                            }
                                        }
                                    }
                                    for (int k_index = 0; k_index < klausur.size(); k_index++) {
                                        if (k_2 != k_index && k != k_index) {
                                            implication_list.add(all_literals[k_index][t][r]);
                                        }
                                    }
                                    temp_array = new BoolExpr[implication_list.size()];
                                    temp_array = implication_list.toArray(temp_array);
                                    ret.add(ctx.mkImplies(temp, ctx.mkNot(ctx.mkOr(temp_array))));
                                    two_klausur_in_one_room = true;
                                    implication_list.clear();
                                    break;
                                }
                            }
                            if (!two_klausur_in_one_room) {
                                klausur_is_written_once.add(all_literals[k][t][r]);
                                for (int t_index = 0; t_index < termin.size(); t_index++) {
                                    for (int r_index = 0; r_index < raum.size(); r_index++) {
                                        if (t != t_index || r != r_index) {
                                            implication_list.add(all_literals[k][t_index][r_index]);
                                        }
                                    }
                                }
                                for (int k_index = 0; k_index < klausur.size(); k_index++) {
                                    if (k != k_index) {
                                        implication_list.add(all_literals[k_index][t][r]);
                                    }
                                }
                                temp_array = new BoolExpr[implication_list.size()];
                                temp_array = implication_list.toArray(temp_array);
                                ret.add(ctx.mkImplies(all_literals[k][t][r], ctx.mkNot(ctx.mkOr(temp_array))));
                                implication_list.clear();
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

    private static List<BoolExpr> mkKlausurSplitTwoRooms (BoolExpr[][][] all_literals, List<Klausur> klausur, List<Termin> termin, List<Raum> raum, Context ctx, List<Integer> klausuren_indexe)throws TestFailedException, Z3Exception {
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for (int k = 0; k < klausur.size(); k++) {
            if (klausuren_indexe.contains(k)){
                for (int t = 0; t < termin.size(); t++) {
                    for (int r_1 = 0; r_1 < raum.size(); r_1++) {
                        if (klausur.get(k).getTeilnehmer() > raum.get(r_1).getKapazitaet()) {
                            for (int r_2 = 0; r_2 < raum.size(); r_2++) {
                                if (r_1 != r_2 && klausur.get(k).getTeilnehmer() <= raum.get(r_1).getKapazitaet() + raum.get(r_2).getKapazitaet()) {
                                    BoolExpr temp = ctx.mkAnd(all_literals[k][t][r_1], all_literals[k][t][r_2]);
                                    klausur_is_written_once.add(temp);
                                    for (int t_index = 0; t_index < termin.size(); t_index++) {
                                        for (int r_index = 0; r_index < raum.size(); r_index++) {
                                            if (t != t_index || (r_1 != r_index && r_2 != r_index)) {
                                                implication_list.add(all_literals[k][t_index][r_index]);
                                            }
                                        }
                                    }
                                    for (int k_index = 0; k_index < klausur.size(); k_index++) {
                                        if (k != k_index) {
                                            implication_list.add(all_literals[k_index][t][r_1]);
                                            implication_list.add(all_literals[k_index][t][r_2]);
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

    private static List<BoolExpr> mkKlausurSplitTreeRooms (BoolExpr[][][] all_literals, List<Klausur> klausur, List<Termin> termin, List<Raum> raum, Context ctx, List<Integer> klausuren_indexe)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for(int k = 0; k < klausur.size(); k++){
            if (klausuren_indexe.contains(k)) {
                for (int t = 0; t < termin.size(); t++) {
                    for (int r_1 = 0; r_1 < raum.size(); r_1++) {
                        if (klausur.get(k).getTeilnehmer() > raum.get(r_1).getKapazitaet()) {
                            for (int r_2 = 0; r_2 < raum.size(); r_2++) {
                                if (r_1 != r_2 && klausur.get(k).getTeilnehmer() > raum.get(r_1).getKapazitaet() + raum.get(r_2).getKapazitaet()) {
                                    for (int r_3 = 0; r_3 < raum.size(); r_3++) {
                                        if (r_1 != r_2 && r_2 != r_3 && r_1 != r_3 && klausur.get(k).getTeilnehmer() <= raum.get(r_1).getKapazitaet() + raum.get(r_2).getKapazitaet() + raum.get(r_3).getKapazitaet()) {
                                            BoolExpr temp = ctx.mkAnd(all_literals[k][t][r_1], all_literals[k][t][r_2], all_literals[k][t][r_3]);
                                            klausur_is_written_once.add(temp);
                                            for (int t_index = 0; t_index < termin.size(); t_index++) {
                                                for (int r_index = 0; r_index < raum.size(); r_index++) {
                                                    if (t != t_index || (r_1 != r_index && r_2 != r_index && r_3 != r_index)) {
                                                        implication_list.add(all_literals[k][t_index][r_index]);
                                                    }
                                                }
                                            }
                                            for (int k_index = 0; k_index < klausur.size(); k_index++) {
                                                if (k != k_index) {
                                                    implication_list.add(all_literals[k_index][t][r_1]);
                                                    implication_list.add(all_literals[k_index][t][r_2]);
                                                    implication_list.add(all_literals[k_index][t][r_3]);
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

    private static List<Klausur> readFilesKlausur(String file) throws IOException{
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        List<Klausur> ret = new LinkedList<>();
        r.readLine();
        String temp = r.readLine();
        while(temp != null){
            line = temp.split(",");
            String name = line[0];
            //int dauer = Integer.parseInt(line[1]);
            int teilnehmer = Integer.parseInt(line[2]);
            //String[] datum = line[3].split("\\.");
            //String[] zeit = line[4].split(":");
            Date date = null;
            //Date date = new Date(Integer.parseInt(datum[2]),Integer.parseInt(datum[1]),Integer.parseInt(datum[0]),
             //       Integer.parseInt(zeit[0]),Integer.parseInt(zeit[1]));
            ret.add(new Klausur(name,10,teilnehmer,date));
            temp = r.readLine();
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

    private static List<Termin> readFilesTermin(String file, List<Raum> raum) throws IOException{
        List<Termin> ret = new LinkedList<>();
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        r.readLine();
        String temp = r.readLine();
        while(temp != null){
            boolean flag = true;
            line = temp.split(",");
            String raumname = null;
            String name = line[0];
            if(line.length > 1){
                raumname = line[1];
            }else{
                raumname = "kein_raum_eingetragen!";
            }
            for (Raum ra : raum){
                if(ra.getName().contains(raumname)){
                    ret.add(new Termin(name, ra));
                    flag = false;
                    break;
                }
            }
            if(flag){
                ret.add(new Termin(name));
            }
            temp = r.readLine();
        }
        return ret;
    }

    private static Klausur searchBiggestKlausur(List<Klausur> klausur){
        Klausur ret = null;
        for(Klausur k : klausur){
            if(ret != null){
                if(ret.getTeilnehmer() < k.getTeilnehmer()){
                    ret = k;
                }
            }else{
                ret = k;
            }
        }
        if(ret != null){
            return ret;
        }else{
            throw new NullPointerException();
        }
    }

    private static Klausur searchSmallestKlausur(List<Klausur> klausur) {
        Klausur ret = null;
        for(Klausur k : klausur){
            if(ret != null){
                if(ret.getTeilnehmer() > k.getTeilnehmer()){
                    ret = k;
                }
            }else{
                ret = k;
            }
        }
        if(ret != null){
            return ret;
        }else{
            return null;
        }
    }
}