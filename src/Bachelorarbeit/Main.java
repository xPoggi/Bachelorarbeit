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
        long start = new Date().getTime();
        //Read Data.
        String testdata_nosplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\nosplit\\";
        String testdata_twosplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\twosplit\\";
        String testdata_treesplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\treesplit\\";
        String testdata_two_treesplit = "C:\\Users\\Poggi\\IdeaProjects\\Bachelorarbeit\\test\\two_treesplit\\";
        String datapath = testdata_two_treesplit;

        List<Klausur> klausuren = readFilesKlausur(datapath + args[0]);
        List<Raum> raume = readFilesRaume(datapath + args[2]);
        List<Termin> termin = readFilesTermin(datapath + args[1], raume);

        //Z3 Context erstellen um SAT-Solver Nutzen zu können.
        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("Model", "true");
        Context ctx = new Context(cfg);
        //Z3 Ausgabe umstellen.(nicht mehr SMT sondern einfache Variablen mit deren boolischen Werten)
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL);

        System.out.println("Versuche " + klausuren.size() + " Klausuren, " + raume.size() + " Räume und " + termin.size() + " Termine zu planen!");

        Model plan = KlausurPlanning(klausuren, termin, raume, ctx);
        mkPlan(plan, klausuren, termin, raume);
        long runningTime = new Date().getTime() - start;
        System.out.println("Das Planen hat: " + (int)(runningTime/1000/60) + " Sekunden gedauert!");
    }

    private static Model KlausurPlanning (List<Klausur> all_klausuren, List<Termin> all_termine, List<Raum> all_raueme, Context ctx)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        BoolExpr[][][] all_literals = new BoolExpr[all_klausuren.size()][all_termine.size()][all_raueme.size()];
        Model retmodel;
        //---------------Declaration end---------------------------

        //---------------Creating or-literals----------------------
        for(int k = 0; k < all_klausuren.size(); k++){
            for(int t = 0; t < all_termine.size(); t++){
                //-------------creating no split---------------------
                for(int r = 0; r < all_raueme.size(); r++){
                    all_literals[k][t][r] = ctx.mkBoolConst(all_klausuren.get(k).getName()+"_"+all_termine.get(t).getName()+"_"+all_raueme.get(r).getName());
                }
            }
        }
        Raum r1 = null;
        Raum r2 = null;
        Klausur temp = searchBiggestKlausur(all_klausuren);
        for(Raum r : all_raueme){
            if(r1 == null || r.getKapazitaet() > r1.getKapazitaet()){
                r1 = r;
            }
        }
        if(temp.getTeilnehmer() <= r1.getKapazitaet()){
            retmodel = no_split(all_literals, all_klausuren, all_termine, all_raueme, ctx);
            if(retmodel != null){
                return retmodel;
            }
        }else{
            for(Raum r : all_raueme){
                if(( r2 == null || r.getKapazitaet() > r2.getKapazitaet() ) && r1 != r){
                    r2 = r;
                }
            }
            if(temp.getTeilnehmer() <= r1.getKapazitaet() + r2.getKapazitaet()){
                retmodel = split_two_no_split(all_literals, all_klausuren, all_termine, all_raueme, ctx);
                if(retmodel != null){
                    return retmodel;
                }
            }else{
                retmodel = split_two_split_tree_no_split(all_literals, all_klausuren, all_termine, all_raueme, ctx);
                if(retmodel != null){
                    return retmodel;
                }
            }
        }
        throw new TestFailedException();
    }

    private static List<BoolExpr> mkMerge(BoolExpr[][][] all_literals, List<Klausur> all_klausuren, List<Termin> all_termine, List<Raum> all_raueme, Context ctx, HashMap <Integer, Integer> klausuren_spliting_map)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        //List<Klausur> already_planted = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.

        for(int k = 0; k < all_klausuren.size(); k++) {
            if (klausuren_spliting_map.get(k).intValue() == 4){
                for (int t = 0; t < all_termine.size(); t++) {
                    for (int r = 0; r < all_raueme.size(); r++) {
                        for(int k_2 = 0; k_2 < all_klausuren.size(); k_2++){
                            if( k_2 != k && all_klausuren.get(k).getTeilnehmer() + all_klausuren.get(k_2).getTeilnehmer() <= all_raueme.get(r).getKapazitaet() && !all_termine.get(t).getRaum().contains(all_raueme.get(r)) && !all_raueme.get(r).getNummer().contains("AM2")) {
                                BoolExpr temp = ctx.mkAnd(all_literals[k][t][r], all_literals[k_2][t][r]);
                                klausur_is_written_once.add(temp);
                                for (int t_index = 0; t_index < all_termine.size(); t_index++) {
                                    for (int r_index = 0; r_index < all_raueme.size(); r_index++) {
                                        if (t != t_index || r != r_index) {
                                            implication_list.add(all_literals[k][t_index][r_index]);
                                            implication_list.add(all_literals[k_2][t_index][r_index]);
                                        }
                                    }
                                }
                                for (int k_index = 0; k_index < all_klausuren.size(); k_index++) {
                                    if (k != k_index && k_2 != k_index) {
                                        implication_list.add(all_literals[k_index][t][r]);
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

    private static List<BoolExpr> mkNoKlausurSplit (BoolExpr[][][] all_literals, List<Klausur> all_klausuren, List<Termin> all_termine, List<Raum> all_raueme, Context ctx, HashMap <Integer, Integer> klausuren_spliting_map)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        //List<Klausur> already_planted = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for(int k = 0; k < all_klausuren.size(); k++) {
            if (klausuren_spliting_map.get(k).intValue() == 1){
                for (int t = 0; t < all_termine.size(); t++) {
                    for (int r = 0; r < all_raueme.size(); r++) {
                        if (all_klausuren.get(k).getTeilnehmer() <= all_raueme.get(r).getKapazitaet() && !all_termine.get(t).getRaum().contains(all_raueme.get(r))) {
                            klausur_is_written_once.add(all_literals[k][t][r]);
                            for (int t_index = 0; t_index < all_termine.size(); t_index++) {
                                for (int r_index = 0; r_index < all_raueme.size(); r_index++) {
                                    if (t != t_index || r != r_index) {
                                        implication_list.add(all_literals[k][t_index][r_index]);
                                    }
                                }
                            }
                            for (int k_index = 0; k_index < all_klausuren.size(); k_index++) {
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
                temp_array = new BoolExpr[klausur_is_written_once.size()];
                temp_array = klausur_is_written_once.toArray(temp_array);
                ret.add(ctx.mkOr(temp_array));
                klausur_is_written_once.clear();
            }
        }
        return ret;
    }

    private static List<BoolExpr> mkKlausurSplitTwoRooms (BoolExpr[][][] all_literals, List<Klausur> all_klausuren, List<Termin> all_termine, List<Raum> all_raeume, Context ctx, HashMap <Integer, Integer> klausuren_spliting_map)throws TestFailedException, Z3Exception {
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for (int k = 0; k < all_klausuren.size(); k++) {
            if (klausuren_spliting_map.get(k).intValue() == 2){
                for (int t = 0; t < all_termine.size(); t++) {
                    for (int r_1 = 0; r_1 < all_raeume.size(); r_1++) {
                        if (all_klausuren.get(k).getTeilnehmer() >= all_raeume.get(r_1).getKapazitaet() && !all_termine.get(t).getRaum().contains(all_raeume.get(r_1))) {
                            for (int r_2 = 0; r_2 < all_raeume.size(); r_2++) {
                                if (r_1 != r_2 && all_klausuren.get(k).getTeilnehmer() <= all_raeume.get(r_1).getKapazitaet() + all_raeume.get(r_2).getKapazitaet() && !all_termine.get(t).getRaum().contains(all_raeume.get(r_2))) {
                                    BoolExpr temp = ctx.mkAnd(all_literals[k][t][r_1], all_literals[k][t][r_2]);
                                    klausur_is_written_once.add(temp);
                                    for (int t_index = 0; t_index < all_termine.size(); t_index++) {
                                        for (int r_index = 0; r_index < all_raeume.size(); r_index++) {
                                            if (t != t_index || (r_1 != r_index && r_2 != r_index)) {
                                                implication_list.add(all_literals[k][t_index][r_index]);
                                            }
                                        }
                                    }
                                    for (int k_index = 0; k_index < all_klausuren.size(); k_index++) {
                                        if (k != k_index) {
                                            implication_list.add(all_literals[k_index][t][r_2]);
                                            implication_list.add(all_literals[k_index][t][r_1]);
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

    private static List<BoolExpr> mkKlausurSplitTreeRooms (BoolExpr[][][] all_literals, List<Klausur> all_klausur, List<Termin> all_termine, List<Raum> all_raeume, Context ctx, HashMap <Integer, Integer> klausuren_spliting_map)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> klausur_is_written_once = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[] temp_array;//Used to create arrays out of lists.
        //---------------Declaration end---------------------------
        for(int k = 0; k < all_klausur.size(); k++){
            if (klausuren_spliting_map.get(k).intValue() == 3){
                for (int t = 0; t < all_termine.size(); t++) {
                    for (int r_1 = 0; r_1 < all_raeume.size(); r_1++) {
                        if (all_klausur.get(k).getTeilnehmer() >= all_raeume.get(r_1).getKapazitaet() && !all_termine.get(t).getRaum().contains(all_raeume.get(r_1))) {
                            for (int r_2 = 0; r_2 < all_raeume.size(); r_2++) {
                                if (r_1 != r_2 && all_klausur.get(k).getTeilnehmer() >= all_raeume.get(r_1).getKapazitaet() + all_raeume.get(r_2).getKapazitaet() && !all_termine.get(t).getRaum().contains(all_raeume.get(r_2))) {
                                    for (int r_3 = 0; r_3 < all_raeume.size(); r_3++) {
                                        if (r_1 != r_2 && r_2 != r_3 && r_1 != r_3 && all_klausur.get(k).getTeilnehmer() <= all_raeume.get(r_1).getKapazitaet() + all_raeume.get(r_2).getKapazitaet() + all_raeume.get(r_3).getKapazitaet()
                                                && !all_termine.get(t).getRaum().contains(all_raeume.get(r_3))) {
                                            BoolExpr temp = ctx.mkAnd(all_literals[k][t][r_1], all_literals[k][t][r_2], all_literals[k][t][r_3]);
                                            klausur_is_written_once.add(temp);
                                            for (int t_index = 0; t_index < all_termine.size(); t_index++) {
                                                for (int r_index = 0; r_index < all_raeume.size(); r_index++) {
                                                    if (t != t_index || (r_1 != r_index && r_2 != r_index && r_3 != r_index)) {
                                                        implication_list.add(all_literals[k][t_index][r_index]);
                                                    }
                                                }
                                            }
                                            for (int k_index = 0; k_index < all_klausur.size(); k_index++) {
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

    private static Model no_split(BoolExpr[][][] all_literals, List<Klausur> all_klausuren, List<Termin> termin, List<Raum> raum, Context ctx)throws TestFailedException, Z3Exception{
        List<BoolExpr> formulas = new LinkedList<>();
        List<BoolExpr> part_formulas;
        List<Klausur> klausur_not_split = new LinkedList<>();
        List<Klausur> klausur_must_merg = new LinkedList<>();
        Solver s = ctx.mkSolver();
        HashMap <Integer, Integer> klausuren_spliting_map = new HashMap<>();
        Random ran = new Random();

        for(Klausur k : all_klausuren){
            if(k.getTeilnehmer() <= 5){
                klausur_must_merg.add(k);
            }else{
                klausur_not_split.add(k);
            }
        }
        int x = ran.nextInt(klausur_must_merg.size());
        if(!(klausur_must_merg.size() % 2 == 0)){
            klausur_not_split.add(klausur_must_merg.remove(x));
        }
        klausur_not_split.removeAll(klausur_must_merg);

        for(int k = 0; k < all_klausuren.size(); k++){
            if(klausur_must_merg.contains(all_klausuren.get(k))){
                klausuren_spliting_map.put(k, 4);
            }else{
                klausuren_spliting_map.put(k, 1);
            }
        }

        part_formulas = mkMerge(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
        formulas.addAll(part_formulas);
        part_formulas = mkNoKlausurSplit(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
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

    private static Model split_two_no_split(BoolExpr[][][] all_literals, List<Klausur> all_klausuren, List<Termin> termin, List<Raum> raum, Context ctx)throws TestFailedException, Z3Exception{
        List<BoolExpr> formulas = new LinkedList<>();
        List<BoolExpr> part_formulas = new LinkedList<>();
        List<Klausur> klausur_not_split = new LinkedList<>();
        klausur_not_split.addAll(all_klausuren);
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
            for(int k = 0; k < all_klausuren.size(); k++){
                if(klausur_must_split_two.contains(all_klausuren.get(k))){
                    klausuren_spliting_map.put(k, 2);
                }else if(klausur_not_split.contains(all_klausuren.get(k))){
                    klausuren_spliting_map.put(k, 1);
                }else{
                    klausuren_spliting_map.put(k, 4);
                }
            }
            part_formulas = mkMerge(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkNoKlausurSplit(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkKlausurSplitTwoRooms(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
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

    private static Model split_two_split_tree_no_split(BoolExpr[][][] all_literals, List<Klausur> all_klausuren, List<Termin> termin, List<Raum> raum, Context ctx)throws TestFailedException, Z3Exception{
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

        for(Klausur k : all_klausuren){
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
            for (int k = 0; k < all_klausuren.size(); k++) {
                if(klausur_must_split_tree.contains(all_klausuren.get(k))){
                    klausuren_spliting_map.put(k, 3);
                }else if(klausur_must_split_two.contains(all_klausuren.get(k))){
                    klausuren_spliting_map.put(k, 2);
                }else if(klausur_must_no_split.contains(all_klausuren.get(k))){
                    klausuren_spliting_map.put(k, 1);
                }else{
                    klausuren_spliting_map.put(k, 4);
                }
            }
            part_formulas = mkMerge(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkNoKlausurSplit(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkKlausurSplitTwoRooms(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            part_formulas = mkKlausurSplitTreeRooms(all_literals, all_klausuren, termin, raum, ctx, klausuren_spliting_map);
            formulas.addAll(part_formulas);
            s.reset();
            for(BoolExpr b : formulas){
                s.add(b);
            }
            if (s.check() != Status.UNSATISFIABLE) {
                System.out.println("GESCHAFFT!");
                return s.getModel();
            }else if(klausur_must_no_split.size() + klausur_must_split_two.size() + klausur_must_split_tree.size() == all_klausuren.size()){
                end = true;
            }
        }
        return null;
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
            int dauer = Integer.parseInt(line[1]);
            int teilnehmer = Integer.parseInt(line[2]);
            String[] datum = line[3].split("\\.");
            String[] zeit = line[4].split(":");
            //Date date = null;
            String[] studiengang = null;
            if(line.length >= 6){
                studiengang = line[5].split(" ");
            }
            Date date = new Date(Integer.parseInt(datum[2]),Integer.parseInt(datum[1]),Integer.parseInt(datum[0]),
                   Integer.parseInt(zeit[0]),Integer.parseInt(zeit[1]));
            Klausur klausur = new Klausur(name,dauer,teilnehmer,date);
            if(studiengang != null){
                for(String s : studiengang){
                    klausur.addStudiengang(s);
                }
            }
            ret.add(klausur);
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
            line = temp.split(",");
            String[] raumname = null;
            String name = line[0];
            if(line.length > 1){
                raumname = line[1].split(" ");
            }
            Termin termin = new Termin(name);
            if(raumname != null){
                for (Raum ra : raum){
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
        return ret;
    }

    private static void mkPlan(Model model, List<Klausur> all_klausuren, List<Termin> all_termine, List<Raum> all_raeume){
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
            for(Klausur k : all_klausuren){
                if(k.getName().equals(temp[0])){
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
            if(planklausur != null && plantermin != null && planraum != null){
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
        String[][] klausurplan = new String[all_klausuren.size()+1][all_termine.size()+1];
        for(int k = 0; k < all_klausuren.size(); k++){
            klausurplan[k+1][0] = all_klausuren.get(k).getName();
        }
        for(int t = 0; t < all_termine.size(); t++){
            klausurplan[0][t+1] = all_termine.get(t).getName();
        }

        for(int k = 0; k < all_klausuren.size(); k++){
            HashMap<Termin, List<Raum>> temp = all_klausuren.get(k).getTerminmap();
            for(Termin t : temp.keySet()){
                for(int t_2 = 0; t_2 < all_termine.size(); t_2++){
                    if(t.equals(all_termine.get(t_2))){
                        for(Raum r : temp.get(t)){
                            klausurplan[k+1][t_2+1] += r.getName() + " ";
                            System.out.println(all_klausuren.get(k).getName() + " findet im Raum " + r.getName() + " zum Termin " + t.getName() + " Statt.");
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