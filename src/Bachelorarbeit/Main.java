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
        //Daten einlesen.
        List<Klausur> klausuren = readFilesKlausur(args[0]);
        List<Termin> termin = readFilesTermin(args[1]);
        List<Raum> raume = readFilesRaume(args[2]);

        //Z3 Context erstellen um SAT-Solver Nutzen zu können.
        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("Model", "true");
        Context ctx = new Context(cfg);
        //Z3 Ausgabe umstellen.(nicht mehr SMT sondern einfache Variablen mit deren boolischen Werten)
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL);

        List<BoolExpr> planung = mkConstraints(klausuren, termin, raume, ctx);
        System.out.println(checkModel(planung, ctx));
    }

    private static List<BoolExpr> mkConstraints (List<Klausur> klausur, List<Termin> termin, List<Raum> raum, Context ctx)throws TestFailedException, Z3Exception{
        //---------------Declaration start-------------------------
        List<BoolExpr> ret = new LinkedList<>();
        List<BoolExpr> or_list = new LinkedList<>();
        List<BoolExpr> overall_literals = new LinkedList<>();
        List<BoolExpr> implication_list = new LinkedList<>();
        BoolExpr[][][] all_literals = new BoolExpr[klausur.size()][termin.size()][raum.size()];
        BoolExpr[] temp_array;
        //---------------Declaration end---------------------------

        //---------------Creating or-literals----------------------
        for(int k = 0; k < klausur.size(); k++){
            for(int t = 0; t < termin.size(); t++){
                for(int r = 0; r < raum.size(); r++){
                    BoolExpr temp_literal = ctx.mkBoolConst(klausur.get(k).getName()+"_"+termin.get(t).getName()+"_"+raum.get(r).getName());
                    or_list.add(temp_literal);
                    all_literals[k][t][r] = temp_literal;
                }
            }
            temp_array = new BoolExpr[or_list.size()];
            temp_array = or_list.toArray(temp_array);
            overall_literals.add(ctx.mkOr(temp_array));
            or_list.clear();
        }
        //---------------Creating or-literals end------------------
        //---------------------------------------------------------
        //---------------Creating and-linkage between or's---------
        temp_array = new BoolExpr[overall_literals.size()];
        temp_array = overall_literals.toArray(temp_array);
        ret.add(ctx.mkAnd(temp_array));
        //---------------Creating and-linkage end------------------

        //---------------Creating implications---------------------
        for(int k = 0; k < klausur.size(); k++){
            for(int t = 0; t < termin.size(); t++){
                for(int r = 0; r < raum.size(); r++){
                    temp_array = new BoolExpr[raum.size()*termin.size()-1+klausur.size()-1];
                    int temp_array_index = 0;
                    //implications for Klausur not in other roo's or at other termin
                    //---------------Start---------------------
                    for(int t_index = 0; t_index < termin.size(); t_index++){
                        for(int r_index = 0; r_index < raum.size(); r_index++){
                            if(t != t_index || r != r_index){
                                temp_array[temp_array_index] = all_literals[k][t_index][r_index];
                                temp_array_index ++;
                            }
                        }
                    }
                    //---------------End-----------------------
                    //implications for no Klausur at the same room and termin
                    //---------------Start---------------------
                    for(int k_index = 0; k_index < klausur.size(); k_index ++){
                        if(k != k_index){
                            temp_array[temp_array_index] = all_literals[k_index][t][r];
                            temp_array_index ++;
                        }
                    }
                    //---------------End-----------------------
                    implication_list.add(ctx.mkImplies(all_literals[k][t][r], ctx.mkNot(ctx.mkOr(temp_array))));
                }
            }
        }
        //---------------Creating implications end-----------------
        ret.addAll(implication_list);
        return ret;
    }

    private static Model checkModel(List<BoolExpr> litterals, Context ctx) throws Z3Exception, TestFailedException{
        Solver s = ctx.mkSolver();
        s.reset();

        for(BoolExpr b : litterals){
            s.add(b);
        }

        if(s.check() != Status.SATISFIABLE){
            throw new TestFailedException();
        }else{
            return s.getModel();
        }
    }

    private static BoolExpr checkKlausurSplitt(Klausur k, Termin t, Raum r){
        switch(k.getClassify()){
            case 'A':
            case 'B':
            case 'C':
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
            Date date = new Date(Integer.parseInt(datum[2]),Integer.parseInt(datum[1]),Integer.parseInt(datum[0]),
                    Integer.parseInt(zeit[0]),Integer.parseInt(zeit[1]));
            ret.add(new Klausur(name,dauer,teilnehmer,date));
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
            ret.add(new Raum(name, nummer, kapazitaet));
            temp = r.readLine();
        }
        return ret;
    }

    private static List<Termin> readFilesTermin(String file) throws IOException{
        List<Termin> ret = new LinkedList<>();
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        r.readLine();
        String temp = r.readLine();
        while(temp != null){
            line = temp.split(",");
            String name = line[0];
            ret.add(new Termin(name));
            temp = r.readLine();
        }
        return ret;
    }
}