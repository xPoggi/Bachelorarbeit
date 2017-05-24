package Bachelorarbeit;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.Z3_ast_print_mode;

import java.io.*;
import java.util.*;

/**
 * Created by Poggi on 19.04.2017.
 */

public class Main{
    public static void main(String[] args) throws Z3Exception, IOException, TestFailedException, addFailExeption{
        //Daten einlesen.
        List<Klausur> klausuren = readFilesKlausur("Klausur.csv");
        List<Raum> raume = readFilesRaume("Raum.csv");
        List<Termin> termin = readFilesTermin("Termin.csv");

        //Z3 Context erstellen um SAT-Solver Nutzen zu können.
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("Model", "true");
        Context ctx = new Context(cfg);
        //Z3 Ausgabe umstellen.(nicht mehr SMT sondern einfache Variablen mit deren boolischen Werten)
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL);

        List<BoolExpr> planung = mkConstrains(klausuren, raume, termin, ctx);
        System.out.println(checkModel(planung, ctx));
    }

    public static Model checkModel(List<BoolExpr> formulas, Context ctx) throws Z3Exception, TestFailedException{
        Solver s = ctx.mkSolver();
        s.reset();

        for(BoolExpr b : formulas){
            s.add(b);
        }

        if(s.check() != Status.SATISFIABLE){
            throw new TestFailedException();
        }else{
            return s.getModel();
        }
    }

    public static List<BoolExpr> mkConstrains (List<Klausur> klausur, List<Raum> raum,List<Termin> termin, Context ctx)throws TestFailedException, Z3Exception{
        List<BoolExpr> ret = new LinkedList<BoolExpr>();
        List<BoolExpr> klausurlist = new LinkedList<BoolExpr>();
        List<BoolExpr> andlist = new LinkedList<BoolExpr>();
        List<BoolExpr> orlist = new LinkedList<BoolExpr>();
        List<BoolExpr> impllist = new LinkedList<BoolExpr>();
        BoolExpr[][][] literals = new BoolExpr[klausur.size()][raum.size()][termin.size()];

        int m = 0, l, k;
        for(Klausur a : klausur){
            l = 0;
            for(Raum b: raum){
                k = 0;
                for(Termin c : termin){
                    BoolExpr temp = ctx.mkBoolConst(a.getName()+"_"+b.getName()+"_"+c.getName());
                    andlist.add(temp);
                    orlist.add(temp);
                    literals[m][l][k] = temp;
                    k++;
                }
                l++;
            }
            m++;
            BoolExpr[] tm = new BoolExpr[orlist.size()];
            tm = orlist.toArray(tm);
            klausurlist.add(ctx.mkOr(tm));
            orlist.clear();
        }
        BoolExpr[] tempand = new BoolExpr[klausurlist.size()];
        tempand = klausurlist.toArray(tempand);
        ret.add(ctx.mkAnd(tempand));

        for(m = 0; m < klausur.size(); m++){
            for(l = 0; l < raum.size(); l++){
                for(k = 0; k < termin.size(); k++){
                    BoolExpr[] temparr = new BoolExpr[raum.size()*termin.size()-1+klausur.size()-1];
                    int index = 0;
                    for(int ra = 0; ra < raum.size(); ra++){
                        for(int te = 0; te < termin.size(); te++){
                            if(ra != l || te != k){
                                temparr[index] = literals[m][ra][te];
                                index++;
                            }
                        }
                    }
                    for(int kla = 0; kla < klausur.size(); kla++){
                        if(kla != m){
                            temparr[index] = literals[kla][l][k];
                            index++;
                        }
                    }
                    impllist.add(ctx.mkImplies(literals[m][l][k], ctx.mkNot(ctx.mkOr(temparr))));
                }
            }
        }

        for(BoolExpr imp : impllist){
            ret.add(imp);
        }

        return ret;
    }

    public static List<Klausur> readFilesKlausur(String file) throws IOException{
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        List<Klausur> ret = new LinkedList<Klausur>();
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

    public static List<Raum> readFilesRaume(String file) throws IOException{
        FileReader f = new FileReader(file);
        BufferedReader r = new BufferedReader(f);
        String[] line;
        List<Raum> ret = new LinkedList<Raum>();
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

    public static List<Termin> readFilesTermin(String file) throws IOException{
        List<Termin> ret = new LinkedList<Termin>();
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

    public static void printKlausuren(List<Klausur> list){
        for(Klausur k : list){
            System.out.println(k);
        }
        return;
    }

    public static void printRaeume(List<Raum> list){
        for(Raum r : list){
            System.out.println(r);
        }
        return;
    }
}