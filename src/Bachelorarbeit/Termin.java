package Bachelorarbeit;

/**
 * Created by Poggi on 14.05.2017.
 */
public class Termin {

    private Klausur klausur;
    private Raum raum = null;
    private String Datum;
    private int freieplaetze;
    private String name;

    public Termin(String n){
        this.name = n;
    }

    public Termin(String n, Raum r){
        this.name = n;
        this.raum = r;
    }

    public String getName(){
        return name;
    }

    public Klausur getKlausur() {
        return klausur;
    }

    public Raum getRaum() {
        return raum;
    }

    public String getDatum(){
        return Datum;
    }

    public boolean isFree(){
        if(raum == null){
            return true;
        }else{
            return false;
        }
    }
}