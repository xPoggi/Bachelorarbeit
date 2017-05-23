package Bachelorarbeit;

import java.util.Date;

/**
 * Created by Poggi on 21.04.2017.
 */
public class Klausur {

    private String Name; //Name der Klausur
    private int Dauer; //Dauer der Klausur
    private Date Datum;
    private int Teilnehmer;
    private char classify;

    /**
     * Erstellt eine Klausur mit Namen und Dauer.
     * @param KlausurName Name der Klausur (String)
     * @param KlausurDauer Dauer der Klausur (int)
     * @param Datum Datum der Klausur
     * @param Teilnehmer Teilnehmeranzahl der Klausur
     */
    public Klausur(String KlausurName, int KlausurDauer, int Teilnehmer, Date Datum){
        this.Name = KlausurName;
        this.Dauer = KlausurDauer;
        this.Teilnehmer = Teilnehmer;
        this.Datum = Datum;
        sortClass();
    }

    /**
     * Gibt den Namen der Klausur zuruck (String)
     * @return
     */
    public String getName() {
        return this.Name;
    }

    /**
     * Gibt die Dauer der Klausur zurück (int)
     * @return
     */
    public int getDauer(){
        return this.Dauer;
    }

    /**
     *
     * @return
     */
    public int getTeilnehmer() {
        return Teilnehmer;
    }

    /**
     *
     * @return
     */
    public String getDatum() {
        return this.Datum.getDate() + "." + this.Datum.getMonth() + "."+ this.Datum.getYear();
    }

    public String getTime(){
        return this.Datum.getHours() + ":" + this.Datum.getMinutes();
    }

    public String getKlausurStart(){
        return this.Datum.getHours() + ":" + this.Datum.getMinutes();
    }

    public char getClassify(){
        return this.classify;
    }

    private void sortClass(){
        if(this.Teilnehmer > 0 && this.Teilnehmer <= 25)
            classify = 'A';
        else if(this.Teilnehmer > 25 && this.Teilnehmer <= 50)
            classify = 'B';
        else if(this.Teilnehmer >= 50)
            classify = 'C';
        else classify = 'Z';
        return;
    }

    public String toString(){
        return "Klausur: " + this.Name + "\tTeilnehmer: " + this.Teilnehmer + "\tDatum: "
                + this.getDatum() + "\tBeginn: " +this.getKlausurStart() + " " + "\tDauer: " + this.getDauer();
    }
}