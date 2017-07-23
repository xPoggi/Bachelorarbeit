package Bachelorarbeit;

import java.util.*;

/**
 * Created by Poggi on 21.04.2017.
 */
public class Klausur {

    private String Name; //Name der Klausur
    private int Dauer; //Dauer der Klausur
    private Date Datum;
    private int Teilnehmer;
    private HashMap<Termin, List<Raum>> terminmap = new HashMap<>();
    private Set<String> studiengang = new TreeSet<>();

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
    }

    public Set<String> getStudiengang(){
        return this.studiengang;
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

    public String toString(){
        return "Klausur: " + this.Name + "\tTeilnehmer: " + this.Teilnehmer + "\tDatum: "
                + this.getDatum() + "\tBeginn: " +this.getKlausurStart() + " " + "\tDauer: " + this.getDauer();
    }

    public HashMap<Termin, List<Raum>> getTerminmap() {
        return terminmap;
    }

    public void addTermin (Termin t){
        terminmap.put(t, new LinkedList<Raum>());
    }

    public void addRaum (Termin t, Raum r){
        terminmap.get(t).add(r);
    }

    public void addStudiengang(String s){
        studiengang.add(s);
    }
}