package Bachelorarbeit;

import java.util.*;

/**
 * Created by Poggi on 21.04.2017.
 * Planning-program for FH-Luebeck
 */
public class Klausur {

    private String klausurnummer;
    private String Name; //Name der Klausur
    private int Dauer; //Dauer der Klausur
    private Date Datum;
    private int Teilnehmer;
    private boolean merg;
    private HashMap<Termin, List<Raum>> terminmap = new HashMap<>();
    private Set<String> studiengang = new TreeSet<>();
    private List<String> SBnummer = new LinkedList<>();
    private List<String> wunschTermin = new LinkedList<>();
    private List<String> mussTermin = new LinkedList<>();

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

    public void setMerg(boolean merg){
        this.merg = merg;
    }

    public boolean getMerg(){
        return this.merg;
    }

    public String getKlausurnummer(){
        return this.klausurnummer;
    }

    public void setKlausurnummer(String klausurnummer){
        this.klausurnummer = klausurnummer;
    }

    public List<String> getSBnummer(){
        return this.SBnummer;
    }

    public void addSBnummer (String SBnummer){
        this.SBnummer.add(SBnummer);
    }

    public void addAllSBnummer (List<String>SBnummer){
        for(String s : SBnummer){
            if(!this.SBnummer.contains(s)){
                this.SBnummer.addAll(SBnummer);
            }
        }
    }

    public void addWunschTermin(String wunsch_termin) {
        this.wunschTermin.add(wunsch_termin);
    }

    public void addMussTermin(String muss_termin) {
        this.mussTermin.add(muss_termin);
    }

    public void addAllMussTermin(List<String> mussTermin){
        for(String s : mussTermin){
            if(!this.mussTermin.contains(s)){
                this.mussTermin.addAll(mussTermin);
            }
        }
    }

    public void addAllWunschTermin(List<String> wunschTermin){
        for(String s : wunschTermin){
            if(!this.wunschTermin.contains(s)){
                this.wunschTermin.addAll(wunschTermin);
            }
        }
    }

    public List<String> getWunschTermin() {
        return wunschTermin;
    }

    public List<String> getMussTermin() {
        return mussTermin;
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

    public void addTeilnehmer(int teilnehmer){
        this.Teilnehmer += teilnehmer;
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

    public void addAllStudiengang(Set<String> studiengang){
        for(String s : studiengang){
            if(!this.studiengang.contains(s)){
                this.studiengang.addAll(studiengang);
            }
        }
    }
}