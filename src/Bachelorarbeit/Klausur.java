package Bachelorarbeit;

import java.util.*;

/**
 * Created by Poggi on 21.04.2017.
 * Planning-program for FH-Luebeck
 */
public class Klausur {

    private String klausurnummer; //Nummer der Klausur
    private String Name; //Name der Klausur
    private int Dauer; //Dauer der Klausur
    private int Teilnehmer; //Teilnehmer der Klausur
    private HashMap<Termin, List<Raum>> terminmap = new HashMap<>(); //Map über Termine und Raeume, an denen die Klausur stattfindt.(nur ein Termin vorhanden)
    private Set<String> studiengang = new TreeSet<>(); //Set über Studiengänge
    private List<String> SBnummer = new LinkedList<>(); //Liste über SBnummern(EDV-Nummern) einzigaritg für jede Klausur(kann mehrere beinhalten)
    private List<String> wunschTermin = new LinkedList<>(); //Liste über Wunschtermine, an denen die Klausur stattfinden soll
    private List<String> mussTermin = new LinkedList<>(); //Liste über Musstermine, an denen die Klausur stattfinden muss!
    private String klausurArt; //Art der Klausur(z.B. gleiche Klausur aber unterschiedliche Namen, dann Art gleich)
    private String mergedKlausurnummer;

    /**
     * Erstellt eine Klausur mit bestimmten Parametern.
     * @param KlausurName Name der Klausur
     * @param KlausurDauer Dauer der Klausur
     * @param Teilnehmer Teilnehmer an dieser Klausur
     * @param klausurArt Die Art der Klausur(ob eine Klausur einen anderen Namen hat aber trozdem zu einer Anderen gehört.)
     */
    public Klausur(String KlausurName, int KlausurDauer, int Teilnehmer, String klausurArt, String nummer){
        this.Name = KlausurName;
        this.Dauer = KlausurDauer;
        this.Teilnehmer = Teilnehmer;
        this.klausurArt = klausurArt;
        this.klausurnummer = nummer;
    }

    /**
     *
     * @param nummer
     */
    public void setMergedKlausurnummer(String nummer){
        this.mergedKlausurnummer = nummer;
    }

    /**
     *
     * @return
     */
    public String getMergedKlausurnummer(){
        return this.mergedKlausurnummer;
    }

    /**
     *
     * @return
     */
    public String getKlausurart(){
        return this.klausurArt;
    }

    /**
     * Gibt die Nummer der Klausur zurück.
     * @return String welcher die Nummer der Klausur repräsentiert. Zusammengelegte Klausuren haben die gleiche Nummer.
     */
    public String getKlausurnummer(){
        return this.klausurnummer;
    }

    /**
     * Bearbeitet die Nummer der Klausur.
     * @param klausurnummer Die neue Nummer der Klausur.
     */
    public void setKlausurnummer(String klausurnummer){
        this.klausurnummer = klausurnummer;
    }

    /**
     * Diese Methode gibt die eingetragenen SB-Nummern der Klausur als Liste über Strings zurück
     * @return String-Liste, welche die SB-Nummern der Klausur enthaelt.
     */
    public List<String> getSBnummer(){
        return this.SBnummer;
    }

    /**
     * Fühgt eine SB-Nummer der Liste über SB-Nummern hinzu.
     * @param SBnummer Der String-Wert, der eine Weitere SB-Nummer ist.
     */
    public void addSBnummer (String SBnummer){
        this.SBnummer.add(SBnummer);
    }

    /**
     * Fühgt eine Liste von SB-Nummern dieser Klausur hinzu.
     * @param SBnummer Liste über SB-Nummern, welcher der Klausur hinzugefühgt werden soll.
     */
    public void addAllSBnummer (List<String>SBnummer){
        for(String s : SBnummer){
            if(!this.SBnummer.contains(s)){
                this.SBnummer.add(s);
            }
        }
    }

    /**
     * Fühgt der Klausur einen Wunschtermin hinzu, welcher dem Namen eines Termins entspricht.
     * @param wunschTermin String-Wert mit dem Namen des Termins, zu welcher die Klausur stattfinden soll.
     */
    public void addWunschTermin(String wunschTermin) {
        this.wunschTermin.add(wunschTermin);
    }

    /**
     * Fühgt der Klausur einen Musstermin hinzu, welcher dem Namen eines Termins entspricht.
     * @param mussTermin String-Wert mit dem Namen des Termins, zu welcher die Klausur stattfinden muss.
     */
    public void addMussTermin(String mussTermin) {
        this.mussTermin.add(mussTermin);
    }

    /**
     * Fühgt eine Liste aus Strings, welche Namen von Mussterminen repraesentieren, der Klausur hinzu.
     * @param mussTermin Stringliste mit Werten von Mussterminnamen, welche der Klausur hinzugefügt werden.
     */
    public void addAllMussTermin(List<String> mussTermin){
        for(String s : mussTermin){
            if(!this.mussTermin.contains(s)){
                this.mussTermin.add(s);
            }
        }
    }

    /**
     * Fühgt eine Liste aus Strings, welche Namen von Wunschterminen repraesentieren, der Klausur hinzu.
     * @param wunschTermin Stringliste mit Werten von Wunschterminnamen, welche der Klausur hinzugefügt werden.
     */
    public void addAllWunschTermin(List<String> wunschTermin){
        for(String s : wunschTermin){
            if(!this.wunschTermin.contains(s)){
                this.wunschTermin.add(s);
            }
        }
    }

    /**
     * Gibt die Liste der Wunschtermine zurück.
     * @return Liste über Strings, welche Namen der Wunschtermine enthält.
     */
    public List<String> getWunschTermin() {
        return wunschTermin;
    }

    /**
     * Gibt die Liste der Musstermine zurück.
     * @return Liste über Strings, welche Namen der Musstermine enthält.
     */
    public List<String> getMussTermin() {
        return mussTermin;
    }

    /**
     * Gibt ein Set von Studiengängen zurück, welches beschreibt zu welchem Studiengang diese Klausur gehört.
     * @return Set über Strings, welche den Studiengang dieser Klausur beschriben.
     */
    public Set<String> getStudiengang(){
        return this.studiengang;
    }

    /**
     * Gibt den Namen der Klausur zurück.
     * @return String-Wert, welcher den Namen der Klausur wiederspiegelt.
     */
    public String getName() {
        return this.Name;
    }

    /**
     * Gibt die Dauer der Klausur zurück.
     * @return Integer-Wert, welcher die Dauer der Klausur in Minuten beschreibt.
     */
    public int getDauer(){
        return this.Dauer;
    }

    /**
     * Fügt einer Klausur weitere Teilnehmer hinzu.
     * @param teilnehmer Integer-Wert, welcher eine Anzahl von Teilnehmer ist und auf die vorhandenen Teilnehmer addiert wird.
     */
    public void addTeilnehmer(int teilnehmer){
        this.Teilnehmer += teilnehmer;
    }

    /**
     * Gibt die Anzahl an Teilnehmern der Klausur zurück.
     * @return Integer-Wert, welcher die Anzahl an Teilnehmern einer Klausur beschreibt.
     */
    public int getTeilnehmer() {
        return Teilnehmer;
    }

    /**
     * Gibt eine Hashmap zurück, in welcher die zugeordneten Raeume und Termine entahlten sind.
     * @return HashMap über Termine und Raeume, welche dieser Klausur zugeordnet wurden.
     */
    public HashMap<Termin, List<Raum>> getTerminmap() {
        return terminmap;
    }

    /**
     * Fügt der Hashmap ein Termin hinzu, welcher der Klausur zugeteilt wurde.
     * @param t Termin, an welcher die Klausur stattfindt.
     */
    public void addTermin (Termin t){
        terminmap.put(t, new LinkedList<Raum>());
    }

    /**
     * Fügt einen geplanten Raum einer Klausur hinzu.
     * @param t Termin, zu welchem die Klausur stattfindt, wird gebraucht um diesen in der Hashmap zu finden.
     * @param r Raum, in dem die Klausur stattfindt.
     */
    public void addRaum (Termin t, Raum r){
        terminmap.get(t).add(r);
    }

    /**
     * Fügt einer Klausur einen Studiengang hinzu.
     * @param s String-Wert, welcher dem Studiengang entspricht, der hinzugefügt wird.
     */
    public void addStudiengang(String s){
        studiengang.add(s);
    }

    /**
     * Fügt einer Klausur eine Liste aus Studiengängen hinzu.
     * @param studiengang Stringliste, welche Studiengänge repraesentieren.
     */
    public void addAllStudiengang(Set<String> studiengang){
        for(String s : studiengang){
            if(!this.studiengang.contains(s)){
                this.studiengang.add(s);
            }
        }
    }

    /**
     *
     * @return
     */
    public String toString(){
        return "Klausur: " + this.Name + "\tTeilnehmer: " + this.Teilnehmer + " " + "\tDauer: " + this.Dauer;
    }
}