package Bachelorarbeit;

import java.util.*;

/**
 * Created by Poggi on 14.05.2017.
 * Planning-program for FH-Luebeck
 */
public class Termin {

    private List<Raum> raeume = new LinkedList<>(); //Liste über belegte Raeume eines Termins
    private String name; //Name des Termins
    private String nummer; //Nummer des Termins

    /**
     * Erstellt einen Termin
     * @param n Name des Termins
     */
    public Termin(String n, String nummer){
        this.name = n;
        this.nummer = nummer;
    }

    /**
     *
     * @return
     */
    public String getNummer(){
        return this.nummer;
    }

    /**
     * Gibt den Namen des Termins zurück.
     * @return String-Wert, welcher den Namen des Termins repraesentiert.
     */
    public String getName(){
        return name;
    }

    /**
     * Gibt die Liste der Raeume zurück, welche an dem Termin belegt sind.
     * @return Liste über Raeme, welche an dem Termin belegt sind.
     */
    public List<Raum> getRaum() {
        return raeume;
    }

    /**
     * Fügt einen Raum zu der Belegtliste hinzu.
     * @param r Der Raum, welcher hinzugefügt wird.
     */
    public void addRaum (Raum r){
        raeume.add(r);
    }

    /**
     * Gibt den Terminnamen auf der Console aus.
     * @return String-Wert mit den Informationen über den Termin.
     */
    @Override
    public String toString() {
        return "Termin: " + this.name;
    }
}