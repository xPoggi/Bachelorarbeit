package Bachelorarbeit;

import java.util.*;

/**
 * Created by Poggi on 21.04.2017.
 */
public class Raum {

    private String Name; //Name des Raumes.
    private String nummer; //Nummer des Raumes.
    private int Kapazitaet;
    private int Besetzt = 0;
    private Klausur[] klausuren;
    private char classify;

    /**
     * Erstellt einen Raum mit Namen und Nummer
     * @param RaumName Name des Raumes (String)
     * @param RaumNummer Nummer des Raumes (int)
     */
    public Raum(String RaumName, String RaumNummer, int Kapazitaet){
        this.Name = RaumName;
        this.nummer = RaumNummer;
        this.Kapazitaet = Kapazitaet;
        this.klausuren = new Klausur[5];
        sortClass();
    }



    /**
     * Gibt den Namen des Raumes zurück. (Stirng)
     * @return
     */
    public String getName() {
        return this.Name;
    }

    /**
     * Gibt die Nummer des Raumes zurück. (int)
     * @return
     */
    public String getNummer() {
        return this.nummer;
    }

    /**
     * @return
     */
    public int getKapazitaet(){
        return this.Kapazitaet;
    }

    /**
     * @return
     */
    public char getClassify(){
        return this.classify;
    }

    /**
     *
     */
    private void sortClass(){
        if(this.Kapazitaet > 0 && this.Kapazitaet <= 25)
            classify = 'A';
        else if(this.Kapazitaet > 25 && this.Kapazitaet <= 50)
            classify = 'B';
        else if(this.Kapazitaet >= 50)
            classify = 'C';
        else classify = 'Z';
        return;
    }

    public String toString(){
        return "Raum: " + this.Name + "\t Raumnummer: " + this.nummer + "\t Kapazitaet: " + this.Kapazitaet;
    }
}