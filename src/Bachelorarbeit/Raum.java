package Bachelorarbeit;

/**
 * Created by Poggi on 21.04.2017.
 * Planning-program for FH-Luebeck
 */
public class Raum {

    private String Name; //Name des Raumes.
    private String nummer; //Nummer des Raumes.
    private int Kapazitaet;

    /**
     * Erstellt einen Raum mit Namen und Nummer
     * @param RaumName Name des Raumes (String)
     * @param RaumNummer Nummer des Raumes (int)
     */
    public Raum(String RaumName, String RaumNummer, int Kapazitaet){
        this.Name = RaumName;
        this.nummer = RaumNummer;
        this.Kapazitaet = Kapazitaet;
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

    public String toString(){
        return "Raum: " + this.Name + "\t Raumnummer: " + this.nummer + "\t Kapazitaet: " + this.Kapazitaet;
    }
}