package Bachelorarbeit;

/**
 * Created by Poggi on 21.04.2017.
 * Planning-program for FH-Luebeck
 */
public class Raum {

    private String Name; //Name des Raumes.
    private String Nummer; //Nummer des Raumes.
    private int Kapazitaet; //Personen die der Raum fassen kann

    /**
     * Erstellt einen Raum mit Namen und Nummer
     * @param RaumName Nummer des Raumes (String)
     * @param Kapazitaet Platz in dem Raum (int)
     */
    public Raum(String RaumName, int Kapazitaet, String Nummer){
        this.Name = RaumName;
        this.Nummer = Nummer;
        this.Kapazitaet = Kapazitaet;
    }

    /**
     * Gibt den Namen des Raumes zurück. (Stirng)
     * @return String-Wert, welcher dem Namen des Raumes entspricht
     */
    public String getName() {
        return this.Name;
    }

    /**
     * Gibt die Nummer des Raumes zurück. (int)
     * @return String-Wert, welcher der Nummer des Raumes entspricht.
     */
    public String getNummer() {
        return this.Nummer;
    }

    /**
     * Gibt die Kapazitaet des Raumes zurück.
     * @return Integer-Wert, welcher der Kapazität des Raumes entspricht
     */
    public int getKapazitaet(){
        return this.Kapazitaet;
    }

    public String toString(){
        return "Raum: " + this.Name + "\t Raumnummer: " + this.Nummer + "\t Kapazitaet: " + this.Kapazitaet;
    }
}