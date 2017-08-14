package Bachelorarbeit;

/**
 * Created by Poggi on 16.05.2017.
 */
public class addFailExeption extends Exception {
    /**
     * Exception, welche erzeugt wird, wenn es nicht möglich ist eine Klausur zu einer Klausurenliste hinzu zufügen.
     */
    public addFailExeption(){
        super("Klausur konnte nicht Hinzugefühgt werden!");
    }
}
