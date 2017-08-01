package Bachelorarbeit;

import java.util.*;

/**
 * Created by Poggi on 14.05.2017.
 * Planning-program for FH-Luebeck
 */
public class Termin {

    private List<Raum> raeume = new LinkedList<>();
    private String name;

    public Termin(String n){
        this.name = n;
    }

    public String getName(){
        return name;
    }

    public List<Raum> getRaum() {
        return raeume;
    }

    public void addRaum (Raum r){
        raeume.add(r);
    }

    @Override
    public String toString() {
        return "Termin: " + this.name;
    }
}