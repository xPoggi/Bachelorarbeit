package Bachelorarbeit;

import sun.awt.image.ImageWatched;

import java.util.*;

/**
 * Created by Poggi on 14.05.2017.
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