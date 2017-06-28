package Bachelorarbeit;

import sun.awt.image.ImageWatched;

import java.util.*;

/**
 * Created by Poggi on 14.05.2017.
 */
public class Termin {

    private Raum raum = null;
    private String name;


    public Termin(String n){
        this.name = n;
    }

    public Termin(String n, Raum r){
        this.name = n;
        this.raum = r;
    }

    public String getName(){
        return name;
    }


    public Raum getRaum() {
        return raum;
    }

    @Override
    public String toString() {
        return "Termin: " + this.name;
    }
}