package Bachelorarbeit;

/**
 * Created by Poggi on 14.05.2017.
 */
public class Termin {

    private Klausur[] klausur= new Klausur[2];
    private Raum raum;
    private boolean[] zeitslots = new boolean[6];
    private String Datum;
    private int freieplaetze;
    private String name;

    public Termin(String n){
        this.name = n;
    }

    public Termin(Klausur k, Raum r){
        for(int i = 0; i<klausur.length-1; i++) {
            //falls noch eine Klausur Platzt hat und der Raum diese Teilnehmer fassen kann
            //dann fühge dem Termin die Klausur und den Raum hinzu.
            if (klausur[i] == null && r.getKapazitaet() >= k.getTeilnehmer()) {
                klausur[i] = k;
                raum = r;
                this.freieplaetze = (r.getKapazitaet()-k.getTeilnehmer());
                this.Datum = k.getDatum();
                //Bestimmen welcher Zeitslott belegt ist.
                switch (k.getKlausurStart()){
                    case "8:15": zeitslots[0] = true;break;
                    case "10:0": zeitslots[1] = true;break;
                    case "12:0": zeitslots[2] = true;break;
                    case "14:30": zeitslots[3] = true;break;
                    case "156:1": zeitslots[4] = true;break;
                    case "18:0": zeitslots[5] = true;break;
                    default:
                        System.err.println("Zeitslot wurde nicht gefunden.");
                }
            }
        }
    }

    public String getName(){
        return name;
    }

    public boolean[] getZeitSlots() {
        return zeitslots;
    }

    public Klausur[] getKlausur() {
        return klausur;
    }

    public Raum getRaum() {
        return raum;
    }

    public String getDatum(){
        return Datum;
    }

    public boolean addKlausur(Klausur k) throws addFailExeption{
        for(int i = 0; i<klausur.length; i++) {
            if (klausur[i] == null && freieplaetze >= k.getTeilnehmer()) {
                klausur[i] = k;
                this.freieplaetze = freieplaetze - k.getTeilnehmer();
                switch (k.getKlausurStart()){
                    case "8:15": {
                        zeitslots[0] = true;
                        break;}
                    case "10:0": {
                        zeitslots[1] = true;
                        break;}
                    case "12:0": {
                        zeitslots[2] = true;
                        break;}
                    case "14:30": {
                        zeitslots[3] = true;
                        break;}
                    case "16:15": {
                        zeitslots[4] = true;
                        break;}
                    case "18:0": {
                        zeitslots[5] = true;
                        break;}
                    default: throw new addFailExeption();
                }
                return true;
            }
        }
        System.err.println("Klausur Hinzufühgen fehlgeschlagen");
        return false;
    }
}