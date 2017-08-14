package Bachelorarbeit;

/**
 * Created by Poggi on 12.05.2017.
 */
public class TestFailedException extends Exception{

    /**
     * Exception, welche generiert wird, wenn es nicht möglich ist mit dem Sat-Solver einen Plan zu erstellen.
     */
    public TestFailedException(){
        super("Check FAILED");
        System.err.println("Es konnte kein Plan erstellt werden!");
    }
}
