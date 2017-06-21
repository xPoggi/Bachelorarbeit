package Bachelorarbeit;

/**
 * Created by Poggi on 12.05.2017.
 */
public class TestFailedException extends Exception{

    public TestFailedException(){
        super("Check FAILED");
        System.err.println("Es konnte kein Plan erstellt werden!");
    }
}
