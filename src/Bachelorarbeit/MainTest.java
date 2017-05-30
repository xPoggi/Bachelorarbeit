package Bachelorarbeit;

import org.jboss.arquillian.container.test.api.Deployment;
import org.jboss.arquillian.junit.Arquillian;
import org.jboss.shrinkwrap.api.ShrinkWrap;
import org.jboss.shrinkwrap.api.asset.EmptyAsset;
import org.jboss.shrinkwrap.api.spec.JavaArchive;
import org.junit.runner.RunWith;

import static org.junit.Assert.*;

/**
 * Created by Poggi on 24.05.2017.
 */
@RunWith(Arquillian.class)
public class MainTest {
    @org.junit.Test
    public void main() throws Exception {
    }

    @org.junit.Test
    public void checkModel() throws Exception {
    }

    @org.junit.Test
    public void mkConstrains() throws Exception {
    }

    @org.junit.Test
    public void readFilesKlausur() throws Exception {
    }

    @org.junit.Test
    public void readFilesRaume() throws Exception {
    }

    @org.junit.Test
    public void readFilesTermin() throws Exception {
    }

    @org.junit.Test
    public void printKlausuren() throws Exception {
    }

    @org.junit.Test
    public void printRaeume() throws Exception {
    }

    @Deployment
    public static JavaArchive createDeployment() {
        return ShrinkWrap.create(JavaArchive.class)
                .addClass(Main.class)
                .addAsManifestResource(EmptyAsset.INSTANCE, "beans.xml");
    }
}
