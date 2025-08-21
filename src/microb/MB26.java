package microb;
/*
 * start join with synchronized different lock
 * expected: monitor would fail
 */
public class MB26 {
	public static void main(String[] args) throws InterruptedException {
		T26 t = new T26();
		t.start();
		System.out.println("14");
		synchronized(t) {
			System.out.println("13");
		}
		System.out.println("15");
		t.join();
		
	}

}
class T26 extends Thread{
	public void run() {
		System.out.println("11");
		MB26 m = new MB26();
		synchronized(m) {
			System.out.println("12");
		}
	}
}