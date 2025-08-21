package microb;
/*
 * start join with synchronized same lock
 * expected: should follow the monitor semantics
 */
public class MB24 {
	public static void main(String[] args) throws InterruptedException {
		T24 t = new T24();
		t.start();
		System.out.println("14");
		synchronized(t) {
			System.out.println("13");
		}
		System.out.println("15");
		t.join();
		
	}

}
class T24 extends Thread{
	public void run() {
		System.out.println("11");
		synchronized(this) {
			System.out.println("12");
		}
	}
}