package microb;
/*
 * Rem sync example, ComPoMHP better
 * a synchs can be removed, if it does not happen in parallel with any other synch.
 * Even if it MHP its lock object is different
 */
public class MB50 {
	public static void main(String[] args) throws InterruptedException {
		T50 t = new T50();
		t.start();
		
		t.join();
		synchronized(t) {
			System.out.println("sync1");
		}
	}
}
class T50 extends Thread{
	public void run() {
		T50 l = new T50();
		synchronized(this) {
			System.out.println("sync2");
		}
	}
}
