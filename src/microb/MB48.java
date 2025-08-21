package microb;
/*
 * Rem sync example
 * a synchs can be removed, if it does not happen in parallel with any other synch.
 * Even if it MHP its lock object is different
 */
public class MB48 {
	public static void main(String[] args) throws InterruptedException {
		T48 t = new T48();
		t.start();
		synchronized(t) {
			System.out.println("sync1");
		}
		t.join();
	}
}
class T48 extends Thread{
	public void run() {
		T48 l = new T48();
		synchronized(this) {
			System.out.println("sync2");
		}
	}
}
