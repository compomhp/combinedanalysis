package microb;
/*
 * Nested start join with synchronized same lock
 * expected: follows the monitor semantics, perfect
 */
public class MB25 {
	public static void main(String[] args) throws InterruptedException {
		T25 t1 = new T25();
		T25_1 t2 = new T25_1();
		t1.start();
		synchronized(t1) {
			System.out.println(6);
		}
		t2.start();
		synchronized(t2) {
			System.out.println(7);
		}
		t2.join();
		System.out.println(8);
		t1.join();
		System.out.println(9);
	}

}
class T25 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println(10);
		}
	}
}
class T25_1 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println(11);
		}
	}
}
