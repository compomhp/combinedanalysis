package microb;
/*
 * Nested start join with synchronized different lock
 */
public class MB27 {
	public static void main(String[] args) throws InterruptedException {
		T27 t1 = new T27();
		T27_1 t2 = new T27_1();
		T27 l = new T27();
		t1.start();
		synchronized(l) {
			System.out.println(6);
		}
		t2.start();
		synchronized(l) {
			System.out.println(7);
		}
		t2.join();
		System.out.println(8);
		t1.join();
		System.out.println(9);
	}

}
class T27 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println(10);
		}
	}
}
class T27_1 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println(11);
		}
	}
}
