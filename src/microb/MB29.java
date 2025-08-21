package microb;
/*
 * synchronized blocks containing method calls with same lock
 */

public class MB29 {
	public static void main(String[] args) throws InterruptedException {
		T29 t = new T29();
		t.start();
		System.out.println("BM");
		synchronized(t) {
			System.out.println("M");
			bar();
		}
		System.out.println("RM");
		t.join();
	}
	static void bar() {
		System.out.println("bar");
	}
}
class T29 extends Thread{
	public void run() {
		System.out.println("BR");
		synchronized(this) {
			System.out.println("R");
		}
		System.out.println("AR");
	}
	void foo() {
		System.out.println("foo");
	}
}
