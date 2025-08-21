package microb;
/*
 * synchronized blocks containing method calls with different lock
 */

public class MB30 {
	public static void main(String[] args) throws InterruptedException {
		T30 t = new T30();
		MB30 m = new MB30();
		t.start();
		System.out.println("BM");
		synchronized(m) {
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
class T30 extends Thread{
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
