package microb;
/*
 * multiple wait notify
 * expected: Both waits will MHP sync statements
 */
public class MB39 {
	public static void main(String[] args) throws InterruptedException {
		T39 t = new T39();
		t.start();
		System.out.println("Before sync main");
		synchronized(t) {
			System.out.println("Before wait");
			t.wait();
			System.out.println("After wait");
			t.wait();
			System.out.println("After wait2");
		}
		System.out.println("After sync main");
		t.join();
	}
}
class T39 extends Thread{
	public void run() {
		System.out.println("Before sync run");
		synchronized(this) {
			System.out.println("Before notify");
			this.notify();
			System.out.println("After notify");
		}
		System.out.println("After sync run");
	}
}
