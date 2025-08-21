package microb;
/*
 * simple wait notify
 * wait runs in parallel with all sync stmts and then sync stmts are
 * removed for its successors
 */
public class MB38 {
	public static void main(String[] args) throws InterruptedException {
		T38 t = new T38();
		t.start();
		System.out.println("Before sync main");
		synchronized(t) {
			System.out.println("Before wait");
			t.wait();
			System.out.println("After wait");
		}
		System.out.println("After sync main");
		t.join();
	}
}
class T38 extends Thread{
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