package microb;

/*
 * multiple wait notify with unsucessful must check points-to
 * expected: Both waits will MHP sync statements
 */
public class MB43 {
	public static void main(String[] args) throws InterruptedException {
		
		T43 t = new T43();
		int i = 2;
		while(i>0) {
			t = new T43();
			i--;
		}
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
class T43 extends Thread{
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

