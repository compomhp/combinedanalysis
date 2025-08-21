package microb;
/*
 * simple wait notify with failed statement must check
 * wait runs in parallel with all sync stmts and with unsuccessful must check
 * As must check fails, statements added to wait will flow to successors without getting
 * eliminated
 */
public class MB44 {
	public static void main(String[] args) throws InterruptedException {
		T44 t = new T44();
		
		
		MB44 m=new MB44();
		m.foo();
		t.f = m;
		
		
		t.start();
		
		System.out.println("Before sync main");
		synchronized(m) {
			System.out.println("Before wait");
			m.wait();
			m.foo();
		}
		System.out.println("After sync main");
		t.join();
		
	}
	void foo() {
		System.out.println("After wait");
	}
}
class T44 extends Thread{
	MB44 f;
	public void run() {
		System.out.println("Before sync run");
		synchronized(f) {
			System.out.println("Before notify");
			f.notify();
			System.out.println("After notify");
		}
		System.out.println("After sync run");
	}
}