package microb;
/*
 * simple wait notify with failed varPts must check
 * wait runs in parallel with all sync stmts and with unsuccessful must check
 * As must check fails, statements added to wait will flow to successors without getting
 * eliminated
 */
public class MB42 {
	public static void main(String[] args) throws InterruptedException {
		T42 t = new T42();
		
		
		MB42 m=null;
		int i =2;
		while(i>0) {
		 m = new MB42();
		 i--;
		}
		t.f = m;
		t.start();
		
		System.out.println("Before sync main");
		synchronized(m) {
			System.out.println("Before wait");
			m.wait();
			System.out.println("After wait");
		}
		System.out.println("After sync main");
		t.join();
		
	}
}
class T42 extends Thread{
	MB42 f;
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