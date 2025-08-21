package microb;
/*
 * simple wait notify with notify having some MHP but notify does not MHP wait
 * expected: The notify becomes MHP predecessor and its MHP flows
 * to wait successor. But only when notify runs in parallel with wait.
 * Here wait does not MHP with notify. So notify's MHP doesnot flow
 * to wait's successors
 * 
 */
public class MB40 {
	public static void main(String[] args) throws InterruptedException {
		T40 t = new T40();
		T40_1 t2 = new T40_1();
		t.start();
		t2.start();
		synchronized(t) {
			System.out.println("Before notify");
			t.notify();
			System.out.println("After notify");
		}
		t2.join();
		t.join();
	}
}
class T40 extends Thread{
	public void run() {
		synchronized(this) {
			try {
				System.out.println("Before wait");
				this.wait();
				System.out.println("After wait");
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		}
	}
}
class T40_1 extends Thread{
	public void run() {
		System.out.println("notify parallel");
	}
}