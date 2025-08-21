package microb;
/*
 * simple wait notify with notify having some MHP and notify MHP wait
 * expected: The notify becomes MHP predecessor and its MHP flows
 * to wait successor as notify MHP wait
 * 
 */
public class MB41 {
	public static void main(String[] args) throws InterruptedException {
		T41 t = new T41();
		T41_1 t2 = new T41_1();
		MB41 m = new MB41();
		t.start();
		t2.start();
		synchronized(m) {
			System.out.println("Before notify");
			t.notify();
			System.out.println("After notify");
		}
		t2.join();
		t.join();
	}
}
class T41 extends Thread{
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
class T41_1 extends Thread{
	public void run() {
		System.out.println("notify parallel");
	}
}
