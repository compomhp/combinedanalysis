package microb;
/*
 * one successful one unsuccessful must check synchronized
 */
public class MB37 {
	public static void main(String[] args) throws InterruptedException {
		T37 t = new T37();
		MB36 m = new MB36();
		t.start();
		synchronized(t){
			System.out.println("B");
			foo();
		}
		synchronized(m){
			System.out.println("D");
			
		}
		t.join();
	}
	static void foo() {
		System.out.println("A");
	}
}
class T37 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println("C");
		}
	}
}
