package microb;
/*
 * start join with multiple synchronized blocks nested
 */
public class MB28 {
	public static void main(String[] args) throws InterruptedException {
		T28 t = new T28();
		t.f = new MB28();
		t.start();
		System.out.println("before S1");
		synchronized(t) {
			System.out.println("S1");
			synchronized(t.f) {
				System.out.println("S2");
			}
			System.out.println("S1_1");
		}
		System.out.println("after S1");
		t.join();
	}
}
class T28 extends Thread{
	MB28 f;
	public void run() {
		System.out.println("before R1");
		synchronized(this) {
			System.out.println("R1");
			synchronized(this.f) {
				System.out.println("R2");
			}
			System.out.println("R1_1");
		}
		System.out.println("after R1");
	}
}
