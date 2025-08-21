package microb;
/*
 * Possible race example
 * Two statements may race if they access same field (heap), 
 * at least one among them is a write (store) and the base variables alias
 * expected: ComPo says no race as they do not MHP while others say a possible race
 */
public class MB49 {
	public static void main(String[] args) throws InterruptedException {
		T49 t = new T49();
		t.start();
		synchronized(t) {
			t.f = new MB49();
		}
		t.join();
	}
}
class T49 extends Thread{
	MB49 f;
	public void run() {
		synchronized(this) {
//			T49 y = new T49();
//			MB49 x = y.f;
			/*
			 * If y.f is used all say no race
			 * as base do not alias
			 */
			MB49 x = this.f;
			System.out.println(x);
		}
	}
}

