package microb;
/*
 * successful must check call site of synchronized 
 * foo statements will not MHP inside monitor
 */
public class MB35 {
	public static void main(String[] args) throws InterruptedException {
		T35 t = new T35();
		t.start();
		synchronized(t){
			System.out.println("B");
			foo();
		}
		t.join();
	}
	static void foo() {
		System.out.println("A");
	}
}
class T35 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println("C");
		}
	}
}