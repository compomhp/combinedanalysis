package microb;
/*
 * unsuccessful must check call site of synchronized 
 * foo will not be excluded
 */
public class MB36 {
	public static void main(String[] args) throws InterruptedException {
		T36 t = new T36();
		foo();
		
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
class T36 extends Thread{
	public void run() {
		synchronized(this) {
			System.out.println("C");
		}
	}
}
