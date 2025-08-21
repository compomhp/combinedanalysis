package microb;
/*
 * successful must check of join only one call site
 */

public class MB31 {
	public static void main(String[] args) throws InterruptedException {
		T31 t = new T31();
		t.start();
		System.out.println("BM");
		bar();
		System.out.println("RM");
		t.join();
		System.out.println("After join");
	}
	static void bar() {
		System.out.println("bar");
	}
}
class T31 extends Thread{
	public void run() {
		System.out.println("BR");
		
	}
}
