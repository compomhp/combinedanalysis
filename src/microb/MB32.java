package microb;
/*
 * unsuccessful must check of join
 * expected: bar is not removed from MHP after join
 */

public class MB32 {
	public static void main(String[] args) throws InterruptedException {
		T32 t = new T32();
		T32.bar();
		t.start();
		System.out.println("BM");
		
		System.out.println("RM");
		t.join();
		System.out.println("After join");
	}
	
}
class T32 extends Thread{
	public void run() {
		bar();
		System.out.println("BR");
		
	}
	static void bar() {
		System.out.println("bar");
	}
}
