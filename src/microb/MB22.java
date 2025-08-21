package microb;
/*
 * start join with method call
 * expected: The method call also gets added in the MHP
 */
public class MB22 {
	public static void main(String[] args) throws InterruptedException {
		T22 t = new T22();
		t.start();
		System.out.println(10);
		MB22 m = new MB22();
		m.foo();
		t.join();
	}
	public void foo() {
		System.out.println(12);
	}
}
class T22 extends Thread{
	public void run() {
		System.out.println(11);
	}
	
}