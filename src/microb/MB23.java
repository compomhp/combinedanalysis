package microb;
/*
 * start join with method call in run
 * expected: foo statements will also run in parallel with run and bar
 */
public class MB23 {
	public static void main(String[] args) throws InterruptedException {
		T23 t = new T23();
		t.start();
		System.out.println(10);
		foo();
		t.join();
	}
	static void foo() {
		System.out.println(11);
	}
}
class T23 extends Thread{
	public void run() {
		System.out.println(12);
		bar();
	}
	static void bar() {
		System.out.println(13);
	}
}