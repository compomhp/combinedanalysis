package microb;
/*
 * Nested start join
 * expected: After 1st start only run of one class run in parallel and after 2 starts all MHP
 * After 1 join 1 run is removed, after 2 joins all MHP removed
 */
public class MB21 {
	public static void main(String[] args) throws InterruptedException {
		T21 t1 = new T21();
		T21_1 t2 = new T21_1();
		t1.start();
		System.out.println(6);
		t2.start();
		System.out.println(7);
		t2.join();
		System.out.println(8);
		t1.join();
		System.out.println(9);
	}

}
class T21 extends Thread{
	public void run() {
		System.out.println(10);
	}
}
class T21_1 extends Thread{
	public void run() {
		System.out.println(11);
	}
}