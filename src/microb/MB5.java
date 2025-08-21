package microb;
/*
 * simple start join
 * expected: stmts between start, join MHP run method
 */
public class MB5 {
	public static void main(String[] args) throws InterruptedException {
		T5 t = new T5();
		t.start();
		int i = 0;
		System.out.println(i);
		t.join();
	}
}
class T5 extends Thread{
	public void run() {
		int k = 1;
		System.out.println(k);
	}
}
