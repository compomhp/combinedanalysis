package microb;
/*
 * Multiple start join
 * expected: MHP follows start join
 */
public class MB20 {
	public static void main(String[] args) throws InterruptedException {
		T20 t1 = new T20();
		T20 t2 = new T20();
		t1.start();
		int i = 10;
		System.out.println(i);
		t1.join();
		i = 20;
		System.out.println(i);
		t2.start();
		i = 30;
		System.out.println(i);
		t2.join();
		i = 40;
		System.out.println(i);
	}

}
class T20 extends Thread{
	public void run() {
		int i = 10;
		System.out.append(":i"+i);
	}
}
