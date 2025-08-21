package microb;
/*
 * unnsuccessful must check join
 * expected: behaves as if no join
 */
public class MB33 {
	public static void main(String[] args) throws InterruptedException {
		T33 t = new T33();
		if(args.length>0) {
			t = new T33();
		}
		t.start();
		System.out.println("B");
		t.join();
		System.out.println("C");
	}
}
class T33 extends Thread{
	public void run() {
		System.out.println("A");
	}
}