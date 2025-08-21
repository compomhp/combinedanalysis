package microb;
/*
 * Heap update through MHP simple start join
 */
public class MB34 {
	public static void main(String[] args) throws InterruptedException {
		T34 t = new T34();
		t.start();
		t.f = new MB34();
		System.out.println(t.f);
		t.join();
	}

}
class T34 extends Thread{
	MB34 f;
	public void run() {
		f = new MB34();
		System.out.println(f);
	}
}