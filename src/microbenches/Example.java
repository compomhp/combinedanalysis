package microbenches;

public class Example{
	public static void main(String args[]) throws InterruptedException{
		LockWrap w1 = new LockWrap();//O2
		w1.k = new MyLock(); //O1
		T t = new T();
		t.w = w1;
		t.start();
		for(int i=0; i<4; i++){
			MyLock mL = w1.k;
			synchronized(mL){ /*B1*/
				w1.k2 = w1.k;
				w1.k1 = new MyLock();//O4
				w1.k = w1.k2;
			}
			} /* end-for */
		t.join();
	}
}
class LockWrap{
	public MyLock k, k1, k2;
}
class MyLock {
}
class T extends Thread{
	LockWrap w;
	public void run(){
		MyLock tL = w.k;
		synchronized(tL){ /*B2*/
			w.k1 = w.k;
			w.k2 = new MyLock(); //O3
			w.k = w.k1;
		}
	}
}