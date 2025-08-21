package microb;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class MB45 {
	public static void main(String[] args) {
		ExecutorService executorService = Executors.newFixedThreadPool(10);

		executorService.execute(new R45());
		System.out.println("Hello executor submit");

		executorService.shutdown();
	}
}
class R45 implements Runnable{
	 public void run() {
	        System.out.println("Asynchronous task");
	    }
}
