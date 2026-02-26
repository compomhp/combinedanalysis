package microb;

class Th extends Thread {
  MB51 f;
  public void run() {
    synchronized (f) { // S2
      System.out.println("sync f");
    }
  }
}

class MB51 {
  public static void main(String args[]) throws InterruptedException  {
    Th t = new Th();      // Ot
    MB51 a1 = new MB51(); // O1
    t.f = a1;
    t.start();
    // Non removable synch
    synchronized (a1) { // S1
      System.out.println("sync a1");
    }
//    try {
      t.join();
//    } catch (InterruptedException e) {
//    }

    // Removable synch
    synchronized (a1) { System.out.println("sync a1 again"); }
  }
} 
