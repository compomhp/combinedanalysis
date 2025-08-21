package microb;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;
/*
 * simple ForkJoin execute
 */
public class MB47 {
    public static void main(String[] args) {
        
        int[] array = new int[100];
        for (int i = 0; i < array.length; i++) {
            array[i] = i + 1; 
        }

        // Create ForkJoinPool
        ForkJoinPool pool = new ForkJoinPool();

        // Create task
        SumTask2 task = new SumTask2(array, 0, array.length);

        pool.execute(task); // Using submit() and join()

//        System.out.println("Sum: " + result);

        // Shutdown pool
        pool.shutdown();
    }
}

class SumTask2 extends RecursiveTask<Long> {
    private static final int THRESHOLD = 10; // Task split threshold
    private final int[] array;
    private final int start, end;

    public SumTask2(int[] array, int start, int end) {
        this.array = array;
        this.start = start;
        this.end = end;
    }

    @Override
    protected Long compute() {
        if (end - start <= THRESHOLD) {
            // Small task, compute directly
            long sum = 0;
            for (int i = start; i < end; i++) {
                sum += array[i];
            }
            return sum;
        } else {
            // Split task into two subtasks
            int mid = (start + end) / 2;
            SumTask leftTask = new SumTask(array, start, mid);
            SumTask rightTask = new SumTask(array, mid, end);

            // Fork (execute asynchronously)
            leftTask.fork();
            rightTask.fork();

            // Join results
            return leftTask.join() + rightTask.join();
        }
    }
}

