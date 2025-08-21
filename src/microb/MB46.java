package microb;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;
/*
 * simple ForkJoin submit
 */
public class MB46 {
    public static void main(String[] args) {
        
        int[] array = new int[100];
        for (int i = 0; i < array.length; i++) {
            array[i] = i + 1; 
        }

        // Create ForkJoinPool
        ForkJoinPool pool = new ForkJoinPool();

        // Create task
        SumTask task = new SumTask(array, 0, array.length);

        long result = pool.submit(task).join(); // Using submit() and join()

        System.out.println("Sum: " + result);

        // Shutdown pool
        pool.shutdown();
    }
}

class SumTask extends RecursiveTask<Long> {
    private static final int THRESHOLD = 10; // Task split threshold
    private final int[] array;
    private final int start, end;

    public SumTask(int[] array, int start, int end) {
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

