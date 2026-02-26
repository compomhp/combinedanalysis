package compomhp;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

public abstract class Constraint {
	
	public ConstraintName name = ConstraintName.GENERAL;
	private static AtomicInteger totalCount = new AtomicInteger(0);
    private static ConcurrentHashMap<Class<?>, AtomicInteger> subtypeCounts = new ConcurrentHashMap<>();

    public Constraint() {
        totalCount.incrementAndGet(); // Atomic increment
        subtypeCounts.computeIfAbsent(this.getClass(), k -> new AtomicInteger(0)).incrementAndGet(); // Atomic per-subclass increment
    }

    public static int getTotalCount() {
        return totalCount.get();
    }
    public static void addToSubtypeCount(Class<?> clazz, int count) {
        if (count < 0) {
            throw new IllegalArgumentException("Count must be non-negative");
        }
        if (clazz != null && Constraint.class.isAssignableFrom(clazz)) {
            totalCount.addAndGet(count); // Atomically add to total count
            subtypeCounts.computeIfAbsent(clazz, k -> new AtomicInteger(0)).addAndGet(count); // Atomically add to subtype count
        } else {
            throw new IllegalArgumentException("Class must be a subclass of Constraint");
        }
    }
    public static int getCountForClass(Class<?> clazz) {
        return subtypeCounts.getOrDefault(clazz, new AtomicInteger(0)).get();
    }
	
	Object outerCondObj = null;
	boolean useOuterCondObj = false;
	
	abstract public String printConstraint(); 
	abstract public void insert();
	abstract public Constraint getCopy();
	abstract public Constraint updateCond(Object obj, int cardinality);
	abstract public void addToList();
	ConstType constType;
}
