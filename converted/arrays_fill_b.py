"""
/**
     * Assigns the specified int value to each element of the specified range of
     * the specified array of ints. The range to be filled extends from index
     * <tt>fromIndex</tt>, inclusive, to index <tt>toIndex</tt>, exclusive. (If
     * <tt>fromIndex==toIndex</tt>, the range to be filled is empty.)
     * 
     * @param a
     *            the array to be filled
     * @param fromIndex
     *            the index of the first element (inclusive) to be filled with
     *            the specified value
     * @param toIndex
     *            the index of the last element (exclusive) to be filled with
     *            the specified value
     * @param val
     *            the value to be stored in all elements of the array
     * @throws IllegalArgumentException
     *             if <tt>fromIndex &gt; toIndex</tt>
     * @throws ArrayIndexOutOfBoundsException
     *             if <tt>fromIndex &lt; 0</tt> or
     *             <tt>toIndex &gt; a.length</tt>
     */
    // Called "fill_b" in http://arxiv.org/abs/1407.5286
    /*@ normal_behavior
      @ requires a != null;
      @ requires TArrays.within(a, fromIndex, toIndex);
      @ assignable a[*];
      @ ensures (\forall int j; 0 <= j && j < fromIndex ==> a[j] == \old(a[j]));
      @ ensures TArrays.eq(a, fromIndex, toIndex, val);
      @ ensures (\forall int j; toIndex <= j && j < a.length ==> a[j] == \old(a[j]));
      @
      @ also   exceptional_behavior
      @ requires fromIndex > toIndex;
      @ signals (java_v.lang_v.IllegalArgumentException ex) true;
      @
      @ also exceptional_behavior
      @ requires fromIndex < 0 || toIndex > a.length;
      @ signals (java_v.lang_v.ArrayIndexOutOfBoundsException  ex) true;
      @
      @ also exceptional_behavior
      @ requires a == null;
      @ signals (NullPointerException ex) true;
      @*/
    public static void fill1(int[] a, int fromIndex, int toIndex, int val)
        throws java_v.lang_v.IllegalArgumentException,
               java_v.lang_v.ArrayIndexOutOfBoundsException, NullPointerException {
        if (a == null)
            throw new NullPointerException();

        rangeCheck(a.length, fromIndex, toIndex);

        int ic = fromIndex;

        //@ loop_invariant fromIndex <= ic && ic <= toIndex;
        //@ loop_invariant (\forall int j; 0 <= j && j < fromIndex ==> a[j] == \old(a[j]));
        //@ loop_invariant TArrays.eq(a, fromIndex, ic, val);
        //@ loop_invariant (\forall int j; toIndex <= j && j < a.length ==> a[j] == \old(a[j]));
        for (; ic < toIndex; ic++) {
            a[ic] = val;
        }
    }

"""

from nagini_contracts.contracts import *
from theories.TArrays import *

def fill_b(a: list[int], from_index: int, to_index: int, val: int) -> None:
    Requires(a is not None) # Might be unnecessary, but identical to java
    Requires(Acc(list_pred(a)) and within(a, from_index, to_index))
    # Requires(from_index <= to_index)
    # Requires(0 <= from_index)
    # Requires(to_index < len(a))
    # Ensures(within(a, from_index, to_index))
    # Ensures(len(a) == len(Old(a)))

    Ensures(Acc(list_pred(a)))
    Ensures(Forall(int, lambda j: Implies(0 <= j and j < from_index, Old(a[j]) == a[j])))
    Ensures(eq(a, from_index, to_index, val))
    Ensures(Forall(int, lambda j: Implies(to_index <= j and j < len(a), a[j] == Old(a[j]))))
    
    # Not working, but tried to implement exceptional behaviors like in Java
    Exsures(ValueError, from_index > to_index)
    Exsures(IndexError, from_index < 0 or to_index > len(a))
    Exsures(TypeError, a is None)

    if a is None:
        raise TypeError
    if from_index > to_index:
        raise ValueError
    if from_index < 0 or to_index > len(a):
        raise IndexError

    ic = from_index

    while(ic < to_index):
        Invariant(Acc(list_pred(a)))
        # Invariant(within(a, from_index, ic))
        Invariant(from_index <= ic and ic <= to_index)
        Invariant(Forall(int, lambda j: Implies(0 <= j and j < from_index and j < to_index, Old(a[j]) == a[j])))
        Invariant(eq(a, from_index, ic, val))
        Invariant(Forall(int, lambda j: Implies(to_index <= j and j < len(a), a[j] == Old(a[j]))))

        a[ic] = val
        ic += 1

    # Assert(False)