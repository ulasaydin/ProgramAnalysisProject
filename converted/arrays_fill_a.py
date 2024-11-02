from nagini_contracts.contracts import *
from theories.TArrays import eq

"""
/**
    * Assigns the specified int value to each element of the specified array of
    * ints.
    * 
    * @param a
    *            the array to be filled
    * @param val
    *            the value to be stored in all elements of the array
    */
// Called "fill_a" in http://arxiv.org/abs/1407.5286
/*@ 
    @ requires a != null;
    @
    @ assignable a[*];
    @
    @ ensures TArrays.eq(a, 0, a.length, val); 
    @*/
public static void fill0(int[] a, int val) {

    int ic = 0;
    int len = a.length;

    //@ loop_invariant 0 <= ic && ic <= a.length;
    //@ loop_invariant TArrays.eq(a, 0, ic, val);
    for (; ic < len; ic++) {
        a[ic] = val;
    }
}
"""

def fill_a(arr: list[int], val: int) -> None:
    Requires(list_pred(arr))
    Requires(Acc(list_pred(arr)))
    Ensures(eq(arr, 0, len(arr), val))

    ic = 0
    l = len(arr)

    while ic < l:
        Invariant(0 <= ic and ic <= l)
        Invariant(eq(arr, 0, ic, val))
        arr[ic] = val
        ic = ic + 1

    Assert(False)
