from nagini_contracts.contracts import *

"""
/*@
      @ requires a != null;
      @ requires TArrays.within(a,fromIndex,toIndex);
      @ requires TArrays.sorted(a,fromIndex,toIndex);
      @
      @ ensures \result >= 0 ==> a[\result] == key;
      @ ensures \result < 0 ==> (!TArrays.in(a,fromIndex,toIndex,key));
      @*/
    private static/*@ pure @*/int binarySearch0(int[] a, int fromIndex,
                                                int toIndex, int key) {

        int low = fromIndex;
        int high = toIndex - 1;

        //@ loop_invariant 0 <= fromIndex && fromIndex <= toIndex && toIndex<=a.length;
        //@ loop_invariant high >= -1;
        //@ loop_invariant fromIndex <= low;
        //@ loop_invariant low <= high +1;
        //@ loop_invariant high < toIndex;
        //@ loop_invariant TArrays.sorted(a, fromIndex, toIndex);
        //@ loop_invariant TArrays.less(a, fromIndex, low, key);
        //@ loop_invariant TArrays.grt(a, high + 1, toIndex, key);
        while (low <= high) {
            int mid = low + ((high - low) / 2); // equivalent to (low + high) >>> 1;
            int midVal = a[mid];

            if (midVal < key) {
                low = mid + 1;
            } else if (midVal > key) {
                high = mid - 1;
            } else {
                return mid; // key found
            }
        }
        return -(low + 1); // key not found.

    }
"""


def binary_search(a: list[int], fromIndex: int, toIndex: int, key: int) -> int:
    low = fromIndex
    high = toIndex - 1
    while low <= high:
        mid = low + (high - low) // 2
        midVal = a[mid]
        if midVal < key:
            low = mid + 1
        elif midVal > key:
            high = mid - 1
        else:
            return mid
    return -(low + 1)