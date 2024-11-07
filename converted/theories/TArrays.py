from nagini_contracts.contracts import *

"""
    // Is `[fromIndex..toIndex)' a valid interval within `[0..a.length)'?
    /**
     * Returns <code>true</code> iff <code>[fromIndex..toIndex)</code> 
       is a subinterval of <code>[0..a.length)</code>.
     * 
     * @param a   an array
     * @param fromIndex   a lower <code>int</code> index
     * @param toIndex   an upper <code>int</code> index
     * @return    <code>true</code> if <code>x</code> is a valid index in <code>a</code>, 
                  otherwise <code>false</code>
     * @throws RuntimeException if the precondition fails
     * @dm.require  <code>a != null</code>
     * @dm.ensure   <code>\result <==> 0 <= fromIndex && fromIndex <= toIndex && toIndex <= a.length</code>
     */
    /*@ 
      @ requires a != null;
      @
      @ ensures \result <==> 0 <= fromIndex && fromIndex <= toIndex && toIndex <= a.length; 
      @*/
    public static /*@ pure @*/ boolean within(int[] a, int fromIndex, int toIndex)
    {
        if (a == null)
            throw new RuntimeException();

        return (0 <= fromIndex && fromIndex <= toIndex && toIndex <= a.length);
    }
"""
@Pure
def within(a: list[int], fromIndex: int, toIndex: int) -> bool:
    Requires(Acc(list_pred(a)))
    Ensures(Result() == (0 <= fromIndex and fromIndex <= toIndex and toIndex <= len(a)))

    return 0 <= fromIndex and fromIndex <= toIndex and toIndex <= len(a)

"""    
    // Does a[fromIndex..toIndex) == key?
    /**
     * Returns <code>true</code> iff all elements of <code>a</code> over <code>[fromIndex..toIndex)</code> 
       have value equal to <code>key</code>.
     * 
     * @param a   an array
     * @param fromIndex   a lower <code>int</code> index
     * @param toIndex   an upper <code>int</code> index
     * @param key   an <code>int</code> value
     * @return    <code>true</code> if all elements of <code>a</code> over <code>[fromIndex..toIndex)</code> 
                  have value equal to <code>key</code>, 
                  otherwise <code>false</code>
     * @throws RuntimeException if the precondition fails
     * @dm.require   <code>a != null</code>
     * @dm.require   <code>within(a, fromIndex, toIndex)</code>
     * @dm.ensure    \result <==> (\forall int i; fromIndex <= i && i < toIndex ==> a[i] == key)
     */
    /*@ 
      @ requires a != null;
      @ requires within(a, fromIndex, toIndex);
      @
      @ ensures \result <==> (\forall int i; fromIndex <= i && i < toIndex ==> a[i] == key); 
      @*/
    public static /*@ pure @*/ boolean eq(int[] a, int fromIndex, int toIndex, int key)
    {
        if (a == null)
            throw new RuntimeException();
        if (!within(a, fromIndex, toIndex))
            throw new RuntimeException();

        if (fromIndex >= toIndex) {
            return true;
        } else {
            int first = a[fromIndex];
            return (first == key) && eq(a, fromIndex + 1, toIndex, key);
        }
    }
"""

@Pure
def eq(a: list[int], fromIndex: int, toIndex: int, key: int) -> bool:
    Requires(Acc(list_pred(a)) and within(a, fromIndex, toIndex))
    Ensures(Result() == Forall(int, lambda i: Implies(fromIndex <= i and i < toIndex, a[i] == key)))

    if fromIndex >= toIndex:
        return True
    else:
        first = a[fromIndex]
        return first == key and eq(a, fromIndex + 1, toIndex, key)