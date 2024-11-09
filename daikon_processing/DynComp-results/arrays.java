public static void fill0(int[] a, int val) {

    int ic = 0;
    int len = a.length;

    //@ loop_invariant 0 <= ic && ic <= a.length;
    //@ loop_invariant TArrays.eq(a, 0, ic, val);
    for (; ic < len; ic++) {
        a[ic] = val;
    }
}

//JIMENA said she added a main
