variable a
  var-kind variable
  dec-type java.lang.String[]
  rep-type hashcode
  flags is_param
  comparability 2

variable a[..]
  var-kind array
  enclosing-var a
  array 1
  dec-type java.lang.String[]
  rep-type hashcode[]
  comparability 3[5]

loop_inv_0():::ENTER
a
[1 2 3]
1
a2
[1 2 4]
1
l
3
1
ic
0
1

iter_inv_0():::ENTER
a
[1 2 3]
1
a2
[1 2 4]
1
l
3
1
ic
0
1

iter_inv_0():::EXIT1
a
[1 2 3]
1
a2
[1 2 4]
1
l
3
1
ic
1
1

iter_inv_0():::ENTER
a
[1 2 3]
1
a2
[1 2 4]
1
l
3
1
ic
1
1

iter_inv_0():::EXIT1
a
[1 2 3]
1
a2
[1 2 4]
1
l
3
1
ic
2
1

iter_inv_0():::ENTER
a
[1 2 3]
1
a2
[1 2 4]
1
l
3
1
ic
2
1


# EOF (added by Runtime.addShutdownHook)

