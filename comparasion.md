# Comparasion

|    Program    | Required invariants |
|---------------|---------------------|
| arrays_fill_a | 3/4 |
| hashCode_a    | 2/3 |
| max_array     | 2/3 |
| min_array     | 2/3 |
| sum_one_to_n  | 1/2 |
| sum_array     | 2/4 |
| linear_search | 3/5 |
| square        | 2/2 |
| cube          | 2/3 |

## arrays_fill_a

### Required invariants

```
Invariant(Acc(list_pred(a)))
Invariant(l == len(a))
Invariant(0 <= ic and ic <= l)
Invariant(eq(a, 0, ic, val))
```

### Found invariants

```
Invariant(Acc(list_pred(a)))
Invariant(val == Old(val))
Invariant(len(a) == Old(len(a)))
Invariant(l == len(a))
Invariant(l == Old(l))
Invariant(ic >= Old(ic))
Invariant(ic <= len(a))
Invariant(ic <= l)
Invariant(a == Old(a))
Invariant(a != None)
Invariant(Old(ic) >= 0)
Invariant(Old(ic) <= len(a))
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(Acc(list_pred(a)))` | `Invariant(Acc(list_pred(a)))` | Yes |
| `Invariant(l == len(a))` | `Invariant(l == len(a))` | Yes |
| `Invariant(0 <= ic and ic <= l)` | `Invariant(ic >= Old(ic))`, `Invariant(ic <= len(a))`, `Invariant(ic <= l)`, `Invariant(Old(ic) >= 0)` | Yes |
| `Invariant(eq(a, 0, ic, val))` | - | No |

## arrays_hashCode_a

### Required invariants

```
Invariant(Acc(list_pred(a)))
Invariant(len(a) == Old(len(a)))
Invariant(0 <= ic and ic <= len(a))
```

### Found invariants

```
Invariant(Acc(list_pred(a)))
Invariant(ic >= Old(ic))
Invariant(ic <= len(a))
Invariant(a == Old(a))
Invariant(a != None)
Invariant(Old(ic) >= 0)
Invariant(Old(ic) <= len(a))
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(Acc(list_pred(a)))` | `Invariant(Acc(list_pred(a)))` | Yes |
| `Invariant(len(a) == Old(len(a)))` | `Invariant(a == Old(a))` | No |
| `Invariant(0 <= ic and ic <= len(a))` | `Invariant(ic >= Old(ic))`, `Invariant(ic <= len(a))`, `Invariant(Old(ic) >= 0)` | Yes |

## max_array

### Required invariants

```
Invariant(Acc(list_pred(xs)))
Invariant(0 <= i and i <= len(xs))
Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, maximum >= xs[j])))
```

### Found invariants

```
Invariant(Acc(list_pred(xs)))
Invariant(xs == Old(xs))
Invariant(xs != None)
Invariant(maximum >= Old(maximum))
Invariant(i <= len(xs))
Invariant(Old(i) >= 0)
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(Acc(list_pred(xs)))` | `Invariant(Acc(list_pred(xs)))` | Yes |
| `Invariant(0 <= i and i <= len(xs))` | `Invariant(i <= len(xs))` and `Invariant(Old(i) >= 0)` | Yes |
| `Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, maximum >= xs[j])))` | - | No |

## min_array

### Required invariants

```
Invariant(Acc(list_pred(xs)))
Invariant(0 <= i and i <= len(xs))
Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, minimum <= xs[j])))
```

### Found invariants

```
Invariant(Acc(list_pred(xs)))
Invariant(xs == Old(xs))
Invariant(xs != None)
Invariant(minimum <= Old(minimum))
Invariant(i <= len(xs))
Invariant(Old(i) >= 0)
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(Acc(list_pred(xs)))` | `Invariant(Acc(list_pred(xs)))` | Yes |
| `Invariant(0 <= i and i <= len(xs))` | `Invariant(i <= len(xs))`, `Invariant(Old(i) >= 0)` | Yes |
| `Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, minimum <= xs[j])))` | - | No |

## sum_one_to_n

### Required invariants

```
Invariant(0 <= i and i <= n)
Invariant(sum == i * (i + 1) // 2)
```

### Found invariants

```
Invariant(sum >= Old(i))
Invariant(n >= i)
Invariant(n >= Old(i))
Invariant(n == Old(n))
Invariant(i <= sum)
Invariant(Old(sum) >= 0)
Invariant(Old(i) >= 0)
Invariant(Old(i) <= Old(sum))
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(0 <= i and i <= n)` | `Invariant(n >= i)`, `Invariant(Old(i) >= 0)`, `Invariant(n >= Old(i))` | Yes |
| `Invariant(sum == i * (i + 1) // 2)` | - | No |

## sum_array

### Required invariants

```
Invariant(Acc(list_pred(a)))
Invariant(len(a) == Old(len(a)))
Invariant(0 <= i and i <= len(a))
Invariant(s == sum_pure(a, 0, i))
```

### Found invariants

```
Invariant(Acc(list_pred(a)))
Invariant(i <= len(a))
Invariant(a == Old(a))
Invariant(a != None)
Invariant(Old(i) >= 0)
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(Acc(list_pred(a)))` | `Invariant(Acc(list_pred(a)))` | Yes |
| `Invariant(len(a) == Old(len(a)))` | `Invariant(a == Old(a))` | No |
| `Invariant(0 <= i and i <= len(a))` | `Invariant(i <= len(a))`, `Invariant(Old(i) >= 0)` | Yes |
| `Invariant(s == sum_pure(a, 0, i))` | - | No |

## linear_search

### Required invariants

```
Invariant(Acc(list_pred(arr)))
Invariant(len(arr) == Old(len(arr)))
Invariant(l == len(arr))
Invariant(0 <= i and i <= l)
Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, arr[j] != x)))
```

### Found invariants

```
Invariant(Acc(list_pred(arr)))
Invariant(x == Old(x))
Invariant(l == len(arr))
Invariant(l == Old(l))
Invariant(i >= Old(i))
Invariant(i <= len(arr))
Invariant(i <= l)
Invariant(arr == Old(arr))
Invariant(arr != None)
Invariant(Old(i) >= 0)
Invariant(Old(i) <= len(arr))
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(Acc(list_pred(arr)))` | `Invariant(Acc(list_pred(arr)))` | Yes |
| `Invariant(len(arr) == Old(len(arr)))` | `Invariant(arr == Old(arr))` | No |
| `Invariant(l == len(arr))` | `Invariant(l == len(arr))` | Yes |
| `Invariant(0 <= i and i <= l)` | `Invariant(i <= l)`, `Invariant(i <= len(arr))`, `Invariant(Old(i) >= 0)` | Yes |
| `Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, arr[j] != x)))` | - | No |

## square

### Required invariants

```
Invariant(0 <= i and i <= n)
Invariant(result == i * i)
```

### Found invariants
```
Invariant(result >= i)
Invariant(result >= Old(result))
Invariant(result == i * i)
Invariant(n >= i)
Invariant(n == Old(n))
Invariant(Old(result) >= Old(i))
Invariant(Old(result) >= 0)
Invariant(Old(i) >= 0)
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(0 <= i and i <= n)` | `Invariant(n >= i)`, `Invariant(Old(i) >= 0)`, `Invariant(n == Old(n))` | Yes |
| `Invariant(result == i * i)` | `Invariant(result == i * i)` | Yes |

## cube

### Required invariants

```
Invariant(0 <= i and i <= n)
Invariant(square == i * i)
Invariant(result == i * i * i)
```

### Found invariants

```
Invariant(square >= i)
Invariant(square == i * i)
Invariant(result >= square)
Invariant(result >= i)
Invariant(result >= Old(result))
Invariant(n >= i)
Invariant(n == Old(n))
Invariant(Old(square) >= Old(i))
Invariant(Old(square) >= 0)
Invariant(Old(result) >= Old(square))
Invariant(Old(result) >= Old(i))
Invariant(Old(result) >= 0)
Invariant(Old(i) >= 0)
```

### Result

| Required Invariant | Found Invariant | Match |
|--------------------|-----------------|-------|
| `Invariant(0 <= i and i <= n)` | `Invariant(n >= i)`, `Invariant(Old(i) >= 0)`, `Invariant(n == Old(n))` | Yes |
| `Invariant(square == i * i)` | `Invariant(square == i * i)` | Yes |
| `Invariant(result == i * i * i)` | - | No |
