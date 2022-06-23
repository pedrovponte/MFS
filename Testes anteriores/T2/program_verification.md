# Exercises on Program Verification with Dafny

## Exercise 1

**c)**

```
1. inserir pré e pós-condição

{n >= 0}
i := 0;
x := 0;
y := 1;
while i < n
{
    x, y := y, x + y; // multiple assignment
    i := i + 1;
}
{x = fib(n)}

2. inserir asserções geradas pelo invariante e variante de ciclo

{n >= 0}
i := 0;
x := 0;
y := 1;
{fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ 0 <= n - i} // I
while i < n
{
    {fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ i < n ∧ 0 <= n - i ∧ n - i = V0} // I ∧ C ∧ V = V0
    x, y := y, x + y; // multiple assignment
    i := i + 1;
    {fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ 0 <= n - i ∧ 0 <= n - i < V0} // I ∧ 0 <= V < V0
}
{fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ i >= n} // I ∧ ¬C
{x = fib(n)}

3. calcular pré-condiçoes mais fracas

{n >= 0}
{fib(0) = 0 ∧ fib(0 + 1) = 1 ∧ 0 <= 0 <= n ∧ 0 <= n - 0}
i := 0;
{fib(i) = 0 ∧ fib(i + 1) = 1 ∧ 0 <= i <= n ∧ 0 <= n - i}
x := 0;
{fib(i) = x ∧ fib(i + 1) = 1 ∧ 0 <= i <= n ∧ 0 <= n - i}
y := 1;
{fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ 0 <= n - i} // I
while i < n
{
    {fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ i < n ∧ 0 <= n - i ∧ n - i = V0} // I ∧ C ∧ V = V0
    {fib(i + 1) = y ∧ fib(i + 2) = x + y ∧ 0 <= i + 1 <= n ∧ 0 <= n - i - 1 < V0}
    x, y := y, x + y; // multiple assignment
    {fib(i + 1) = x ∧ fib(i + 2) = y ∧ 0 <= i + 1 <= n ∧ 0 <= n - i - 1 < V0}
    i := i + 1;
    {fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ 0 <= n - i < V0} // I ∧ 0 <= V < V0
}
{fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ i >= n} // I ∧ ¬C
{x = fib(n)}

4. provar as implicações

(n >= 0) => (fib(0) = 0 ∧ fib(0 + 1) = 1 ∧ 0 <= 0 <= n ∧ 0 <= n - 0)
<=> (0 <= n) => (0 = 0 ∧ 1 = 1 ∧ 0 <= n ∧ 0 <= n)
<=> (0 <= n) => (True ∧ True ∧ 0 <= n)
<=> (0 <= n) => (0 <= n)
<=> True

(fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ i < n ∧ 0 <= n - i ∧ n - i = V0) => (fib(i + 1) = y ∧ fib(i + 2) = x + y ∧ 0 <= i + 1 <= n ∧ 0 <= n - i - 1 < V0)
<=> (0 <= i <= n ∧ fib(i) = x ∧ fib(i + 1) = y ∧ i < n ∧ 0 <= n - i ∧ n - i = V0) => (0 <= i + 1 <= n ∧ fib(i + 1) = y ∧ fib(i + 2) = x + y ∧0 <= n - i - 1 < V0)
<=> True

(fib(i) = x ∧ fib(i + 1) = y ∧ 0 <= i <= n ∧ i >= n) => (x = fib(n))
<=> (i = n ∧ fib(i) = x ∧ fib(i + 1) = y) => (x = fib(n))
<=> True
```

## Exercise 2

**c)**

```

{n >= 0}
{0 <= 0 <= n ∧ fact(0) == 1 ∧ 0 <= n - 0}
f := 1;
{0 <= 0 <= n ∧ fact(0) == f ∧ 0 <= n - i}
var i := 0;
{0 <= i <= n ∧ fact(i) == f ∧ 0 <= n - i} // I
while i < n
{
    {0 <= i <= n ∧ fact(i) == f ∧ 0 <= n - i ∧ i < n ∧ n - i = V0} // I ∧ C ∧ V = V0
    {0 <= i + 1 <= n ∧ fact(i + 1) == f * (i + 1) ∧ 0 <= n - i - 1 < V0}
    i := i + 1;
    {0 <= i <= n ∧ fact(i) == f * i ∧ 0 <= n - i < V0}
    f := f * i;
    {0 <= i <= n ∧ fact(i) == f ∧ 0 <= n - i < V0} // I ∧ 0 <= V < V0
}
{0 <= i <= n ∧ fact(i) == f ∧ i >= n} // I ∧ ¬C
{f = fact(n)}

Provas

(n >= 0) => (0 <= 0 <= n ∧ fact(0) = 1 ∧ 0 <= n - 0)
<=> (n >= 0) => (n >= 0 ∧ 1 = 1 ∧ n >= 0)
<=> (n >= 0) => (n >= 0)
<=> True

(0 <= i <= n ∧ fact(i) = f ∧ 0 <= n - i ∧ i < n ∧ n - i = V0) => (0 <= i + 1 <= n ∧ fact(i + 1) = f * (i + 1) ∧ 0 <= n - i - 1 < V0)
<=> (0 <= i <= n ∧ fact(i) = f ∧ n - i = V0) => (0 <= i + 1 <= n ∧ fact(i + 1) = f * (i + 1) ∧ True ∧ n - i - 1 < V0)
<=> (0 <= i < n ∧ fact(i) = f ∧ n - i = V0) => (0 <= i + 1 <= n ∧ fact(i + 1) = f * (i + 1) ∧ n - i - 1 < V0)
<=> True

(0 <= i <= n ∧ fact(i) == f ∧ i >= n) => (f = fact(n))
<=> (i = n ∧ fact(i) == f) => (f = fact(n))
<=> (fact(n) = f) => (fact(n) = f)
<=> True
```
