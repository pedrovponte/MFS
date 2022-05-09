# Exercises on Program Verification with Hoare Logic

## Exercise 1

**a)** True

**b)** False

**c)** True

**d)** True

**e)** True

## Exercise 2

**a)** x >= 5

**b)** a >

**c)** x >= y

## Exercise 3

**a)**

```
wp(S,Q) 
<=> wp(skip, x > 0) 
<=> x > 0

P -> wp(S,Q) 
<=> x > 5 -> x > 0 True
```

**b)**

```
wp(S,Q) 
<=> wp(x := x + 1, x > 5) 
<=> x + 1 > 5 
<=> x > 4

P -> wp(S,Q) 
<=> x < 6 -> x > 4 False
```

**c)**

```
wp(S,Q) 
<=> wp(if x > 0 then y := 10 else skip, y = 10) 
<=> (x > 0 ∧ wp(y := 10, y = 10)) ∨ (x <= 0 ∧ wp(skip, y = 10)) 
<=> (x > 0 ∧ 10 = 10) ∨ (x <= 0 ∧ y = 10) 
<=> (x > 0) ∨ (x <= 0 ∧ y = 10)

P -> wp(S,Q) 
<=> (x = 5 ∧ y = 0) -> (x > 0) ∨ (x <= 0 ∧ y = 10) True
```

**d)**

```
wp(S,Q) 
<=> wp(x := y; y := a, x = b ∧ y = a) 
<=> wp(x := y, wp(y := a, x = b ∧ y = a)) 
<=>

```

## Exercise 4

```
P -> I 
<=> x > y -> x >= y True

I ∧ ¬C → Q 
<=> x >= y ∧ ¬(x > y) -> x = y 
<=> x >= y ∧ x <= y -> x = y 
<=> x = y -> x = y True

{I ∧ C ∧ V = V0} S {I ∧ 0 ≤ V < V0} 
<=> {x >= y ∧ x > y ∧ x - y = V0} x := x - 1 {x >= y ∧ 0 <= x - y < V0} 
<=> {x > y ∧ x - y = V0} x := x - 1 {x >= y ∧ x -y < V0} 
<=> (x > y ∧ x - y = V0) -> wp(x := x - 1, x >= y ∧ x - y < V0) 
<=> (x > y ∧ x - y = V0) -> (x - 1 >= y ∧ x - y - 1 < V0) True
```

## Exercise 5

```
I = q * d + r
V = r

{D >= 0 ∧ d > 0}
{0 * d + D = D}
q := 0
{q * d + D = D}
r := D

{q * d + r = D}

while r >= d do
    {q * d + r = D ∧ r >= d ∧ r = V0}
    {(q+1) * d + r - d = D ∧ 0 <= r - d < V0}
    q := q + 1
    {q * d + r - d = D ∧ 0 <= r - d < V0}
    r := r - d
    {q * d + r = D ∧ 0 <= r < V0}

{q * d * r = D ∧ ¬(n >= d)}

{0 <= r < d ∧ q * d + r = D}

É necessário fortalecer o invariante : I = q * d + r ∧ r > 0