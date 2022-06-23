# Exercises on Program Verification with Hoare Logic

## Exercise 1

**a)** True

**b)** False

**c)** True

**d)** True

**e)** True

## Exercise 2

**a)**

```
wp(S,Q)
= wp(x := x+1, x > 5)
= x + 1 > 5
= x > 4
```

**b)**

```
wp(S,Q)
= wp(if a>b then x:=a else x:=b, x > 0)
= (a>b ∧ wp(x:=a, x>0)) ∨ (a<=b ∧ wp(x:=b, x>0))
= (a>b ∧ a>0) ∨ (a<=b ∧ b>0)
= a>0 ∨ b>0
```

**c)** wp(S,Q) = x>=y

## Exercise 3

**a)**

```
wp(skip, x>0)
= x>0

P -> wp(S,Q)
<=> x>5 -> x>0
<=> True
```

**b)**

```
wp(x:=x+1, x>5)
= x+1 > 5
= x > 4

P -> wp(S,Q)
<=> x<6 -> x>4
<=> x>=6 ∨ x>4
<=> x>4

Since this does not reduce to true (does not always hold), the triple is not valid
```

**c)**

```
wp(if x>0 then y:=10 else skip, y=10)
= (x>0 ∧ wp(y:=10, y=10)) ∨ (x<=0 ∧ wp(skip, y=10))
= (x>0 ∧ (10=10)) ∨ (x<=0 ∧ y=10)
= x>0 ∨ (x<=0 ∧ y=10)
= x>0 ∨ y=10

P -> wp(S,Q)
<=> (x=5 ∧ y=0) -> x>0 ∨ y=10
<=> True
```

**d)**

```
wp(x:=y, y:=a; x=b ∧ y=a)
= wp(x:=y, wp(y:=a; x=b ∧ y=a))
= wp(x:=y, x=b ∧ a=a)
= wp(x:=y, x=b)
= y = b

P -> wp(S,Q)
<=> (x=a ∧ y=b) -> y=b
<=> True
```

## Exercise 4

```
P -> I
<=> x > y -> x >= y
<=> True

I ∧ ¬C -> Q
<=> (x >= y) ∧ (x <= y) -> x = y
<=> x = y => x = y
<=> True

{I ∧ C ∧ V = V0}S{I ∧ 0 <= V < V0}
<=> {(x >= y) ∧ (x > y) ∧ (x-y = V0)} x:=x-1 {(x >= y) ∧ 0 <= x-y <= V0}
<=> {x > y ∧ x-y=V0} x:=x-1 {x >= y ∧ x-y < V0}
<=> (x > y ∧ x-y=V0) => (x-1 >= y ∧ x-1-y < V0)
<=> (x > y ∧ x-y=V0) => (x >= y+1 ∧ x-y <= V0)
<=> (x>y ∧ x-y=V0) => (x > y ∧ x-y <= V0)
<=> True

So the given triple is Valid
```

## Exercise 5

```
// Identify loop invariants and variants
I = r >= 0 ∧ d > 0 ∧ q * d + r = D
V = r

// Insert loop variants and invariants
{D >= 0 ∧ d > 0}
q := 0;
r := D;
**{r >= 0 ∧ d > 0 ∧ q * d + r = D} // I**
while r >= d do
    **{r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r >= d ∧ r = V0} // I ∧ C ∧ V = V0**
    q := q + 1;
    r := r - d;
    **{r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ 0 <= V < V0} // I ∧ 0 <= V < V0**
** {r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r < d} // I ∧ ¬C
{0 <= r < d ∧ q * d + r = D}

// Calculate pre-conditions bottom-up
{D >= 0 ∧ d > 0}
***{D >= 0 ∧ d > 0 ∧ 0 * d + D = D}***
q := 0;
***{D >= 0 ∧ d > 0 ∧ q * d + D = D}***
r := D;
**{r >= 0 ∧ d > 0 ∧ q * d + r = D} // I**
while r >= d do
    **{r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r >= d ∧ r = V0} // I ∧ C ∧ V = V0**
    ***{r-d >= 0 ∧ d > 0 ∧ (q+1) * d + (r-d) = D ∧ 0 <= r-d < V0}***
    q := q + 1;
    ***{r-d >= 0 ∧ d > 0 ∧ q * d + (r-d) = D ∧ 0 <= r-d < V0}***
    r := r - d;
    **{r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ 0 <= V < V0} // I ∧ 0 <= V < V0**
** {r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r < d} // I ∧ ¬C
{0 <= r < d ∧ q * d + r = D}

// Prove implications of consecutive conditions
(D >= 0 ∧ d > 0 => D >= 0 ∧ d > 0 ∧ 0 * d + D = D)
<=> (D >= 0 ∧ d > 0 => D >= 0 ∧ d > 0 ∧ D = D)
<=> (D >= 0 ∧ d > 0 => D >= 0 ∧ d > 0)
<=> True

(r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r >= d ∧ r = V0 => r-d >= 0 ∧ d > 0 ∧ (q+1) * d + (r-d) = D ∧ 0 <= r-d < V0)
<=> (d > 0 ∧ q * d + r = D ∧ r >= d ∧ r = V0 ==> r >= d ∧ d > 0 ∧ q * d + r = D ∧ r < V0 + d)
<=> True

(r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r < d => 0 <= r < d ∧ q * d + r = D)
<=> (r >= 0 ∧ d > 0 ∧ q * d + r = D ∧ r < d => r >= 0 ∧ d > 0 ∧ q * d + r = D)
<=> True
```

## Exercise 6

**a)**

```
{x >= 0}
**{x >= 0}**
z := x;
**{z + 0 = x ∧ z >= 0}**
y := 0;
{z + y = x ∧ z >= 0} //I
while z != 0 do
    {z != 0 ∧ z + y = x ∧ z >= 0 ∧ z = V0} // C ∧ I ∧ V = V0
    **{z + y = x ∧ z - 1 >= 0 ∧ 0 <= z - 1 < V0}**
    y := y + 1
    **{z - 1 + y = x ∧ z - 1 >= 0 ∧ 0 <= z - 1 < V0}**
    z := z - 1;
    {z + y = x ∧ z >= 0 ∧ 0 <= z < V0} // I ∧ 0 <= V < V0
{z = 0 ∧ z + y = x ∧ z >= 0} // ¬C ∧ I
{x = y}
```

**b)**

```
(x >= 0 => x >= 0) <=> True

(z != 0 ∧ z + y = x ∧ z >= 0 ∧ z = V0 => z + y = x ∧ z - 1 >= 0 ∧ 0 <= z - 1 < V0)
<=> (z + y = x ∧ z > 0 ∧ z = V0 => z + y = x ∧ z > 0 ∧ z - 1 < V0)
<=> (z + y = x ∧ z > 0 ∧ z = V0 => z + y = x ∧ z > 0 ∧ V0 - 1 < V0)
<=> (z + y = x ∧ z > 0 ∧ z = V0 => z + y = x ∧ z > 0)
<=> True

(z = 0 ∧ z + y = x ∧ z >= 0 => x = y)
<=> (z = 0 ∧ z + y = x => x = y)
<=> (y = x => x = y)
<=> True
```
