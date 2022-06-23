type T = int

predicate sorted(a: array<T>, n: nat)
  reads a
  requires 0 <= n <= a.Length
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

function elems(a: array<T>, n: nat): multiset<T>
  requires n <= a.Length
  reads a
{
  multiset(a[..n])
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'
method merge(a: array<T>, b: array<T>) returns (c: array<T>) 
    requires sorted(a, a.Length)
    requires sorted(b, b.Length)
    ensures sorted(c, c.Length)
    ensures elems(c, c.Length) == elems(a, a.Length) + elems(b, b.Length)
{
    c := new T[a.Length + b.Length];
    var i, j := 0, 0;

    // Repeatedly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length 
        decreases (a.Length - i) + (b.Length - j)
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant sorted(c, i + j)
        invariant elems(c, i + j) == elems(a, i) + elems(b, j)
        invariant forall k, l :: i <= k < a.Length && 0 <= l < i + j ==> a[k] >= c[l]
        invariant forall k, l :: j <= k < b.Length && 0 <= l < i + j ==> b[k] >= c[l]
    {
        if i < a.Length && (j == b.Length || a[i] <= b[j]) {
            c[i + j] := a[i];
            i := i + 1;
        }
        else {
            c[i + j] := b[j];
            j := j + 1;
        }
    }
}

method testMerge() {
    var a: array<T> := new T[3] [1, 3, 5];
    var b: array<T> := new T[2] [2, 4];
    var c:= merge(a, b);
    assert a[..a.Length] == [1, 3, 5];
    assert b[..b.Length] == [2, 4];
    assert elems(c, c.Length) == multiset{1, 2, 3, 4, 5};
    assert c[..] == [1, 2, 3, 4, 5];
}