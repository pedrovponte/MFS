/* 
* Formal verification of the selection sort algorithm in Dafny.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Checks if all elements in subarray a[i], ..., a[j-1] are less or equal than
// all elements in subarray a[k], ..., a[l-1].
predicate leq(a: array<real>, i: nat, j: nat, k: nat, l: nat)
  requires 0 <= i <= j <= a.Length && 0 <= k <= l <= a.Length
  reads a
{
  forall x, y :: i <= x < j && k <= y < l ==> a[x] <= a[y]
}


method bubbleSort(a: array<real>)
  modifies a
  ensures isSorted(a,0,a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := a.Length; 
    while n > 1
      invariant 0 <= n <= a.Length
      invariant isSorted(a, n, a.Length) && leq(a, 0, n, n, a.Length)
      invariant multiset(old(a[..])) == multiset(a[..])
    {
      var newn := 0;
      var i := 1;
      while i < n 
        invariant 0 <= newn < i <= n
        invariant isSorted(a, n, a.Length) && leq(a, 0, n, n, a.Length)
        invariant isSorted(a, newn, i) && leq(a, 0, newn, newn, i)
        invariant multiset(old(a[..])) == multiset(a[..])
      {
          if (a[i-1] > a[i]) { 
              a[i-1], a[i] := a[i], a[i-1]; 
              newn := i;
          }
          i := i+1; 
      }
      n := newn;
    }
}

predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}
