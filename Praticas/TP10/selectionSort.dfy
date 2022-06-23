/* 
* Formal verification of the selection sort algorithm in Dafny.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0; 
    while i < a.Length - 1 
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall l, r :: 0 <= l < i <= r < a.Length ==> a[l] <= a[r]
    {
        var j := findMin(a, i, a.Length); // minimum in remaining subarray
        a[i], a[j] := a[j], a[i]; // swap
        i := i + 1;
    }
}

predicate isSorted(a: array<real>, from: nat, to: nat)
    reads a
    requires 0 <= from <= to <= a.Length
{   
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Finds the position of a miminum value in a non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat) 
    requires from < to <= a.Length
    ensures from <= index < to
    ensures forall i :: from <= i < to ==> a[index] <= a[i]
{
    var i := from + 1;
    index := from; // position of min up to position i (excluded)
    while i < to 
        invariant from <= i <= to && from <= index < i
        invariant forall j :: from <= j < i ==> a[index] <= a[j]
    {
        if a[i] < a[index] {
            index := i;
        }
        i := i + 1;
    }
}

method testSelectionSort() {
  var a := new real[5] [9.0, 4.0, 6.0, 3.0, 8.0];
  assert a[..] == [9.0, 4.0, 6.0, 3.0, 8.0];
  selectionSort(a);
  assert a[..] == [3.0, 4.0, 6.0, 8.0, 9.0];
}

method testFindMin() {
  var a := new real[5] [9.0, 5.0, 6.0, 4.0, 8.0];
  assert a[..] == [9.0, 5.0, 6.0, 4.0, 8.0];
  var m := findMin(a, 0, 5);
  assert a[3] == a[m] == 4.0;
  assert m == 3;
}