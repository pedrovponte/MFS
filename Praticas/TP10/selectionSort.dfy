/* 
* Formal verification of the selection sort algorithm in Dafny.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>) {
    var i := 0; 
    while i < a.Length - 1 {
        var j := findMin(a, i, a.Length); // minimum in remaining subarray
        a[i], a[j] := a[j], a[i]; // swap
        i := i + 1;
    }
}

// Finds the position of a miminum value in a non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat) {
    var i := from + 1;
    index := from; // position of min up to position i (excluded)
    while i < to {
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