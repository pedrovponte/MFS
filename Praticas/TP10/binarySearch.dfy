// checks if array 'a' is sorted
predicate isSorted(a : array<int>) 
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found
method binarySearch(a : array<int>, x : int) returns (index : int) 
    requires isSorted(a)
    ensures (index == -1 && x !in a[..]) || (0 <= index < a.Length && a[index] == x)
{    
    var low, high := 0, a.Length;
 
    while low < high 
        invariant 0 <= low <= high <= a.Length
        invariant x !in a[..low]
        invariant x !in a[high..]
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        if {
            case a[mid] < x => low := mid + 1;
            case a[mid] > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return -1;
}

method testBinarySearch() {
    var a := new int[] [1, 4, 4, 6, 8];
    assert a[..]  == [1, 4, 4, 6, 8];
    var id1 := binarySearch(a, 6);
    assert a[3] == 6; // added
    assert id1 == 3;
    var id2 := binarySearch(a, 3);
    assert id2 == -1; 
    var id3 := binarySearch(a, 4);
    assert a[1] == 4 && a[2] == 4; // added
    assert id3 in {1, 2};
}