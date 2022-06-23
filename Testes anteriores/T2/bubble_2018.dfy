method bubbleSort(a: array<real>)
    // ensures forall k :: 0 <= k <= a.Length ==> a[k] <= a[k+1]
    ensures forall i,j :: 0 <= i < j <= a.Length - 1 ==> a[i] <= a[j]
    ensures forall i,j :: 0 <= i <= a.Length - 1 && i+1 <= j <= a.Length - 1 ==> a[i] <= a[j]
    ensures forall k :: 1 <= k <= a.Length - 1 ==> a[k-1] <= a[k]
{
    var i : int := a.Length - 1;
    while (i > 0) 
        invariant -1 <= i <= a.Length - 1
    
    {
        innerLoop(a, i);
        i := i - 1;
    }
} 

method innerLoop(a: array<real>, i: int) 
{
    var j: int := 0;
    while (j < i)
        invariant 0 <= j <= i && forall k :: 0 <= k <= j-1 ==> a[k] <= a[j]
    {
        if (a[j] > a[j+1]) 
        {
            swap(a, j, j+1);
        }
        j:= j + 1;
    }
}

method swap(a: array<real>, from: int, to: int)
{

}