function method fact(n : nat) : nat 
    decreases n
{
    if n == 0 then 1 else n * fact(n-1)
}

method factIter(n : nat) returns (f : nat)
    requires n >= 0
    ensures f == fact(n)
{
    f := 1;
    var i := 0;
    while i < n
        decreases n - i
        invariant f == fact(i) && 0 <= i <= n
    {
        i := i + 1;
        f := f * i;
    }
}

method Main()
{
    var f := 6;
    var x := factIter(f);
    print "fact(", f, ") = ", x, "\n";
    assert x == 720;
}