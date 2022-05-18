function fib (n : nat) : nat 
    decreases n
{
    if n < 2 then n else fib(n-2) + fib(n-1)
}

method computeFib (n : nat) returns (x : nat)
    requires n > 0
    ensures x == fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while i < n
        decreases n - i
        invariant x == fib(i) && y == fib(i + 1) && 0 <= i <= n
    {
        x, y := y, x + y; // multiple assignement
        i := i + 1;
    }
}

method Main()
{
    var f := 6;
    var x := computeFib(f);
    print "fib(", f, ") = ", x, "\n";
    assert x == 8;
}