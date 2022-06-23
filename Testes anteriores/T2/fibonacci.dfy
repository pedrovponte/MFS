function fib(n : nat ) : nat
    decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}

method computeFib (n : nat) returns (x : nat)
    ensures x == fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while i < n
        invariant fib(i) == x && fib(i + 1) == y && 0 <= i <= n
        decreases n - i
    {
        x, y := y, x + y; // multiple assignment
        i := i + 1;
    }
}