function method abs(x : int) : nat
{
    if x < 0 then -x else x
}

method div(n: nat, d: nat) returns (q: nat, r: nat)
    requires d > 0
    ensures 0 <= r <= abs(d) && q * d + r == n
{
    if n >= 0 {
        q := 0;
        r := n;  
        while r >= d
            decreases r
            invariant q * d + r == n
        {
            q := q + 1;
            r := r - d;
        }
    }
    else {
        
    }
    
}

// A simple test case
method Main()
{
    var q, r := div(15, 6);
    print "q = ", q, " r=", r, "\n";
}