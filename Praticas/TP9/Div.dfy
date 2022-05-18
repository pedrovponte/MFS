/* 
* Formal specification and verification of a simple method 
* for performing integer division.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Computes the quotient 'q' and remainder 'r' of 
// the integer division of a (non-negative) dividend
// 'n' by a (positive) divisor 'd'.
method div(n: nat, d: nat) returns (q: nat, r: nat)
  requires d > 0
  ensures 0 <= r <= d && q * d + r == n
{
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

// A simple test case
method Main()
{
    var q, r := div(15, 6);
    print "q = ", q, " r=", r, "\n";
}
