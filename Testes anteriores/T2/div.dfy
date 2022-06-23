function method abs(d: int) : nat
{
    if d >= 0 then d else -d
}

function method sign(d : int) : int
{
    if d >= 0 then 1 else -1
}

method div(n: int, d: int) returns (q: int, r: int)
  requires d != 0
  ensures 0 <= r < abs(d)
  ensures q * d + r == n
{
  q := 0;
  r := n;  

  if n > 0
  {
    while r >= abs(d)
        decreases r
        invariant r >= 0
        invariant q * d + r == n
    {
        q := q + sign(d);
        r := r - abs(d);
    }
  }
  else if n < 0
  {
    while r < 0
        decreases abs(d) - r
        invariant r < abs(d) 
        invariant q * d + r == n
    {
        q := q - sign(d);
        r := r + abs(d);
    }
  }
}

// A simple test case
method Main()
{
  var q, r := div(15, 6);
  print "q = ", q, " r = ", r, "\n";
  assert q == 2 && r == 3;

  var q1, r1 := div(15, -6);
  print "q = ", q1, " r = ", r1, "\n";
  assert q1 == -2 && r1 == 3;
}