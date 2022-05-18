/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(b: real, n: nat) returns (p : real)
{
    // start with p = b^0
    p := 1.0;
    var i := 0;
    // iterate until reaching p = b^n
    while i < n
    {
        p := p * b;
        i := i + 1;
    }
}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(b: real, n: nat) returns (p : real)
{
    if n == 0 {
        return 1.0;
    }
    else if n % 2 == 0 {
        var r := powerOpt(b, n/2);
        return r * r;
    }
    else {
        var r := powerOpt(b, (n-1)/2);
        return r * r * b;
    } 
}

// A simple test case to make sure the specification is adequate.
method testPower() {
    var p1 := powerIter(2.0, 5);
    var p2 := powerOpt(2.0, 5);
}