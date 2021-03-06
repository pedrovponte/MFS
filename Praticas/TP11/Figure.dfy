/* 
* Illustration of Design by Contract with inheritance in Dafny.
* FEUP, M.EIC, MFS, 2021/22.
*/

trait Figure {
    var center: (real, real);

    // predicate Valid()
    //     reads this
      
    function method getSizeX(): real
        // requires Valid()
        reads this

    function method getSizeY(): real
        // requires Valid()
        reads this
    
    method resize(factor: real)
        requires factor > 0.0
        // requires Valid()
        modifies this
        // ensures Valid()
        ensures getSizeX() == factor * old(getSizeX()) 
        ensures getSizeY() == factor * old(getSizeY())
        ensures center == old(center) 
}

class Circle extends Figure {
    var radius: real;

    constructor Circle(center: (real, real), radius: real)
    {
        this.center := center;
        this.radius := radius;
    }
    
    function method getSizeX(): real
        reads this
    {
        radius
    }

    function method getSizeY(): real
        reads this
    {
        radius
    }

    method resize(factor: real)
        modifies this
        requires factor != 0.0
        ensures center == old(center)
        ensures radius == abs(factor) * old(radius)
    {
       radius := abs(factor) * radius;
    }

    function method abs(x: real): real
    {
        if x >= 0.0 then x else -x 
    }
}