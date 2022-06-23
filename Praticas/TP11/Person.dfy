datatype Sex = Masculine | Feminine
datatype CivilState = Single | Married | Divorced | Widow | Dead

class Person
{
    const name: string; // ‘const’ for immutable fields
    const sex: Sex;
    const mother: Person?; // ‘?’ to allow null
    const father: Person?;
    var spouse: Person?;
    var civilState: CivilState;

    constructor (name: string, sex: Sex, mother: Person?, father: Person?)
        requires (father != null ==> father.sex == Masculine)
        requires (mother != null ==> mother.sex == Feminine)
        ensures Valid()
    {
        this.name := name;
        this.sex := sex;
        this.mother := mother;
        this.father := father;
        this.spouse := null;
        this.civilState := Single;
    }

    predicate Valid()
        reads this
    {
        (this.civilState == Married <==> this.spouse != null) &&
        (this.mother != null ==> this.mother.sex == Feminine) &&
        (this.father != null ==> this.father.sex == Masculine) &&
        (this.spouse != null ==> this.spouse.spouse == this)
    }
    
    method marry(spouse: Person)
        modifies this, spouse
        requires Valid()
        requires (this.civilState == Single) || (this.civilState == Divorced) || (this.civilState == Widow)
        requires (spouse.civilState == Single) || (spouse.civilState == Divorced) || (spouse.civilState == Widow)
        ensures Valid()
        ensures spouse.spouse == this
        ensures spouse.civilState == Married
        ensures this.civilState == Married
        ensures this.spouse == spouse
    {
        spouse.spouse := this;
        spouse.civilState := Married;
        this.spouse := spouse;
        this.civilState := Married;
    }
    
    method divorce()
        modifies this, spouse
        requires Valid()
        requires spouse != null
        requires this.civilState == Married
        requires spouse.civilState == Married
        requires Valid()
    {
        spouse.spouse := null;
        spouse.civilState := Divorced;
        this.spouse := null;
        this.civilState := Divorced;
    }
    
    method die()
    {
        if spouse != null
        {
            spouse.spouse := null;
            spouse.civilState := Widow;
        }
        this.spouse := null;
        this.civilState := Dead;
    }
}