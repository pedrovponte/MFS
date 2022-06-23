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
    ghost const ancestors : set<Person>

    constructor (name: string, sex: Sex, mother: Person?, father: Person?)
        requires (mother != null ==> mother.sex == Feminine)
        requires (father != null ==> father.sex == Masculine)
        ensures this.name == name 
        ensures this.sex == sex 
        ensures this.mother == mother 
        ensures this.father == father 
        ensures this.spouse == null 
        ensures this.civilState == Single
        ensures this.ancestors == (if this.mother != null then {this.mother} + this.mother.ancestors else {}) + (if this.father != null then {this.father} + this.father.ancestors else {})
        ensures Valid()
    {
        this.name := name;
        this.sex := sex;
        this.mother := mother;
        this.father := father;
        this.spouse := null;
        this.civilState := Single;
        this.ancestors := (if mother != null then {mother} + mother.ancestors else {}) + (if father != null then {father} + father.ancestors else {});
    }

    predicate Valid() 
        reads this, spouse
    {
        (this.spouse != null <==> this.civilState == Married) &&
        (this.mother != null ==> this.mother.sex == Feminine) &&
        (this.father != null ==> this.father.sex == Masculine) &&
        (this.spouse != null ==> this.spouse.spouse == this && this.spouse.sex != this.sex && this.spouse !in ancestors && (this.spouse.father != null ==> spouse.father != this.father) && (this.spouse.mother != null ==> spouse.mother != this.mother)) &&
        (ancestors == (if this.mother != null then {this.mother} + this.mother.ancestors else {}) + (if this.father != null then {this.father} + this.father.ancestors else {}))
    }

    method marry(spouse: Person)
        modifies this, spouse
        requires Valid()
        requires this.civilState != Married && this.civilState != Dead
        requires spouse.civilState != Married && spouse.civilState != Dead
        requires this.sex != spouse.sex
        requires spouse !in ancestors && this !in spouse.ancestors
        requires spouse.father != null ==> this.father != spouse.father 
        requires spouse.mother != null ==> this.mother != spouse.mother
        ensures Valid()
        ensures this.spouse == spouse
        ensures this.civilState == Married
        ensures spouse.civilState == Married
        ensures spouse.spouse == this
    {
        spouse.spouse := this;
        spouse.civilState := Married;
        this.spouse := spouse;
        this.civilState := Married;
    }

    method divorce()
        modifies this, spouse
        requires Valid()
        requires civilState == Married
        ensures Valid()
        ensures old(spouse).spouse == null
        ensures old(spouse).civilState == Divorced
        ensures this.spouse == null
        ensures this.civilState == Divorced
    {
        spouse.civilState := Divorced;
        spouse.spouse := null;
        this.spouse := null;
        this.civilState := Divorced;
    }

    method die()
        modifies this, spouse
        requires Valid()
        requires this.civilState != Dead
        ensures Valid()
        ensures (old(spouse) != null ==> old(spouse).civilState == Widow && old(spouse).spouse == null)
        ensures this.spouse == null
        ensures this.civilState == Dead
    {
        if spouse != null
        {
            spouse.civilState := Widow;
            spouse.spouse := null;
        }
        this.spouse := null;
        this.civilState := Dead;
    }
}

// Test scenario to cover all valid transitions of civil state (checking post-conditions).
method Main()
{
    var person := new Person("vitor", Masculine, null, null);
    var person2 := new Person("catarina", Feminine, null, null);

    person.marry(person2);

    assert person.spouse == person2;
    assert person2.spouse == person;
    assert person.sex != person2.sex;
}