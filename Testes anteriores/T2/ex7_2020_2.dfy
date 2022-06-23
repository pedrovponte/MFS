class {:autocontracts} Customer { }
class {:autocontracts} Book {
    const id: nat;
    var holder: Customer?; // current rental holder of the book, or null
    var queue: seq<Customer>; // list of customers with pending rental requests,
                            // by temporal order (oldest request at position 0)

    /* Class invariant */
    predicate Valid() // a)
        reads this
    {
        (holder != null ==> holder !in queue) &&
        forall i, j :: 0 <= i < j < |queue| ==> queue[i] != queue[j]

    }
    /* Operations */
    constructor (id: nat)
    method pickBook(customer: Customer) // b)
        requires holder == null
        requires (|queue| > 0 && queue[0] == customer) || |queue| == 0
        ensures holder == customer
        ensures queue == old(if queue == [] then queue else queue[1..])
    {

    }
     
    method reserveBook(customer: Customer)
    method returnBook(customer: Customer)
    method cancelReservation(customer: Customer) // c)
        requires customer in queue && |queue| > 0
        ensures customer !in queue && |queue| == old(|queue|) - 1 
    {

    }
}