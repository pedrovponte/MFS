/* 
* Specification, implementation and verification of a Set implemented with an array (resizable).
* Illustrates the usage of ghost variables and abstraction/refinment relations to better separate
* specification (interface) and implementation.
* Pre/post-conditions of public operations are defined in terms of the abstract state variables.
* FEUP, M.EIC, MFS, 2021/22.
*/

class {:autocontracts} ArraySet<T(==)> {
  // (Public) ghost variables used for specification purposes only  
  ghost var elems: set<T>;
 
  // (Private) concrete variables with internal representation.
  var list: array<T>;
  var used : nat;
  const initializer: nat -> T;

  // (Private) predicate that formalizes the class invariant.  
  predicate Valid() {
    // constraints on concrete representation
    used <= list.Length 
    && list.Length > 0
    && (forall i, j :: 0 <= i < j < used ==> list[i] != list[j]) // no duplicates
    // abstraction relation (between concrete and abstract variables)
    && elems == set x | x in list[..used] 
  }

  // (Public) Constructor, initializes this set as empty.
  constructor (initializer: nat -> T)
    ensures elems == {}
  {
    // initialize concrete state variables
    list := new T[10] (initializer); 
    used := 0;
    this.initializer := initializer;
    // initialize ghost state variable
    elems := {};
  }

  // (Public) Checks if this set contains an element x.
  predicate method contains(x: T) 
    ensures contains(x) <==> x in elems  
  {
    // search concrete state variables
    exists i :: 0 <= i < used && list[i] == x
  }

  // (Public) Inserts a new element x into this set.
  method insert(x : T)
    requires x !in elems
    ensures elems == old(elems) + {x}
  {
    // allocate larger array if needed
    if used == list.Length { 
      grow();
    }
    // update concrete variables
	  list[used] := x;
    // trick: remind Dafny that other positions were not changed!!
    assert list[..used] == old(list[..used]);
    used := used + 1;
    // update ghost variable
    elems := elems + {x};
  }

  // (Private) Auxiliary method to reallocate the array.
  method grow()
    ensures list.Length > old(list.Length)
    ensures list[..used] == old(list[..used])
  {
    var oldList := list;
    list := new T[ 2 * list.Length](initializer);
    forall i | 0 <= i < used {
        list[i] := oldList[i];
    }
    // trick: remind Dafny thar values were not changed (to prove Valid)
    assert list[..used] == old(list[..used]);
  }

  // (Public) Deletes an existing element x from this set in time O(n).
  method delete(x: T)
    requires x in elems
    ensures elems == old(elems) - {x} 
  {
    // update concrete variables
    var i :| 0 <= i < used && list[i] == x;
    list[i] := list[used-1];
    // remind Dafny that other positions were not changed!!
    assert forall j :: 0 <= j < used && j != i ==> list[j] == old(list[j]);
    used := used-1;
    // update ghost variable
    elems := elems - {x};
  }

  // (Public) Obtains the size of the set
  function method size(): nat
    ensures size() == |elems|  
  {
    // recalls property to prove the post-condition
    assert elems == elemsN(used);
    sizeProp(used);
    // now return the expression 
    used
  }

  // Same as elems, but for a part of the list.
  function elemsN(n: nat): set<T> 
     requires n <= used
  {
      set x | x in list[..n]
  }
  
  // Proves (by induction on the length (n) of list) that, since the list has no 
  // duplicates, the size of the corresponding set equals the length of the list. 
  lemma sizeProp(n: nat)
   requires n <= used
   ensures |elemsN(n)| == n
  {
    if n > 0 { 
      // recall the same property for a simpler case (n-1)
      sizeProp(n-1);
      // fact needed to complete the proof
      assert elemsN(n) == elemsN(n-1) + {list[n-1]};
    }
  }
}

// A simple test scenario checked statically.
method testSet() {
  var s := new ArraySet<int>(n => 0);
  s.insert(2);
  s.insert(5);
  assert s.size() == 2;
  assert s.contains(2);
  assert s.contains(5);
  assert !s.contains(1);
  s.delete(2);
  assert s.size() == 1;
  assert s.contains(5);
  assert !s.contains(2);
  s.delete(5);
  assert !s.contains(5);
  assert s.size() == 0;
}


// Examples of test cases with invalid inputs
// method testInvalidDelete() {
//   var s := new ArraySet();
//   s.insert(1);
//   s.delete(2);
// }

// method testInvalidInsert() {
//   var s := new ArraySet();
//   s.insert(1);
//   s.insert(1);
// }
