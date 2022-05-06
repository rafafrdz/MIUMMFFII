/*

    This is Williams minimum heap implemented as a class
    Specified and verified by Ricardo Peña, January 2019

*/


// Rafael Fernandez Ortiz

class Williams_heap {
    var v: array<int>;
    var next: nat;
    ghost var repr: set<object>;

    // It replaces the usual Valid() predicate. It specifies that v[j..next) is a minHeap
    
    // Generalized isHeap
    predicate isHeap () 
    reads this, v
    {
        this in repr && v in repr &&
        0 <= next <= v.Length && 
        forall i | 1 <= i < next :: v[(i-1)/2] <= v[i]
    }
    
 // Constructor
    constructor (size: nat) 
    ensures isHeap() && v.Length == size && next == 0
    ensures fresh (repr)
    {
        v := new int [size];
        next := 0;
        repr := {this, v};
    }

    // Lemmas auxiliares
    // ####################################
    lemma {:induction j} aux_lemma2(j: nat)
    requires isHeap();
    requires 0 <= j < next;
    ensures  v[0] <= v[j];
  {}

    lemma aux_lemma()
    requires isHeap();
    ensures  forall j | 0 <= j < next :: v[0] <= v[j];
    { forall j | 0 <= j < next ensures v[0] <= v[j] { aux_lemma2(j); }}

    function AuxSet() : multiset<int>
    reads    this, v;
    requires isHeap();
    ensures  next > 0 ==> forall e | e in AuxSet() :: v[0] <= e;
  {
    aux_lemma();
    multiset(v[..next])
  }
  // ####################################


// Get Min
    function method min(): int
    reads repr;
    requires isHeap();
    requires next > 0;
    ensures min() in AuxSet();
    ensures forall x | x in AuxSet() :: min() <= x;
    { v[0] }


// Insert
    method insert (val: int)
    requires isHeap()
    requires next < v.Length
    modifies repr
    ensures isHeap() 
    ensures next == old(next) + 1
    ensures repr == old(repr) 
    ensures v == old(v);
    ensures old(AuxSet()) + multiset{val} == AuxSet();
    {
        v[next] := val;next := next + 1;
        float ();
    }

    method float()
    requires 0 < next <= v.Length
    requires this in repr && v in repr; // isHeap() does not hold here
    requires forall i | 0 < i < next-1 :: v[(i-1)/2] <= v[i]
    modifies v
    ensures repr == old(repr)
    ensures isHeap()
    ensures  multiset(v[..next]) == old(multiset(v[..next]));
    ensures  old(next) == next;
    {
        var j := next-1;
        while j > 0 && v[(j-1)/2] > v[j] 
            invariant 0 <= j <= next-1 < v.Length
            invariant forall i | 0 < i < next :: i != j ==> v[(i-1)/2] <= v[i]
            invariant multiset(v[..next]) == old(multiset(v[..next]));
            invariant j > 0 && 2*j+1< next ==> v[(j-1)/2] <= v[2*j+1] 
            invariant j > 0 && 2*j+2< next ==> v[(j-1)/2] <= v[2*j+2]

        {
            v[(j-1)/2], v[j] := v[j], v[(j-1)/2];
            j := (j-1)/2;
        }
}

// Delete
    method deleteMin ()
    requires isHeap()
    requires 0 < next
    modifies repr
    ensures isHeap()
    ensures AuxSet() == old(AuxSet() - multiset{v[0]})
    ensures next == old(next) - 1
    ensures repr == old(repr)
    {
        v[0] := v[next-1]; next := next - 1;
        sink();
    }

    // It sinks v[s] in a heap ending in v[l-1]
    method sink()
    requires next <= v.Length
    requires this in repr && v in repr    // isHeap() does not hold here
    requires forall i | 0 < i < next :: (i-1)/2 != 0 ==> v[(i-1)/2] <= v[i]
    modifies v
    ensures repr == old(repr)
    ensures isHeap()
    ensures multiset(v[..next]) == old(multiset(v[..next]))
  {
    var j := 0;
    while 2*j+1 < next
      invariant forall k | 1 <= k < next :: (k-1)/2 != j ==> v[(k-1)/2] <= v[k]
      invariant multiset(v[..next]) == old(multiset(v[..next]))
      invariant j >= 1 && 2*j+1< next ==> v[(j-1)/2] <= v[2*j+1]
      invariant j >= 1 && 2*j+2< next ==> v[(j-1)/2] <= v[2*j+2]
    {
      var m: nat;
      if 2*j+2 < next && v[2*j+2] <= v[2*j+1] {
        m := 2*j+2;  // right son is smaller
      } else {
        m := 2*j+1;  // left son is smaller
      }
      if v[j] > v[m] {
        v[j], v[m] := v[m], v[j];
        j  := m;
      } else { break; }								
        }
    }
}
method heapsort_with_extra_space (a: array<int>)
modifies a
{
    var queue := new Williams_heap(a.Length);
    var i := 0;
    while i < a.Length 
       invariant queue.isHeap() 
       invariant a.Length == queue.v.Length
       invariant i == queue.next <= queue.v.Length 
       invariant fresh(queue.repr)
    {
        queue.insert(a[i]);
        i := i + 1;
    }
    i := 0;
    while i < a.Length 
       invariant queue.isHeap() 
       invariant queue.next == a.Length - i
       invariant fresh(queue.repr)
    {
        assert queue.isHeap(); 
        assert queue.next > 0;
        a[i] := queue.min(); 
        queue.deleteMin();
        i := i + 1;
    }
}

/*

   Exercise: add an observable  model function or model ghost field to the class, 
   write suitable postconditions in terms of the observable model, and prove 
   that array 'a' becomes sorted at the end of the second while loop
   
*/