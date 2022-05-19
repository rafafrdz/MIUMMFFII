class Node {
    var val: int;
    var next: Node?    
    ghost var repr: set<object>;
    ghost var model : seq<int>;

    predicate Valid() 
    reads this, repr
    decreases repr
    {
        (
        next == null ==> model == [val]) &&
        this in repr && (next != null ==> 
                next in repr && next.repr <= repr && this !in next.repr && next.Valid()
                    && model == [val] + next.model
            )
    }

    constructor (v: int) 
    ensures Valid()
    ensures fresh(repr)
    {
        val  := v;
        next := null;
        repr := {this};
        model := [v];
    }

   function length() : nat
   decreases repr, this
    reads this
    reads repr
    requires Valid()
    ensures length () == |model|
    {
        if next == null then 1 else 1 + next.length()
    }
    
    method append (node: Node)
    decreases repr
    modifies this, repr
    
    requires Valid() && node.Valid()
    requires node.repr - repr == node.repr
    
    ensures Valid()
    ensures repr == old(repr) + node.repr
    ensures model == old(model) + node.model
    
    {
        if next == null {next := node;}
        else { next.append(node); }

        repr := repr + next.repr;
        model := [val] + next.model;

    }
}

class List {
    var first : Node?;
   ghost var repr: set<object>;
   ghost var model: seq<int>;


    predicate Valid() 
    reads this, repr
    {
        this in repr && (if   first != null
                       then first in repr
                          && model == first.model
                          && first.repr <= repr
                          && this !in first.repr
                          && first.Valid()
                       else model == [])
    }

    constructor () 
    ensures Valid()
    ensures fresh(repr)
    ensures model == []
    {
        first := null;
        repr := {this};
        model := [];
    }    

    function length (): nat
    reads this
    reads repr
    requires Valid()
    ensures length () == |model|
    {
        if first == null then 0 else first.length()
    }

    // This adds an element to the left of the list
    method add(v: int)
    modifies repr;
    requires Valid();
    ensures  Valid();
    ensures  fresh(repr - old(repr));
    ensures  model == [v] + old(model);
    {
        var node := new Node(v);
        if first != null {
            node.next  := first;
            node.repr  := node.repr + first.repr;
            node.model := [v] + first.model;
        }
        first := node;
        model := node.model;
        repr  := {this} + node.repr;
    }
    // This method adds an element to the end of the list
    method append(v: int)
            modifies repr;
        requires Valid();
        ensures  Valid();
        ensures  fresh(repr - old(repr));
        ensures  model == old(model) + [v];
    {
        var node := new Node(v);
        if first == null {
            first := node;
        } else {
            first.append(node);
        }
        model := first.model;
        repr  := repr + node.repr;
    }
 }

method Main ()
{
    var l := new List();
    assert l.length () == 0;
    l.add(1);
    assert l.length () == 1;
    l.add(2);
    assert l.length() == 2;
    l.append(7);
    //assert l.model() == [2,1,7];
}

/*
   Exercise: 
   
   implement and verify append methods in classes Node and List,
   which adds a new element to the right of the list.

    requires Valid()
    ensures Valid()
    ensures model == old(model)+ [v]
    modifies repr 
 
*/  
