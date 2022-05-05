
class Node {
    var val : int;
    var next : Node?;
    ghost var repr : set<object>;
    ghost var model : seq<int>;

    predicate Valid()
    reads this, repr;
    decreases repr;
    {
        this in repr &&
        (if next == null then model == [val]
        else 
        next in repr &&
        next.repr <= repr &&
        this !in next.repr &&
        next.Valid() &&
        model == [val] + next.model)
    }

    constructor (v: int)
        ensures Valid();
        ensures model == [v];
        ensures fresh(repr);
    {
        val  := v;
        next := null;
        repr := {this};
        model := [v];
    }

    function length() : nat
        reads repr;
        requires Valid();
        ensures  length () == |model|;
        decreases this, repr;
    { if next == null then 1 else 1 + next.length() }

    method append (node : Node)
        requires Valid();
        requires node.Valid();
        requires node.repr - repr == node.repr;
        ensures  Valid();
        ensures  repr==old(repr)+ node.repr;
        ensures  model==old(model)+ node.model;
        modifies repr;
        decreases repr;
    {
        if next != null { next.append(node); repr:= repr+ next.repr; model:= [val] + next.model;}
        else {next  := node; repr  := repr + node.repr; model := [val] + node.model;}
    }
}

class List {
    var first : Node?;
    ghost var repr : set<object>;
    ghost var model : seq<int>;

    predicate Valid()
    reads this, repr;
    {
        (
            if first != null then
            first in repr &&
            model == first.model &&
            first.repr <= repr &&
            this !in first.repr &&
            first.Valid()
            else model == []
            ) && this in repr
    }

    constructor () 
    ensures Valid();
    ensures fresh(repr);
    ensures model == [];
    { first := null; repr := {this}; model := [];}    

    function length (): nat
    reads repr
    requires Valid()
    ensures  length () == |model|
    { if first == null then 0 else first.length() }

    method add (v : int)
        modifies repr
        requires Valid()
        ensures  Valid()
        ensures  fresh(repr - old(repr))
        ensures  model == [v] + old(model)
    {
        var node := new Node(v);
        if first != null {
        node.repr:=node.repr+first.repr;
        node.next:=first;
        node.model:=[v]+first.model;
        }
        model:=node.model;
        first:=node;
        repr:={this}+node.repr;
    }

    method append(v:int)
        modifies repr
        requires Valid()
        ensures  Valid()
        ensures  fresh(repr-old(repr))
        ensures  model==old(model)+[v]
    {
        var node:=new Node(v);
        if first!=null { first.append(node); }
        else { first := node;}
        repr:=repr+node.repr;
        model:=first.model;
        
    }
}

method Main ()
{
    var l := new List();
    assert l.model == [];
    assert l.length () == 0;
    l.add(1);
    assert l.model == [1];
    assert l.length () == 1;
    l.add(2);
    assert l.model == [2,1];
    assert l.length() == 2;
    l.append(7);
    assert l.length() == 3;
    assert l.model == [2,1,7];
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
