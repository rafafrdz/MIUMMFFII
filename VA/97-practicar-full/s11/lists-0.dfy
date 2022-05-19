datatype List<T> = Nil | Cons(head:T, tail:List<T>)

function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

predicate sorted(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

predicate sorted2(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, Nil) => true
       case Cons(x, Cons(y, ys)) => x <= y && sorted(Cons(y, ys))
}

function elems<T> (l:List<T>) : multiset<T>
decreases l
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

function sum(l:List<int>): (res:int)
decreases l
{
    match l 
        case Nil         => 0
        case Cons(y, ys) => y + sum(ys)
}

function insert(x: int, l:List<int>): (res:List<int>)
decreases l 
requires sorted(l)
ensures sorted(res)
ensures elems(res) == elems(l) + multiset{x}
{
    match l
        case Nil => Cons(x, Nil)
        case Cons(y, ys) => if x < y then Cons(x, l) else Cons(y, insert(x, ys))
}


function delete<T> (x: T, l:List<T>): (res:List<T>)
decreases l
ensures elems(res) == elems(l) - multiset{x}
{
    match l
        case Nil =>  Nil
        case Cons(y, ys) => if x==y then ys else Cons(y, delete(x, ys))
}


function search<T> (x: T, l:List<T>): (res:bool)
decreases l
ensures res == (x in elems(l))
{
    match l
        case Nil =>  false
        case Cons(y, ys) => x==y || search(x, ys)
}

function min(x:nat, y:nat): (res:nat)
{
    if x <=y then x else y
}

function take<T> (n: nat, l:List<T>): (res:List<T>)
decreases l
ensures length(res) == min (n, length(l))
{
    match (n, l)
        case (_,Nil) => Nil
        case (0, _) => Nil
        case (_, Cons(x, xs)) => Cons(x, take(n-1, xs))
}

function drop<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match (n, l)
        case (_, Nil) => Nil
        case (0, _) => l
        case (_, Cons(x, xs)) => drop(n-1, xs)
}

function method splitWhileNE <T(==)> (x: T, l:List<T>): (res:(List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match l
      case Nil        => (Nil,Nil)
      case Cons(y,ys) => if x == y then (Nil, l)
                         else var (l1,l2) := splitWhileNE (x, ys);
                              (Cons(y,l1), l2)
}

/*
   Exercises
*/

// 1. write the code of this function and verify it (but do not use take and drop)

function method split<T> (n: nat, l:List<T>): (res:(List<T>, List<T>))
ensures length(res.0) == min (n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match (n, l)
        case (_, Nil) => (Nil, Nil)
        case (0, _) => (Nil, l)
        case (_, Cons(x, xs)) =>
            var (tks, drpd) := split(n-1, xs);
            (Cons(x, tks), drpd)

}

// 2. specify, write the code of this function, and verify it

function method reverse(l:List<int>): (res:List<int>)
ensures length(l) == length(res)
ensures elems(l) == elems(res)
{
    match l
        case Nil => Nil
        case Cons(x, xs) =>
            var hds:= reverse(xs);
            concat(hds, Cons(x, Nil))
}
// 3. specify, write the code of this function, and verify it

function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures length(l1) + length(l2) == length(res)
ensures elems(l1) + elems(l2) == elems(res)
{
    match (l1, l2)
        case (_,Nil) => l1
        case (Nil, _) => l2
        case (Cons(x, xs), _) =>
            Cons(x, concat(xs, l2))
}


// 4. prove it

lemma concatAssoc(l1:List<int>,l2:List<int>,l3:List<int>)
ensures concat(l1,concat(l2,l3))==concat(concat(l1,l2),l3)
{}

// 5. prove it

lemma reverseConcatList(xs :List<int>, ys: List<int>)
ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs))



lemma reverseIdemp(l:List<int>)
ensures reverse(reverse(l))==l
{
    match l
        case Nil =>
        case Cons(x, xs) =>
        calc == {
            reverse(reverse(l));
            reverse(reverse(Cons(x, xs)));
            reverse(reverse(concat(Cons(x, Nil), xs)));
            {reverseConcatList(Cons(x, Nil), xs);}
            reverse(concat(reverse(xs), Cons(x, Nil)));
            {reverseConcatList(reverse(xs), Cons(x, Nil));}
            concat(Cons(x, Nil), reverse(reverse(xs)));
            {reverseIdemp(xs);}
            concat(Cons(x, Nil), xs);
            Cons(x, xs);
            l;            
        }
}


