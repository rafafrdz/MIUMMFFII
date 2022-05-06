datatype List<T> = Nil | Cons(head:T, tail:List<T>)

function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}


predicate sorted2(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, Nil) => true
       case Cons(x, Cons(y, ys)) => x <= y && sorted(Cons(y, ys))
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

function elems<T> (l:List<T>) : multiset<T>
decreases l
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

function sum(l:List<int>): (res:int)
{
    match l 
        case Nil         => 0
        case Cons(y, ys) => y + sum(ys)
}

function insert(x: int, l:List<int>): (res:List<int>)
requires sorted(l)
ensures sorted(res)
ensures elems(res) == elems(l) + multiset{x}
{
    match l
        case Nil => Cons(x, Nil)
        case Cons(y, ys) =>  if x <= y then Cons(x, l) else Cons(y, insert(x, ys))
}

function delete<T> (x: T, l:List<T>): (res:List<T>)
ensures elems(res) == elems(l) - multiset{x}
{
    match l
        case Nil => Nil
        case Cons(y, ys) => if x == y then ys else Cons(y, delete(x, ys))
}

function search<T> (x: T, l:List<T>): (res:bool)
ensures res == (x in elems(l))
{
    match l
        case Nil => false
        case Cons(y, ys) => if x == y then true else search(x, ys)
}

function min(x:nat, y:nat): (res:nat)
{
    if x <=y then x else y
}

function take<T> (n: nat, l:List<T>): (res:List<T>)
decreases l, n
ensures length(res) == min (n, length(l))
{
    match l
        case Nil => Nil
        case Cons(x, xs) => if n==0 then Nil else Cons(x, take(n-1, xs))
}

function drop<T> (n: nat, l:List<T>): (res:List<T>)
decreases l, n
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match l
        case Nil => Nil
        case Cons(x, xs) => if n==0 then l else drop(n-1, xs)
}

function drop2<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match (n,l)
        case (0, _) => l
        case (_, Nil) => Nil
        case (_, Cons(_, xs)) => drop(n-1, xs)
}

function method splitWhileNE <T(==)> (x: T, l:List<T>): (res:(List<T>, List<T>))
decreases l
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match l
      case Nil        => (Nil,Nil)
      case Cons(y,ys) => if x == y then (Nil, l)
                         else var (l1,l2) := splitWhileNE (x, ys);
                              (Cons(y,l1), l2)
}

function isort (l: List<int>) : (res: List<int>)
decreases l
ensures sorted(res)
ensures elems(res) == elems(l)
{
    match l
        case Nil => Nil
        case Cons(x, xs) => insert(x, isort(xs))
}
/*
   Exercises
*/


// 1. write the code of this function and verify it (but do not use take and drop)
// No usar ni take ni drop
function method split<T> (n: nat, l:List<T>): (res:(List<T>, List<T>)) // (take, drop)
decreases n, l
ensures length(res.0) == min (n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match (n, l)
        case (0,_) => (Nil, l)
        case (_, Nil) => (l, l)
        case (n, Cons(x, xs)) =>
            var (l1, l2) := split(n-1, xs);
            (Cons(x, l1), l2)
}


// 2. specify, write the code of this function, and verify it
function method reverse(l:List<int>): (res:List<int>)
  decreases l
  ensures elems(l) == elems(res);
  ensures length(l) == length(res);
  ensures l != Nil ==> res == concat(reverse(l.tail), Cons(l.head, Nil));
{
    match l
        case Nil => Nil
        case Cons(x, xs) =>
            var ress := reverse(xs);
            var ys := Cons(x, Nil);
            concat(ress, ys)

}


// 3. specify, write the code of this function, and verify it
function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
  decreases l1, l2
  ensures elems(res) == elems(l1) + elems(l2);
  ensures take(length(l1), res) == l1;
  ensures drop(length(l1), res) == l2;
  ensures length(res) == length(l1) + length(l2);
  ensures l1 != Nil || l2 != Nil ==> res != Nil;
{
  match l1
    case Nil => l2
    case Cons(x, xs) => Cons(x, concat(xs, l2))
}


// 4. prove it
lemma concatAssoc(l1:List<int>,l2:List<int>,l3:List<int>)
ensures concat(l1,concat(l2,l3))==concat(concat(l1,l2),l3)
{}


// 5. prove it
// lemma reverseIdemp(l:List<int>)
// ensures reverse(reverse(l))==l