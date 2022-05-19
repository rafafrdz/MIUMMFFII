datatype List<T> = Nil | Cons(head:T, tail:List<T>)

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
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

method mergesort(l:List<int>) returns (res:List<int>)
ensures sorted(res) 
ensures elems(l) == elems(res)
decreases length(l)
{
  if length(l) < 2
  {
     sortedSmallList(l);
     res := l;
   }
  else {
         var (left, right) := split(l);
         var resl := mergesort(left);
         var resr := mergesort(right);
         res := merge(resl,resr);
    }
}

function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

function method split<T> (l:List<T>): (res: (List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(l) >= 2 ==> (length(split(l).0) < length(l) && length(split(l).1) < length(l))
{
   match l
      case Nil => (Nil, Nil)
      case Cons(x, Nil) => (l, Nil)
      case Cons(x, xs) =>
      var (lhs, rhs) := split(xs);
      if length(lhs) > length(rhs) then (lhs, Cons(x, rhs))
      else (Cons(x, lhs), rhs)
         
}

function method merge(l1:List<int>, l2:List<int>) : (res:List<int>)
requires sorted(l1) && sorted(l2)
ensures sorted (res)
ensures elems(res) == elems(l1) + elems(l2)
{
   match (l1, l2)
      case (_, Nil) => l1
      case (Nil, _) => l2
      case (Cons(x, xs), Cons(y, ys)) => 
      if x <= y then Cons(x, merge(xs, l2))
      else Cons(y, merge(l1, ys))
}



lemma splitLengths(l:List<int>)
requires length(l) >= 2 
ensures length(split(l).0) < length(l) && 
        length(split(l).1) < length(l)
        {}



lemma sortedSmallList (l:List<int>)
requires length(l) < 2
ensures  sorted(l)
{}


function partition (l:List<int>, x:int)  : (res: (List<int>,List<int>))
ensures forall z | z in elems(res.0) :: z <= x
ensures forall z | z in elems(res.1) :: z > x
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(res.0) <= length(l)
ensures length(res.1) <= length(l)
{
   match l
      case Nil => (Nil, Nil)
      case Cons(y, ys) =>
         var (lhs, rhs) := partition(ys, x);
         if y <= x then (Cons(y, lhs), rhs)
         else (lhs, Cons(y, rhs))
}


function quicksort (l:List<int>): (res:List<int>)
ensures sorted(res) 
ensures elems(l) == elems(res)
decreases length(l)
{
   match l
      case Nil        => Nil
      case Cons(x,xs) => var (l1,l2) := partition(xs,x);
                         var left    := quicksort(l1);
                         var right   := quicksort(l2);
                         auxSortedCons(x, right);
                         sortedConcat(left, Cons(x,right));
                         concat(left,Cons(x,right))                         
}

function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures elems(res) == elems(l1) + elems(l2)

lemma sortedConcat(l1: List<int>, l2: List<int>)
requires sorted(l1) && sorted(l2)
ensures elems(l1) + elems(l2) == elems(concat(l1, l2))
ensures sorted(concat(l1, l2))


lemma auxSortedCons(x: int, xs: List<int>)
requires sorted(xs)
requires forall z :: z in elems(xs) ==> z > x
ensures sorted(Cons(x, xs))



/*
   Exercises
*/

// 1. Modify and verify mergesort using function splitAt n/2 instead of split
function method splitAt<T>(n : nat, l : List<T>) : (res : (List<T>, List<T>))
decreases n, l;
ensures elems(l) == elems(res.0) + elems(res.1);
ensures length(l) >= 2 ==> (length(split(l).0) < length(l) && length(split(l).1) < length(l));
{
   match (n, l)
      case (_, Nil) => (Nil, Nil)
      case (0, _) => (l, Nil)
      case (_, Cons(x, xs)) =>
         var (lhs, rhs) := splitAt(n-1, xs);
         (Cons(x, lhs), rhs)
}


// 2. Complete the verification of quicksort

// 3. Prove the following Lemma

lemma uniqueSortedList(l1:List<int>,l2:List<int>)
requires sorted(l1) && sorted(l2) && elems(l1)==elems(l2)
ensures l1 == l2
