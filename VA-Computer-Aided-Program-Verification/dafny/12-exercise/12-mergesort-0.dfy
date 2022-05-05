datatype List<T> = Nil | Cons(head : T, tail : List<T>)

predicate sorted(l : List<int>)
{
    match l
       case Nil         => true
       case Cons(x, xs) =>
            match xs
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems<T>(l : List<T>) : multiset<T>
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
         res := l;}
  else {
         var (left, right) := split(l);
         var resl := mergesort(left);
         var resr := mergesort(right);
         res := merge(resl,resr);
    }
}

function method length<T>(l : List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

// Split by even and odd position in left and right, respectly
function method split<T>(l : List<T>) : (res : (List<T>, List<T>))
  ensures elems(l) == elems(res.0) + elems(res.1);
  ensures length(l) >= 2 ==> (length(split(l).0) < length(l) && length(split(l).1) < length(l));
{
  match l
    case Nil         => (Nil, Nil)
    case Cons(x, xs) => var (r1, r2) := split(xs);
      if length(r1) > length(r2)
      then (r1, Cons(x, r2))
      else (Cons(x, r1), r2)
}

function method merge(l1:List<int>, l2:List<int>) : (res:List<int>)
requires sorted(l1) && sorted(l2)
ensures sorted (res)
ensures elems(res) == elems(l1) + elems(l2)
{
   match (l1, l2)
      case (Nil, Nil) => Nil
      case (_, Nil) => l1
      case (Nil, _) => l2
      case (Cons(x1, xs1), Cons(x2, xs2)) =>
      if x1 <= x2 then Cons(x1, merge(xs1, l2))
      else Cons(x2, merge(l1, xs2))
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


function partition (l : List<int>, x : int)  : (res : (List<int>,List<int>))
  ensures forall z | z in elems(res.0) :: z <= x;
  ensures forall z | z in elems(res.1) :: z > x;
  ensures elems(l) == elems(res.0) + elems(res.1);
  ensures length(res.0) <= length(l);
  ensures length(res.1) <= length(l);
{
  match l
    case Nil => (Nil, Nil)
    case Cons(y, ys) =>
      var (r1, r2) := partition(ys, x);
      if y <= x then (Cons(y, r1), r2)
      else (r1, Cons(y, r2))
}


function quicksort (l : List<int>) : (res : List<int>)
  ensures sorted(res);
  ensures elems(l) == elems(res);
  decreases length(l);
{
   match l
      case Nil => Nil
      case Cons(x,xs) =>
                        var (l1,l2) := partition(xs,x);
                        var left    := quicksort(l1);
                        var right   := quicksort(l2);
                        consSmaller(x, right);
                        sortedConcat(left, Cons(x, right));
                        concat(left,Cons(x,right))
}

function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures elems(res) == elems(l1) + elems(l2)
{
   match l1 
      case Nil => l2
      case Cons(x, xs) => Cons(x, concat(xs, l2))
}

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
    case (0, _) => (Nil, l)
    case (_, Nil) => (Nil, Nil)
    case (n, Cons(x, xs)) =>
                        var (r1, r2) := splitAt(n - 1, xs);
                        (Cons(x, r1), r2)
}

method mergesort2(l : List<int>) returns (res : List<int>)
  ensures sorted(res);
  ensures elems(l) == elems(res);
  decreases length(l);
{
  if length(l) < 2
  {
    sortedSmallList(l);
    res := l;
  }
  else
  {
    var (left, right) := splitAt(length(l)/2, l);
    var resl := mergesort(left);
    var resr := mergesort(right);
    res := merge(resl,resr);
  }
}


// 2. Complete the verification of quicksort

// There is to write an auxiliary lemma that say concat two sorted list
// and the elements of the left one is less than the element of the right one
lemma sortedConcat(l1: List<int>, l2: List<int>)
requires sorted(l1) && sorted(l2)
requires forall x, y | x in elems(l1) && y in elems(l2):: x <= y
ensures sorted(concat(l1, l2))
{
   match (l1, l2)
      case (Nil, _) =>
      case (Cons(x, Nil), Nil       ) =>
      case (Cons(x, Nil), Cons(y, _)) => assert x in elems(l1) && y in elems(l2);
      case (Cons(x, xs ), _ ) => assert elems(xs) == (elems(l1) - multiset{x});
}

lemma consSmaller(x : int, l : List<int>)
  requires sorted(l);
  requires forall y | y in elems(l) :: x <= y;
  ensures sorted(Cons(x, l))
{
  match l
    case Nil =>
    case Cons(y, ys) => if x >= y {
        assert y in elems(l);
        assert exists z | z in elems(l) :: x >= z;
      }
}

// 3. Prove the following Lemma

lemma uniqueSortedList(l1:List<int>,l2:List<int>)
requires sorted(l1) && sorted(l2) && elems(l1)==elems(l2)
ensures l1 == l2
