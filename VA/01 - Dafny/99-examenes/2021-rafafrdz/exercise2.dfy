/*
    Final Exam, June 10th, 2021
    Exercise on algebraic datatypes

    You are given the definitions below and you are asked to represent
    sets of integers as sorted lists of integers without duplicates

    You are also given the specifications of the emptySet, singleton, union and 
    intersection functions. Your task consists of implementing and verifying 
    them. The cost of union and intersection should in O(n1+n2), being n1 and n2
    the cardinals of the sets received as arguments. 
*/

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate noDup <T> (l:List<T>)
{
    match l
        case Nil        => true
        case Cons(x,xs) => x !in elems(xs) && noDup(xs)
}

predicate sorted (l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems <T> (l:List<T>) : set<T>
{
    match l
       case Nil         => {}
       case Cons(x, xs) => {x} + elems(xs)
}

///////////////////////////////////////////////////////////////

function method emptySet() : (res:List<int>)
ensures elems(res) == {}
{
	Nil
}


function method singleton(x:int): (res:List<int>)
ensures elems(res) == {x} && noDup(res)
{
	Cons(x, Nil)
}


function method union (l1:List<int>,l2:List<int>): (res: List<int>)
decreases l1, l2
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) + elems (l2)
{
	match (l1, l2)
		case (Nil, _) => l2
		case (_, Nil) => l1
		case(Cons(x, xs), Cons(y, ys)) =>

		if x < y then
		nodup(l1, l2);
		Cons(x, union(xs, l2))

		else if x > y then
		nodup(l2, l1);
		Cons(y, union(l1, ys))

		else Cons(x, union(xs, ys))
}

lemma {:induction l1, l2} nodup(l1: List<int>, l2: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures l1.Cons? && l2.Cons? && l1.head < l2.head ==> l1.head !in elems(l2)
{}





function method inters (l1:List<int>,l2:List<int>): (res: List<int>)
decreases l1, l2
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) * elems(l2)
{
	match (l1, l2)
		case (Nil, _) =>
			assert elems(Nil) == elems(l1) * elems(l2);
			Nil
		case (_, Nil) => 
			assert elems(Nil) == elems(l1) * elems(l2);
			Nil
		case (Cons(x, xs), Cons(y, ys)) =>
		
		if x < y then
			assert sorted(inters(xs, l2)) && noDup(inters(xs, l2));
			assert elems(inters(xs, l2)) == elems(xs) * elems (l2);
		inters(xs, l2)
		
		else if x > y then
			assert sorted(inters(l1, ys)) && noDup(inters(l1, ys));
			assert elems(inters(l1, ys)) == elems(l1) * elems (ys);
		inters(l1, ys)
		
		else
			sortedHead(xs);
			assert sorted(Cons(x, inters(xs, ys))) && noDup(Cons(x, inters(xs, ys)));

			assert {x} + elems(inters(xs, ys)) == elems(l1) * elems (l2);
			assert elems(Cons(x, inters(xs, ys))) == elems(l1) * elems (l2);
			assert x !in elems(inters(xs,ys));

		Cons(x, inters(xs, ys))
}


lemma {:induction l1} sortedHead(l1: List<int>)
requires sorted(l1) && noDup(l1)
ensures l1.Cons? ==> forall k : int :: k in elems(l1.tail) ==> l1.head < k
{}



// lemma {:induction l1, l2} notin(l1: List<int>, l2: List<int>)
// requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
// ensures l1.Cons? && l2.Cons? && l1.head == l2.head ==> l1.head !in elemsl1.tail && l1.head !in l2.tail
// {
// 	match (l1, l2)
// 	case (Nil, _) => 
// 	case (_, Nil) =>
// 	case (Cons(x, xs), Cons(y, ys)) =>
// 		assert sorted(l1);
		
// }