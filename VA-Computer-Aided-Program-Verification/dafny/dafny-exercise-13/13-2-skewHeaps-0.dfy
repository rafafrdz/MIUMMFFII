/*

Skew Heaps
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// Skew Heaps are just binary trees holding the so-called heap property 
datatype Skew = Empty  |  Node (left: Skew, key: int, right: Skew)

// This is the Skew Heap invariant
predicate isSkew (t: Skew)
decreases t
{
   match t
      case Empty       => true
      case Node(l,x,r) => isSkew(l) && isSkew(r) &&  heap(l, x, r) 
}				

// This is the heap property at the root level
predicate heap(l:Skew, x:int, r:Skew) 
{
   forall z | z in mset(l) + mset(r) :: x <= z
}		
			
// this is the mathematical model implemented by a Skew Heap
function mset(t:Skew): multiset<int>
decreases t
{
   match t
      case Empty       => multiset{}		
      case Node(l,x,r) => mset(l) + multiset{x} + mset(r)	
}				

// This funtion joins two Skew heaps in amortized logarithmic time
function method join(t1:Skew, t2:Skew): (res:Skew)
decreases t1, t2
{
    match t1
     case Empty          => t2
     case Node(l1,x1,r1) => match t2
            case Empty          => t1
            case Node(l2,x2,r2) => if x1 <= x2
                                   then Node(join(r1,t2),x1,l1)
                                   else Node(join(t1,r2),x2,l2)
}
/*
   Exercises
*/
// 1. Provide the specification and verification of the above function method join

function method joinAux(t1 : Skew, t2 : Skew) : (res : Skew)
  requires  isSkew(t1) && isSkew(t2);
  ensures   isSkew(res);
  ensures   mset(res) == mset(t1) + mset(t2);
  decreases t1, t2;
  {
     match (t1, t2)
      case (Empty, _) => t2
      case (_, Empty) => t1
      case (Node(l1, x1, r1), Node(l2, x2, r2)) =>
         if x1 > x2
         then
            assert isSkew(joinAux(t1, r2));
            assert isSkew(l2);
            assert forall z | z in mset(l1) + mset(r1) + multiset{x1} :: x2 <= x1 <= z;
            assert mset(l2) <= mset(l2) + mset(r2) && forall z | z in mset(l2) :: x2 <= z;
            assert mset(r2) <= mset(l2) + mset(r2) && forall z | z in mset(r2) :: x2 <= z;
            assert mset(t1) == mset(l1) + mset(r1) + multiset{x1};
            assert mset(joinAux(t1, r2)) == mset(t1) + mset(r2);
            assert forall z | z in mset(joinAux(t1, r2)) + mset(l2) :: x2 <= z;
            assert heap(joinAux(t1, r2), x2, l2);
            Node(joinAux(t1, r2), x2, l2)
         else
            assert isSkew(l1);
            assert isSkew(joinAux(r1, t2));
            assert forall z | z in mset(l2) + mset(r2) + multiset{x2} :: x1 <= x2 <= z;
            assert mset(joinAux(r1, t2)) == mset(r1) + mset(t2);
            assert mset(t2) == mset(l2) + mset(r2) + multiset{x2};
            assert mset(l1) <= mset(l1) + mset(r1) && forall z | z in mset(l1) :: x1 <= z;
            assert mset(r1) <= mset(l1) + mset(r1) && forall z | z in mset(r1) :: x1 <= z;
            assert forall z | z in mset(joinAux(r1, t2)) + mset(l1) :: x1 <= z;
            assert heap(joinAux(r1, t2), x1, l1);
            Node(joinAux(r1, t2), x1, l1)
  }

// 2. Provide the specification, code and verification of the following function method
//    It inserts an element in a Skew Heap in amortized logarithmic time
//    Hint: use join
function method insert(x:int, t:Skew): (res:Skew)
  requires isSkew(t);
  ensures isSkew(res);
  ensures mset(res) == mset(t) + multiset{x};
{
  assert multiset{x} == mset(Node(Empty, x, Empty));
  joinAux(t, Node(Empty, x, Empty))
}

// 3. Provide the specification, code and verification of the following function method
//    It gets the minimum of a Skew Heap in constant time
function method min(t:Skew): (res: int)
  requires t.Node?;
  requires isSkew(t);
  ensures forall z | z in mset(t) :: res <= z
{
  assert mset(t) == mset(t.left) + mset(t.right) + multiset{t.key};
  t.key
}

// 4. Provide the specification, code and verification of the following function method
//    It deletes the minimum of a Skew Heap in amortized logarithmic time
//    Hint: use join
function method deleteMin(t:Skew): (res:Skew)
  requires isSkew(t);
  ensures  isSkew(res);
  ensures  t.Node? ==> mset(t) == mset(res) + multiset{t.key};
{
  match t
    case Empty => t
    case Node(l, n, r) => joinAux(l, r)
}
