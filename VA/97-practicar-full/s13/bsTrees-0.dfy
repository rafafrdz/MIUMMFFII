/*

Binary Search Trees (BST)
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// BSTs are binary trees having unique keys and sorted inorder traversal
datatype BST = Empty  |  Node (left: BST, key: int, right: BST)

// This is the BST invariant
predicate isBST (t: BST)
{
   match t
      case Empty       => true
      case Node(l,x,r) => promising(l,x,r) && isBST(l) && isBST(r)
}				

// This is the BST property at the root level
predicate promising(l:BST, x:int, r:BST) 
{
   (forall z :: z in tset(l) ==> z < x) && 
   (forall z :: z in tset(r) ==> x < z)
}	

function tset(t:BST): set<int>
{
   match t
      case Empty       => {}		
      case Node(l,x,r) => tset(l)+{x}+tset(r)	
}				

function inorder(t: BST): seq<int>
{
   match t
      case Empty       => []
      case Node(l,x,r) => inorder(l) + [x] + inorder(r)
}			

// It searchs whether an element is present in a BST
function method search(x:int, t:BST): (res:bool)
requires isBST(t)
ensures res == (x in tset(t))
{
   match t 
      case Empty => false
      case Node(l, k, r) => x == k || search(x, l) || search(x, r)
}

// It inserts an element in a BST 
function method insert(x:int, t:BST): (res:BST)
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) + {x}
{
   match t
      case Empty => Node(Empty, x, Empty)
      case Node(l, k, r) =>
      if x < k then Node(insert(x, l), k, r)
      else if x == k then t
      else Node(l, k, insert(x, r))
}

// It deletes an element from a BST 
function method merge(t1: BST, t2:BST): (res:BST)
requires isBST(t1) && isBST(t2)
ensures isBST(res)
ensures tset(t1) + tset(t2) == tset(res)
{
   match (t1, t2)
      case (Empty, _) => t2
      case (_, Empty) => t1
      case (Node(l1, k1, r1), Node(l2, k2, r2)) =>
      if k1==k2 then Node(merge(l1, l2), k1, merge(r1, r2))
      else if k1 < k2 then Node(l1, k1, merge(r1, t2))
      else Node(merge(l1, Node(l2, k2, Empty)), k1, merge(r1, r2))
}

// function method delete(x:int, t:BST): (res:BST)
// requires isBST(t)
// ensures  isBST(res)
// ensures  tset(res) == tset(t) - {x}
// {
//    match t
//       case Empty => Empty
//       case Node(l, k, r) =>
//       if x < k then Node(delete(x, l), k, r)
//       else if x > k then Node(l, k, delete(x, r))
//       else

// }

// It deletes the minimum element of a non empty BST
function method deleteMin (t: BST): (res: (int, BST))
requires isBST(t) && t != Empty
ensures res.0 in tset(t) 
ensures forall x | x in tset(t)-{res.0} :: res.0 < x
ensures isBST(res.1) 
ensures tset(res.1) == tset(t) - {res.0}


predicate sorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

lemma sortedInorder(t: BST)
requires isBST(t)
ensures  sorted(inorder(t))
//{
//   match t 
//      case Empty       =>
//      case Node(l,x,r) => 
//            assert promising(l,x,r);
//            inorderPreserveSet(l);
//            assert forall z | z in inorder(l) :: z in tset(l);
//            assert forall z | z in inorder(l) :: z < x;
            //inorderPreserveSet(r);
            //assert forall z | z in inorder(r) :: z > x;
            //assert inorder(t)[|inorder(l)|]==x;
            //assert forall j | 0<= j < |inorder(l)| :: inorder(t)[j] in tset(l);
            //assert forall j | |inorder(l)| < j < |inorder(t)| :: inorder(t)[j] in tset(r);
//}

//lemma inorderPreserveSet (t:BST)
//ensures forall z | z in inorder(t) :: z in tset(t)

/*
     Exercises
*/


// 1. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root and prove the postcondition shown

function mirror(t:BST):(res:BST)
ensures tset(res)==tset(t)

// 2. We give you this function returning the reverse of a sequence

function rev <T> (s:seq<T>): (res:seq<T>)
{
   if s==[] then []
            else rev(s[1..]) + [s[0]]
}

// then, prove the following lemma by using the 'calc' facility

lemma reverseInorder (t:BST)
ensures inorder(mirror(t)) == rev(inorder(t))

