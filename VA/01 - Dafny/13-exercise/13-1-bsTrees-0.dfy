/*

Binary Search Trees (BST)
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// BSTs are binary trees having unique keys and sorted inorder traversal
datatype BST = Empty  |  Node (left: BST, key: int, right: BST)

// This is the BST invariant
predicate isBST (t: BST)
decreases t;
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
decreases t;
{
   match t
      case Empty       => {}		
      case Node(l,x,r) => tset(l)+{x}+tset(r)	
}				

function inorder(t: BST): seq<int>
decreases t;
{
   match t
      case Empty       => []
      case Node(l,x,r) => inorder(l) + [x] + inorder(r)
}			

// It searchs whether an element is present in a BST
function method search(x:int, t:BST): (res:bool)
requires isBST(t)
decreases t
ensures res == (x in tset(t))
{
   match t
      case Empty => false
      case Node(l, y, r) => x == y || search(x, l) || search(x, r)
}

// It inserts an element in a BST 
function method insert(x:int, t:BST): (res:BST)
decreases t
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) + {x}
{
   match t
      case Empty => Node(Empty, x, Empty)
      case Node(l, y, r) => if x < y then Node(insert(x, l), y, r)
                           else if x == y then t
                           else Node(l, y, insert(x, r))
}

// It deletes an element from a BST 
function method delete(x:int, t:BST): (res:BST)
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) - {x}
{
   match t
      case Empty => t
      case Node(l, y, r) => if x < y then Node(delete(x,l), y, r)
                              else if x > y then Node(l, y, delete(x, r))
                              else 
                                 match r
                                    case Empty => l
                                    case Node(_,_,_) =>
                                       var (m, t') := deleteMin(r);
                                       Node(l, m, t')
}

// It deletes the minimum element of a non empty BST
function method deleteMin (t: BST): (res: (int, BST))
requires isBST(t) && t != Empty
decreases t
ensures res.0 in tset(t) 
ensures forall x | x in tset(t) - {res.0} :: res.0 < x
ensures isBST(res.1) 
ensures tset(res.1) == tset(t) - {res.0}
{
   match t
      case Node(Empty, x, r) => (x, r)
      case Node(l, x, r) => 
         var (min, l') := deleteMin(l);
         assert tset(t) - {min} == tset(Node(l', x, r));
         (min, Node(l', x, r))
}


predicate sorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

lemma {:induction t} sortedInorder(t: BST)
requires isBST(t)
ensures  sorted(inorder(t))
{
  match t 
     case Empty       =>
     case Node(l,x,r) => 
           assert promising(l,x,r);
           inorderPreserveSet(l);
           assert forall z | z in inorder(l) :: z in tset(l);
           assert forall z | z in inorder(l) :: z < x;
           inorderPreserveSet(r);
           assert forall z | z in inorder(r) :: z > x;
           assert inorder(t)[|inorder(l)|]==x;
           assert forall j | 0<= j < |inorder(l)| :: inorder(t)[j] in tset(l);
           assert forall j | |inorder(l)| < j < |inorder(t)| :: inorder(t)[j] in tset(r);
}

lemma inorderPreserveSet (t:BST)
ensures forall z | z in inorder(t) :: z in tset(t)
{}

/*
     Exercises
*/


// 1. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root and prove the postcondition shown

function mirror(t:BST):(res:BST)
ensures tset(res)==tset(t)
ensures   t.Node? ==> t.key == res.key && tset(t.left) == tset(res.right) && tset(t.right) == tset(res.left);
decreases t;
{
   match t
      case Empty         => Empty
      case Node(l, x, r) => Node(mirror(r), x, mirror(l))
}

// 2. We give you this function returning the reverse of a sequence

function rev <T> (s:seq<T>): (res:seq<T>)
   decreases s;
   ensures |res| == |s|;
{
   if s==[] then []
            else rev(s[1..]) + [s[0]]
}

// then, prove the following lemma by using the 'calc' facility

lemma reverseInorder(t : BST)
   ensures inorder(mirror(t)) == rev(inorder(t));
   decreases t;
{
   match t
      case Empty         =>
      case Node(l, x, r) =>
         calc == {
            inorder(mirror(Node(l, x, r)));
            inorder(Node(mirror(r), x, mirror(l)));
            inorder(mirror(r)) + [x] + inorder(mirror(l));
            { reverseInorder(r); reverseInorder(l); }
            rev(inorder(r)) + [x] + rev(inorder(l));
            { reverseListAux(inorder(r), x, inorder(l)); }
            rev(inorder(l) + [x] + inorder(r));
            rev(inorder(t));
         }
}

lemma reverseListAux(l : seq<int>, x : int, r : seq<int>)
   ensures rev(l) + [x] + rev(r) == rev(r + [x] + l);

