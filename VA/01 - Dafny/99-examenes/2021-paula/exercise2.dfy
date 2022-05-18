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
    Cons(x,Nil)
}

function method union (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) + elems (l2)
{
    match l1
        case Nil => //assert noDup(l2);
                    l2
        case Cons(x,xs) =>
            match l2
                case Nil => //assert noDup(l1);
                            l1
                case Cons(y,ys) =>
                    if x==y then var res_aux := union(xs,ys);
                                 //assert noDup(res_aux);
                                 //assert noDup(Cons(x,res_aux));
                                 Cons(x,res_aux)
                    else if x < y then var res_aux := union(xs,Cons(y,ys));
                                       //assert noDup(res_aux);
                                       //assert sorted(l2);
                                       sortedLemma(l2,y,ys);
                                       //assert noDup(Cons(x,res_aux));
                                       Cons(x,res_aux)
                         else var res_aux := union(Cons(x,xs),ys);
                              //assert noDup(res_aux);
                              //assert sorted(l1);
                              sortedLemma(l1,x,xs);
                              //assert noDup(Cons(y,res_aux));
                              Cons(y,res_aux)
}

lemma sortedLemma(l:List<int>, x:int, xs:List<int>)
requires sorted(l) && l == Cons(x,xs)
ensures forall i :: i in elems(l) ==> x <= i
{
    match l
        case Nil =>
        case Cons(x,xs) =>
            match xs
                case Nil =>
                case Cons(y,ys) => assert x <= y;
                                   sortedLemma(Cons(y,ys),y,ys);
}

function method inters (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) * elems (l2)
{
    match l1
        case Nil => Nil
        case Cons(x,xs) =>
            match l2
                case Nil => Nil
                case Cons(y,ys) =>
                    if x==y then var res_aux := Cons(x,inters(xs,ys));
                                 sortedLemma(l1,x,xs);
                                 //assert forall i :: i in elems(l1) ==> x <= i;
                                 sortedLemma(l2,x,ys);
                                 assert forall i :: i in elems(l2) ==> x <= i;
                                 //assert sorted(res_aux);
                                 res_aux
                    else if x<y then var res_aux := inters(xs,Cons(y,ys));
                                     //assert sorted(res_aux);
                                     sortedLemma(l2,y,ys);
                                     assert x !in elems(l2);
                                     //assert elems(res_aux) == elems(l1) * elems (l2);
                                     res_aux
                         else var res_aux := inters(Cons(x,xs),ys);
                              //assert sorted(res_aux);
                              sortedLemma(l1,x,xs);
                              assert y !in elems(l1);
                              //assert elems(res_aux) == elems(l1) * elems (l2);
                              res_aux
}