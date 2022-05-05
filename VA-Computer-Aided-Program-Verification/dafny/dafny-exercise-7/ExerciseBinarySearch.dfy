predicate sorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
 {
  var c,f:=0,v.Length-1;
  while (c<=f)
     decreases f-c
     invariant 0<=c<=v.Length && -1<=f<=v.Length-1 && c<=f+1
     invariant (forall u::0<=u<c ==> v[u]<=elem) && 
               (forall w::f<w<v.Length ==> v[w]>elem)
  {var m:=(c+f)/2;
   if (v[m]<=elem) 
        {c:=m+1;}
   else {f:=m-1;}
   }
   p:=c-1;
 
 
 }


 method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
{
   var p : int := binarySearch(v, elem);
   b := 0 <= p && v[p] == elem;
}

//Recursive binary search

method {:tailrecursion  false} binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem // los invariants de los whiles son los requires de la recursion
 decreases f-c
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
 {
  if (c==f+1) 
     {p:=c-1;} //empty case: c-1 contains the last element less or equal than elem
  else 
  {
   var m:=(c+f)/2;
   
   if (v[m]<=elem) 
      {p:=binarySearchRec(v,elem,m+1,f);}
   else 
      {p:=binarySearchRec(v,elem,c,m-1);}
   
  }
 
 
 }
 
 


  method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && (forall w::p<=w<v.Length ==> v[w]>elem)
 {

  var s : nat := 0;
  var q : nat := v.Length;
  var r : nat;
  while q > s
    decreases q - s;
    invariant q <= v.Length;
    invariant s <= q;
    invariant forall i | 0 <= i < s        :: v[i] < elem;
    invariant forall i | q <= i < v.Length :: v[i] >= elem;
  {
    r := (s + q) / 2;
    if v[r] == elem {b, p := true, r; return; }
    else if v[r] < elem { s := r + 1;}
    else { q := r; }
  }

  b, p := q < v.Length && v[q] == elem, q;
}
 

 