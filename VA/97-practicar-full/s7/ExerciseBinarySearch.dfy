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
   var idx: nat := 0;
   b:=false;
   while(idx < v.Length && !b)
   decreases v.Length - idx
   invariant idx <= v.Length
   invariant b <==> elem in v[0..idx]
   {
      b:= v[idx]==elem;
      idx := idx + 1;
   }
}
 //Implement by calling binary search function




//Recursive binary search

method {:tailrecursion  false} binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
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

 //Implement and verify
 

 