

//a valid index of the array contains x
predicate appears(v:array<int>,x:int)
reads v;
{exists index:: 0 <= index < v.Length && x==v[index]}

//a valid index of the array contains 0
predicate existCero(v:array<int>)
reads v;
{appears(v,0)}

//all the valid indexes contain strictly positive integers
predicate allPositive(v:array<int>)
reads v;
{ forall index :: 0 <= index < v.Length ==> v[index]>0 }

//x appears exactly once in the array
predicate exactlyOne(v:array<int>,x:int)
reads v;
{forall j, k :: 0<= j <= k < v.Length && x==v[j]==v[k] ==> j == k}
// {exists i::0<=i<v.Length && v[i]==x && 
//     (forall j :: 0<=j<v.Length ... )}


//mathematical function to count the number of times that x appears in v in range [c,f)
function count(v:array<int>,x:int,c:int,f:int): (cont:int)
requires 0 <= c <= f <= v.Length
decreases f - c
reads v;
{if c == f then 0 else (if v[c]==x then 1 + count(v,x,c+1,f) else count(v,x,c+1,f))}
// 


//using count define exactlyOnce
predicate exactlyOne2(v:array<int>,x:int)
reads v;
{count(v,x,0,v.Length)==1}

//x is the maximum element of v
predicate isMax(v:array<int>,x:int)
reads v;
{ forall index :: 0<=index<v.Length ==> v[index]<=x }

//i is one position of the minimum of v
predicate posMin(v:array<int>,i:int)
requires 0 <= i < v.Length
reads v;
{ forall index :: 0<=index<v.Length ==> v[i]<=v[index] }

//each element in v is the double of its index
predicate allDouble(v:array<int>)
reads v;
{ forall index :: 0 <= index < v.Length ==> v[index] == 2 * index }

//v is the mirror of w
predicate mirror(v:array<int>,w:array<int>)
requires v.Length == w.Length
reads v,w;
{forall index :: 0 <= index < v.Length ==> v[index] == w[(w.Length - index - 1)]}

//Write a main program to experiment with these predicates

method main()
{

// Example 1
 var v:array<int>;
 v:=new[3];
 v[0]:=0; v[1]:=7; v[2]:=7;

 assert v[1]==7;
 assert v[2]==7;
 assert v[0]==0;
 assert appears(v, 7);
 assert !appears(v,2);
 assert existCero(v);
 assert exactlyOne(v, 0);

 assert !allPositive(v);
 v[0]:=-3;
 assert !allPositive(v);
 v[0]:=1;
 assert allPositive(v);

// Example 2
var w:array<int>;
  w := new[4];
  w[0] := 1;
  w[1] := 2;
  w[2] := 7;
  w[3] := 7;
  assert w[0] == 1 && w[1] == 2 && w[2] == 7 && w[3] == 7;
  assert exactlyOne(w, 1);
  assert !exactlyOne(w, 7);
//   assert exactlyOne2(w,1); // assertion violation (?)

  assert !isMax(w, 5);
  assert isMax(w, 7);

  assert posMin(w, 0);
  assert !posMin(w, 1);
  assert !posMin(w, 2);

// Example 3
  var h : array<int>;
  h := new[3];
  h[0] := 0;
  h[1] := 2;
  h[2] := 4;
  assert h[0] == 0 && h[1] == 2 && h[2] == 4;
  assert allDouble(h);
  assert !allDouble(w);

  var p : array<int>;
  p := new[3];
  p[0] := 4;
  p[1] := 2;
  p[2] := 0;
  assert p[0] == 4 && p[1] == 2 && p[2] == 0;
  assert mirror(h, p);
}