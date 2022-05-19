

//a valid index of the array contains x
predicate appears(v:array<int>,x:int)
reads v
{
    exists i: nat :: i < v.Length && v[i] == x
}
//a valid index of the array contains 0
predicate existCero(v:array<int>)
reads v
{
    appears(v, 0)
}

//all the valid indexes contain strictly positive integers
predicate allPositive(v:array<int>)
reads v
{
    forall i: nat :: i < v.Length ==> v[i] > 0
}

//x appears exactly once in the array
predicate exactlyOne(v:array<int>,x:int)
reads v
{
    forall i :nat, j:nat :: i < v.Length && j < v.Length ==> (v[i] == x || v[j]==x) <==> i == j
}

//mathematical function to count the number of times that x appears in v in range [c,f)
function count(v:array<int>,x:int,c:int,f:int): (cont:int)
reads v
requires 0 <= c <= f <= v.Length
decreases f - c
{
    if c == f then 0
    else if v[c]==x then 1 + count(v, x, c + 1, f)
    else count(v, x, c + 1, f)
}

//using count define exactlyOnce
predicate exactlyOne2(v:array<int>,x:int)
reads v
{
    count(v, x, 0, v.Length) == 1
}

//x is the maximum element of v
predicate isMax(v:array<int>,x:int)
reads v
{
    forall i:nat :: i < v.Length ==> v[i] <= x
}

//i is one position of the minimum of v
predicate posMin(v:array<int>,i:int)
requires 0 <= i < v.Length
reads v
{
    forall j:nat :: j < v.Length ==> v[i] <= v[j]
}

//each element in v is the double of its index
predicate allDouble(v:array<int>)

//v is the mirror of w
predicate mirror(v:array<int>,w:array<int>)

//Write a main program to experiment with these predicates


method main()
{
  var a:array<int>;
  a := new[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 0;
  assert a[0] == 1 && a[1] == 2 && a[2] == 3 && a[3] == 0;
//   assert appears(a,2);
//   assert appears(a,3);
//   assert appears(a,1);
//   assert !appears(a,5);

//   assert existCero(a);

  var b:array<int>;
  b := new[3];
  b[0] := 1;
  b[1] := 2;
  b[2] := 3;
  assert b[0] == 1 && b[1] == 2 && b[2] == 3;
//   assert allPositive(b);

  assert a.Length == 4 && a[0] == 1 && a[1] != 1 && a[2] != 1 && a[3] != 1;
//   assert exactlyOne(a,1); // this hangs

//   assert count(a,1,0,1) == 1;
//   assert count(a,1,0,2) == 1;
  // assert count(a,1,0,3) == 1; // this fails, but it shouldn't

//   assert exactlyOne2(a,0); // this fails and it shouldn't

//   assert isMax(a,3);
//   assert !isMax(a,12);

//   assert !posMin(a,1);
//   assert posMin(a,3);

//   var c:array<int>;
//   c := new[3];
//   c[0] := 0;
//   c[1] := 2;
//   c[2] := 4;
//   assert c[0] == 0 && c[1] == 2 && c[2] == 4;
//   assert allDouble(c);
//   assert !allDouble(a);

//   var d:array<int>;
//   d := new[3];
//   d[0] := 4;
//   d[1] := 2;
//   d[2] := 0;
//   assert d[0] == 4 && d[1] == 2 && d[2] == 0;

//   assert mirror(c,d);
}