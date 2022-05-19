include "ExerciseCountEven.dfy"

method sameEven(v:array<int>) returns (b:bool)
requires positive(v[0..v.Length])
ensures b <==> CountEven(v[0..v.Length]) == (v.Length-CountEven(v[0..v.Length]))
{ ArrayFacts<int>();
  var n:int;
  n:=mcountEven(v);
  b:=(n==v.Length-n);
}


method sameEvenb(v:array<int>) returns (b:bool)
requires positive(v[0..v.Length])
ensures b <==> CountEven(v[0..v.Length]) == (v.Length-CountEven(v[0..v.Length]))
{
  var i:=0;
  var dif:int;
  dif := 0;
  while (i < v.Length)
    decreases v.Length - i
    invariant //write
  {  ArrayFacts<int>(); 

    if (v[i]%2==0) { dif := dif+1;}
    else {dif := dif-1;}
    i := i+1;
  }
  return (dif==0);
}



