function SumR(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}

function SumL(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}


lemma concatLast(s:seq<int>,t:seq<int>)
requires t!=[]
ensures (s+t)[..|s+t|-1] == s+(t[..|t|-1])
{}
lemma concatFirst(s:seq<int>,t:seq<int>)
requires s!=[]
ensures (s+t)[1..] == s[1..]+t
{}

lemma {:induction s,t} SumByPartsR(s:seq<int>,t:seq<int>)
decreases s,t
ensures SumR(s+t) == SumR(s)+SumR(t)
{ if (t==[])
     {assert s+t == s;}
  else if (s==[])
     {assert s+t==t;}   
   else
     { 
       calc =={
        SumR(s+t);
        SumR((s+t)[..|s+t|-1])+(s+t)[|s+t|-1];
        SumR((s+t)[..|s+t|-1])+t[|t|-1];
        {concatLast(s,t);}
        SumR(s+t[..|t|-1])+t[|t|-1];
        {SumByPartsR(s,t[..|t|-1]);}
        SumR(s)+SumR(t[..|t|-1])+t[|t|-1];
        SumR(s)+SumR(t);

       }
     }


}

lemma concatEmpty(s : seq<int>)
  ensures [] + s == s && s + [] == s;
{}

lemma lastElementSeq(s : seq<int>, i : int, j : int)
  requires 0 <= i < j <= |s|;
  ensures s[i..j] == s[i..j-1] + s[j-1..j];
{}

lemma {:induction s,t} SumByPartsL(s:seq<int>,t:seq<int>)
decreases s,t
ensures SumL(s+t) == SumL(s)+SumL(t)
{
  if s == [] {
    concatEmpty(t);
  } else if t == [] {
    concatEmpty(s);
  } else {
    SumByPartsL(s[1..], t);
    calc == {
      SumL(s) + SumL(t);
      s[0] + SumL(s[1..]) + SumL(t);
      (s + t)[0] + SumL(s[1..] + t);
      { concatFirst(s,t); }
      (s + t)[0] + SumL((s + t)[1..]);
      SumL(s + t);
    }
  }
}




lemma  {:induction s,i,j} equalSumR(s:seq<int>,i:int,j:int)
decreases j-i
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
{
  if j > i + 1 {
    calc == {
      SumR(s[i..j]);
      { lastElementSeq(s, i, j); }
      SumR(s[i..j-1] + s[j-1..j]);
      { SumByPartsR(s[i..j-1], s[j-1..j]); }
      SumR(s[i..j-1]) + SumR(s[j-1..j]);
      { equalSumR(s, i, j-1); }
      SumL(s[i..j-1]) + SumR(s[j-1..j]);
      { equalSumR(s, j-1, j); }
      SumL(s[i..j-1]) + SumL(s[j-1..j]);
      { SumByPartsL(s[i..j-1], s[j-1..j]); }
      SumL(s[i..j-1] + s[j-1..j]);
      { lastElementSeq(s, i, j); }
      SumL(s[i..j]);
    }
  }
}


lemma equalSumsV()
ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
  { forall v:array<int>,i,j | 0<=i<=j<=v.Length
    ensures SumR(v[i..j])==SumL(v[i..j])
    {equalSumR(v[..],i,j);}
  }


function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {SumR(v[c..f])}


lemma ArrayFacts<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
  ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
  ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
 {equalSumsV();}
  

   method sumElems(v:array<int>) returns (sum:int)
  //ensures sum==SumL(v[0..v.Length])
  //ensures sum==SumR(v[..])
  ensures sum==SumV(v,0,v.Length)
  {
    ArrayFacts<int>();
    sum := 0;
    var idx : int;
    idx := 0;
    while idx < v.Length
    decreases v.Length - idx;
    invariant 0 <= idx <= v.Length;
    invariant sum == SumV(v,0,idx);
    {
      sum := sum + v[idx];
      idx := idx + 1;
    }
  }


method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
{
  ArrayFacts<int>();
  sum := 0;
  var idx : int;
  idx := v.Length;
  while idx > 0
    decreases idx;
    invariant 0 <= idx <= v.Length;
    invariant sum == SumR(v[idx..v.Length]);
  {
    sum := sum + v[idx - 1];
    idx := idx - 1;
  }
}






