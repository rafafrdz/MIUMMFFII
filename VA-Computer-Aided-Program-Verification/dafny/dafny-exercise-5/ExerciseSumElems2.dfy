include "ExerciseSumElems.dfy"

function SumM(m : multiset<int>) : int
decreases m
{
	if m == multiset{} then 0 else var x :| x in m; x + SumM(m - multiset{x})
}
function SumS(s : seq<int>) : int
{
 SumM(multiset(s))
}


function SumVM(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
{SumM(multiset(v[c..f]))}



lemma {:induction m} SumOne(m : multiset<int>, x : int)
decreases m
	requires x in m
	ensures SumM(m) == x + SumM(m - multiset{x})
{	var y :| y in m && SumM(m) == y + SumM(m - multiset{y});

	if x == y
	{
		return;
	}
	else {
		calc == {
			SumM(m);
			y + SumM(m - multiset{y});
			{ SumOne(m - multiset{y}, x); }
			y + x + SumM(m - multiset{y} - multiset{x});
			{ assert m - multiset{y} - multiset{x} == m - multiset{x} - multiset{y}; }
			x + y + SumM(m - multiset{x} - multiset{y});
			{ SumOne(m - multiset{x}, y); }
			x + SumM(m- multiset{x});
		}
	}
	
  }


  lemma {:induction a, b} SumByParts(a : multiset<int>, b : multiset<int> )
  decreases  a, b
	ensures SumM(a + b) == SumM(a) + SumM(b)
{
	// Base case
	if a == multiset{}
	{
		assert a + b == b;
	}
	else
	{
		var x :| x in a;
		// Induction step
		SumByParts(a - multiset{x}, b);
		assert a - multiset{x} + b == a + b - multiset{x};
		assert SumM(a + b - multiset{x}) == SumM(a - multiset{x}) + SumM(b);
		SumOne(a, x);
		SumOne(a + b, x);
	}
}


lemma sequenceAxiom(s : seq<int>)
  ensures s == s[0..|s|];
  ensures forall i :nat :: i<=|s| ==> s[i..]==s[i..|s|];
  ensures forall j :nat :: j<=|s| ==> s[..j]==s[0..j];
{}

// last set into a multiset could see like a multiset with one set (last set)
lemma lastSetOfMultiSet(s : seq<int>)
  decreases s;
  requires 1 <= |s|;
  ensures multiset{s[|s|-1]} == multiset(s[|s|-1..|s|]) ;
{}
// let s: [s[..last]] + [s[last]] == [s] <==> [s] - [s[last]] == [s[..last]]]
lemma appendDropSetMultiSet(s : seq<int>)
decreases s
requires 1 <= |s|;
ensures multiset(s[..|s|-1]) + multiset{s[|s|-1]} == multiset(s) <==> multiset(s) - multiset{s[|s|-1]} == multiset(s[..|s|-1]);
{}



lemma {:induction s} sums(s:seq<int>)
decreases s
ensures SumS(s)==SumR(s)
ensures SumS(s)==SumL(s)
{
  if s != [] {
    equalSumR(s, 0, |s|);
    SumOne(multiset(s), s[|s|-1]);
    sequenceAxiom(s);
    lastSetOfMultiSet(s);
    SeqFacts<int>();
    appendDropSetMultiSet(s);
    sums(s[..|s|-1]);
  }
}


lemma  decomposeM(v:array<int>,c:int,f:int)
requires 0<=c<f<=v.Length
ensures SumVM(v,c,f)==SumVM(v,c,f-1)+v[f-1]
ensures SumVM(v,c,f)==v[c]+SumVM(v,c+1,f)
{
  if f == c + 1 { SumOne(multiset{v[c]}, v[c]); }
  else {
    sums(v[c..f]);
    SeqFacts<int>();
    sums(v[c..f - 1]);
    sums(v[c + 1..f]);
  }
}


lemma {:induction s,r} sumElemsS(s:seq<int>,r:seq<int>)
requires multiset(s)==multiset(r)
// ensures SumR(s)==SumR(r)
// ensures SumL(s)==SumL(r)
ensures SumS(s)==SumS(r)
{}



lemma SeqFacts<T>()
     ensures forall s : seq<T> | |s|>=1 ::|s[1..|s|]|==|s|-1;
     ensures forall s : seq<T>, i,j | 0<=i<=j<=|s| :: |s[i..j]| == j-i
     ensures forall s : seq<T>, i,j | 0<=i<j<=|s| :: s[i..j][..(j-i)-1] == s[i..j-1]
     ensures forall s : seq<T>,i,j,k | 0<=i<=k<=j<=|s| :: multiset(s[i..k])+multiset(s[k..j])==multiset(s[i..j])
   {
     forall s : seq<T>,i,j,k | 0<=i<=k<=j<=|s|
     ensures multiset(s[i..k])+multiset(s[k..j])==multiset(s[i..j])
     {  assert s[i..k]+s[k..j]==s[i..j];  }
    
    }


lemma ArrayFactsM<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
  ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
  ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
  ensures forall v:array<int>,i,j | 0<=i<j<=v.Length::SumVM(v,i,j)==SumVM(v,i,j-1)+v[j-1]
  ensures forall v:array<int>,i,j | 0<=i<j<=v.Length::SumVM(v,i,j)==v[i]+SumVM(v,i+1,j) 
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length ::SumS(v[i..j])==SumR(v[i..j])
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length ::SumS(v[i..j])==SumL(v[i..j])
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length ::SumV(v,i,j)==SumVM(v,i,j)==SumL(v[i..j])==SumR(v[i..j])==SumS(v[i..j])
  ensures forall v:array<int>,i,j,k | 0<=i<=k<=j<=v.Length ::SumVM(v,i,j)==SumVM(v,i,k)+SumVM(v,k,j)
{
  equalSumsV();
  SeqFacts<int>();

  forall v:array<int>,i,j | 0<=i<j<=v.Length
  ensures SumVM(v,i,j)==SumVM(v,i,j-1)+v[j-1]
  {decomposeM(v,i,j);}

  forall v:array<int>,i,j | 0<=i<j<=v.Length
  ensures SumVM(v,i,j)==v[i]+SumVM(v,i+1,j) 
  {decomposeM(v,i,j);}

  forall s:seq<int>
  ensures SumS(s)==SumR(s)
  ensures SumS(s)==SumL(s)
  {sums(s);}

  forall v : array<int>, i, j, k  | 0 <= i <= k <= j <= v.Length
  ensures SumVM(v, i, j) == SumVM(v, i, k) + SumVM(v, k, j);
  { SumByParts(multiset(v[i..k]), multiset(v[k..j]));  }
}

method sumElems3(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
//ensures sum==SumR(v[..])
ensures sum==SumVM(v,0,v.Length)

{
  ArrayFactsM<int>();
  sum:=0;
  var i:int;
  i:=0; var m:=v.Length/2;
  while (i<m)
   decreases m-i
   invariant 0<=i<=m && sum == SumVM(v,0,i)
 {
   sum:=sum+v[i];
   i:=i+1;
  }
   assert sum==SumVM(v,0,m);
   var aux:=0;
   assert i==m;
   while (i<v.Length)
    decreases v.Length - i
    invariant m <= i <= v.Length;
    invariant aux == SumR(v[m..i]);
  {
    aux:=aux+v[i];
    i:=i+1;
  }
  assert aux==SumVM(v,m,v.Length);
    sum:=sum+aux;
}