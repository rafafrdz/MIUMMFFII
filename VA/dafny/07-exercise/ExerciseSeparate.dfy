predicate strictNegative(v:array<int>,i:int,j:int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

predicate isPermutation(s:seq<int>, t:seq<int>)
{multiset(s)==multiset(t)}

method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
{
  var k : nat := 0;
  i := 0;
  while k < v.Length
    decreases v.Length - k;
    invariant 0 <= i <= k <= v.Length;
    invariant positive(v[0..i]);
    invariant strictNegative(v, i, k);
    invariant isPermutation(v[0..v.Length], old(v[0..v.Length]));
  {
    if v[k] >= 0 {
      if (k > i) {v[k], v[i] := v[i], v[k]; }
      i := i + 1;
    }
    k := k + 1;
  }
}