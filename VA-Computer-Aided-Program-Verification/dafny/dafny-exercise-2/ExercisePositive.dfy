predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
   var i: nat := 0;
   var n: nat := v.Length;
   while i < n
    decreases n - i;
    invariant i<=n;
    invariant positive(v[0..i]);
    {
        if v[i]<0 {return false;}
        i := i +1;
    }
   return true;
}