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
    var idxl:int := 0;
    var idxr:int := v.Length;
    while(idxl < idxr)
    decreases idxr - idxl
    invariant
    {
        if v[idxl] < 0 && v[idxr] < 0 {idxr := idxr - 1;}
        else if v[idxl] >= 0 && v[idxr] >= 0 {idxl := idxl + 1;}
        else if v[idxl] >= 0 && v[idxr] < 0 {idxl, idxr := idxl + 1, idxr - 1;}
        else {
            v[idxl], v[idxr] := v[idxr], v[idxl];
        }
    }
}