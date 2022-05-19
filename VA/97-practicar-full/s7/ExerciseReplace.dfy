


method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{
    var idx:nat := 0;
    while idx < v.Length
    decreases v.Length - idx;
    invariant idx <= v.Length;
    invariant forall k:nat :: k < idx && old(v[k]) == x ==> v[k] == y;
    invariant forall k:nat :: k < idx && old(v[k]) != x ==> v[k] == old(v[k]) ;
    invariant forall k:nat :: idx <= k < v.Length ==> v[k] == old(v[k]);
    {
        if v[idx] == x {v[idx] := y;}
        idx := idx + 1;
    }
}