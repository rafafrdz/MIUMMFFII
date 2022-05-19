
//Algorithm 1: From left to right return the first
method mmaximumL2R(v:array<int>) returns (i:int) 
requires v.Length > 0
ensures 0 <= i < v.Length 
ensures forall k:: 0 <= k < v.Length ==> v[i] >= v[k]
{
    i := 0;
    var n := v.Length;
    var idx := 0;
    while(idx < n)
    decreases n - idx;
    invariant idx <= n
    invariant i < n
    invariant forall k: nat :: k < idx ==> v[i] >= v[k]
    {
        if v[idx]>=v[i] {i := idx;}
        idx := idx + 1;
    }
}


// //Algorithm 2: From right to left return the last
method mmaximumR2L(v:array<int>) returns (i:int) 
requires v.Length > 0
ensures 0 <= i < v.Length 
ensures forall k:: 0 <= k < v.Length ==> v[i] >= v[k]
{
    var n := v.Length;
    i:= n - 1;
    var idx := n - 1;
    while(idx >= 0)
    decreases idx
    invariant -1 <= idx <= n
    invariant 0 <= i < n
    invariant forall k: nat :: idx < k < n ==> v[i] >= v[k]
    {
        if v[idx]>=v[i] {i := idx;}
        idx := idx - 1;
    }
}

// method mfirstMaximum(v:array<int>) returns (i:int)
// requires v.Length>0
// ensures 0<=i<v.Length 
// ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// ensures forall l:: 0<=l<i ==> v[i]>v[l]
// //Algorithm: from left to right

// method mlastMaximum(v:array<int>) returns (i:int)
// requires v.Length>0
// ensures 0<=i<v.Length 
// ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// ensures forall l:: i<l<v.Length ==> v[i]>v[l]

// //Algorithm : from left to right
// //Algorithm : from right to left

// method mmaxvalue(v:array<int>) returns (m:int)
// requires v.Length>0
// ensures m in v[..]
// ensures forall k::0<=k<v.Length ==> m>=v[k]