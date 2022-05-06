


method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{
  var i : nat := 0;
  while i < v.Length
    decreases v.Length - i;
    invariant i <= v.Length;
    invariant forall j : nat | (j < i && old(v[j]) != x) || (i <= j < v.Length) :: v[j] == old(v[j]);
    invariant forall j : nat | j < i && old(v[j]) == x :: v[j] == y;
  {
    if v[i] == x { v[i] := y; }
    i := i + 1;
  }
}