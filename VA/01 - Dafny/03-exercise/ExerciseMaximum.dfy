//Algorithm 1: From left to right return the first
method mmaximum(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    var j:=1; i:= 0;
    while (j<v.Length)
        decreases v.Length - j;
        invariant 0<=j<=v.Length;
        invariant 0<=i<j;
        invariant forall k:: 0<=k<j ==> v[i]>=v[k]
    {
        if(v[j]>v[i]) {i := j;}
        j:=j+1;
    }
}


//Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    var j:=1; i:= 0;
    while (j<v.Length)
        decreases v.Length - j;
        invariant 0<=j<=v.Length;
        invariant 0<=i<j;
        invariant forall k:: 0<=k<j ==> v[i]>=v[k]
    {
        if(v[j]>=v[i]) {i := j;}
        j:=j+1;
    }
}



//Algorithm: from left to right
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
{
    var j:=1; i:= 0;
    while (j<v.Length)
        decreases v.Length - j;
        invariant 0<=j<=v.Length;
        invariant 0<=i<j;
        invariant forall k:: 0<=k<j ==> v[i]>=v[k]
        invariant forall k:: 0<=k<i ==> v[i]>v[k]
    {
        if(v[j]>v[i]) {i := j;}
        j:=j+1;
    }
}


//Algorithm : from left to right
method mlastMaximumL2R(v : array<int>) returns (i : int)
  requires v.Length > 0;
  ensures  0 <= i < v.Length;
  ensures  forall k : nat :: k < v.Length     ==> v[i] >= v[k];
  ensures  forall j : nat :: i < j < v.Length ==> v[i] > v[j];
{
  var idx : int := 1;
  i := 0;
  while idx < v.Length
    decreases v.Length - idx;
    invariant idx <= v.Length;
    invariant i < idx;
    invariant forall j : int :: i < j < idx ==> v[j] < v[i];
    invariant forall j : int :: 0 <= j < i ==> v[j] <= v[i];
  {
    if v[idx] >= v[i] {i := idx;}
    idx := idx + 1;
  }
}

//Algorithm : from right to left
method mlastMaximumR2L(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall j:: i<j<v.Length ==> v[i]>v[j]
{
  var idx : int := v.Length - 2;
  i := v.Length - 1;
  while 0 <= idx
    decreases idx + 1;
    invariant idx < i < v.Length;
    invariant 0 <= i;
    invariant forall j : int :: 0 <= j && idx < j < v.Length ==> v[j] <= v[i];
    invariant forall j : int :: i < j < v.Length  ==> v[j] < v[i];
  {
    if v[idx] > v[i] {i := idx;}
    idx := idx - 1;
  }
}


method mmaxvalue(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
   var idx : int := 1;
   m := v[0] ;
   while idx < v.Length
   decreases v.Length - idx;
   invariant 1 <= idx <= v.Length;
   invariant m in v[..idx];
   invariant forall j : nat :: j < idx ==> v[j] <= m;
   {
       if v[idx] > m {m:=v[idx];}
       idx := idx + 1;
   }
}