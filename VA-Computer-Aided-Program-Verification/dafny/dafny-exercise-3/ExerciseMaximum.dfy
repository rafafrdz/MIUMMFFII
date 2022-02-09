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


method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]