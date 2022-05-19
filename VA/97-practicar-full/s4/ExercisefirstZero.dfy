
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <= i <=v.Length
ensures forall j:: 0 <= j < i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0  
{
 i:=0;
 while (i < v.Length && v[i]!=0)
 invariant i <= v.Length
   decreases v.Length - i
   invariant forall k:nat :: k < i ==> v[k] != 0
  {i:=i+1;}
}