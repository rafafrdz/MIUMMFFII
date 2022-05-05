
 predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

// peekSum is the sum of the all peeks
 function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }

 
 method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 {
     var i:nat := 1;
     var elem:int := 0;
     sum := v[0];
     while(i < v.Length)
      decreases v.Length - i;
      invariant elem < i <= v.Length;
      invariant isPeek(v, elem);
      invariant forall k : nat | elem < k < i :: v[k] < v[elem];
      invariant sum == peekSum(v, i);
      {
          if (v[elem]<=v[i])
          {
              elem := i;         
              sum := sum + v[elem];
          }

          i := i + 1;
      }
 }
 //Implement and verify an O(v.Length) algorithm to solve this problem