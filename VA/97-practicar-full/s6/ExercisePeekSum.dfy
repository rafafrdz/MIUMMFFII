
 predicate isPeak(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

 function peakSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeak(v,i-1) then v[i-1]+peakSum(v,i-1)
  else peakSum(v,i-1)
 }

 
 method mPeakSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peakSum(v,v.Length)
 {
     if(v.Length == 1) {sum:=v[0];}
     else {
     sum := v[0];
     var idx: nat:= 1;
     var ixpeak: nat := 0 ;
     while idx < v.Length
     decreases v.Length - idx;
     invariant ixpeak < idx <= v.Length
     invariant forall j : nat | ixpeak < j < idx :: v[j] < v[ixpeak];
     invariant isPeak(v, ixpeak);
     invariant sum == peakSum(v, idx);
     {
      if v[idx]>=v[ixpeak] {
          ixpeak := idx;
          sum := sum + v[idx];
      }
      idx := idx + 1;
     }
    }

 }
 //Implement and verify an O(v.Length) algorithm to solve this problem