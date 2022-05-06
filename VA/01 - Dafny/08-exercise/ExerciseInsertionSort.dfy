
predicate sorted_seg(a:array<int>, i:int, j:int) 
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..]));
{
  var i := 0;
  while (i < a.Length)
     decreases a.Length-i
     invariant 0<=i<=a.Length
     invariant sorted_seg(a,0,i-1)
     invariant multiset(a[..]) == old(multiset(a[..]));
  {
     var temp := a[i];
     var j := i;
     var xs := a[..];         
     while (j > 0 && temp < a[j - 1])
         decreases j
         invariant 0<=j<=i<a.Length
         invariant sorted_seg(a,0,j-1) && sorted_seg(a,j+1,i)
         invariant forall k,l :: 0<=k<=j-1 && j+1<=l<=i ==> a[k]<=a[l]
         invariant forall k :: j<k<=i ==> temp <a[k]
         
         invariant xs[0..i] + xs[i + 1..a.Length] == a[0..j] + a[j + 1..a.Length];
         invariant i > j ==> a[j] == a[j+1];
         invariant xs[0..j] == a[0..j] && xs[i + 1..] == a[i + 1..] && xs[j..i] == a[j+1..i+1];
     {   
         a[j] := a[j - 1]; 
         j := j - 1;
   
     }

  assert xs == xs[0..j] + xs[j..i] + [xs[i]] + xs[(i+1)..] == a[0..j] +  a[(j+1) .. (i+1)] + [temp]  +  a[(i+1)..];
  a[j] := temp;
  assert xs[0..j] + [xs[i]] + xs[j..i] + xs[(i+1)..] == a[..];
  i := i + 1;

  }
}




