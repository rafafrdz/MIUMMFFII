


//Method barrier below receives an array and an integer p
//and returns a boolean b which is true if and only if 
//all the positions to the left of p and including also position p contain elements 
//that are strictly smaller than all the elements contained in the positions to the right of p 
//Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false, 
// but for p=2 the method should return true
//1.Specify the method
//2.Implement an O(v.size()) method
//3.Verify the method
predicate barrierAx(v:array<int>,p:int)
requires 0 <= p < v.Length;
reads v;
{forall k,j | 0 <= k <= p < j < v.Length :: v[k] < v[j] }


method barrier(v : array<int>, p : int) returns (b : bool)
  requires 0 <= p < v.Length;
  ensures b <==> barrierAx(v,p);
{
  b := true;
  var len := v.Length;

  if p <= len - 2 {
    var idx := p + 2;
    var acc := v[p + 1];
    while idx < len
      decreases len - idx;
      invariant p <= idx <= len;
      invariant acc in v[p + 1 .. idx]
      invariant forall k | p < k < idx :: v[k] >= acc;
    {
      if v[idx] < acc { acc := v[idx]; }
      idx := idx + 1;
    }

    var idxg := 0;
    while idxg <= p && b
      decreases p - idxg, b;
      invariant 0 <= idxg <= p + 1;
      invariant !b ==> v[idxg] >= acc && idxg <= p;
      invariant b ==> forall k | 0 <= k < idxg :: v[k] < acc;
    {
      b := v[idxg] < acc;
      if b { idxg := idxg + 1; }
    }
  }
}
