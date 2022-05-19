
//Specify a method that computes the quotient q and the remain r
//of integer division between a and b
method divide(a:int,b:int)returns (q:int,r:int)
requires a >= 0 && b > 0;
ensures  q * b + r == a && 0 <= r < b;
{
    return a / b, a % b;
    
}


//Specify a method that returns a copy of the argument x
 method copy(x:int) returns (y:int)
 ensures x == y
 {
     y:=x;
     return;
 }
 

 //Specify a method that returns the maximum of three integers
 method max3(x:int, y:int,z:int) returns (m:int)
 ensures m >= x && m >= y && m>=z
 {
     if(z<=y && x <= y) {
         return y;
         }
     else if (z<=x && y <= x) {
         return x;
         }
     else {
         return z;
         }
 }

//Specify a method that returns a position of the maximum of the array
 method posMax1(v:array<int>) returns (i:int)
 requires v.Length > 0;
 ensures 0 <= i < v.Length
 ensures forall j:nat :: j < v.Length ==> v[j] <= v[i]
 {
     var idx := 1;
     var imax := 0;
     while(idx < v.Length)
        decreases v.Length - idx
        invariant 0 <= imax < v.Length
        invariant forall k: nat :: k < idx && k < v.Length ==> v[imax] >= v[k];
        {
            if v[idx] > v[imax] {imax := idx;}
            idx := idx + 1;
        }
     return imax;
 }
 
 //Specify a method that returns a position of the maximum of the array
 //in segment [c,f)

 method subArray(v:array<int>, c:int, f:int) returns (vs: array<int>)
 requires 0 <= c <= f < v.Length
 ensures vs.Length <= v.Length
 ensures vs.Length > 0
//  ensures v[c..f] == vs[..] todo.
 {
     var xs := v[c .. f];
     var ys: array<int>;
     ys := new [f-c+1];

     var k := 0;
     while(k < ys.Length)
     decreases ys.Length - k
     invariant c + k <= v.Length
     {
         ys[k] := v[c + k];
         k := k + 1;
     }
     return ys;
 }
 
 method posMax(v:array<int>, c:int, f:int) returns (i:int)
 requires 0 <= c <= f < v.Length
 {
     var xs := subArray(v, c, f);
     var result := posMax1(xs);
     return result;
}

//Specify a method that swaps the values in v in indexes i and j
 method swap(v:array<int>,i:int,j:int) 
 
//Specify a method that modifies v such that all the negative values are assign value 0
// and the positive values are unchanged
 method positivize(v:array<int>,n:int)
  


