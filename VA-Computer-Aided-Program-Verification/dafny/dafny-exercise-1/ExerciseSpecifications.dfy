
//Specify a method that computes the quotient q and the remain r
//of integer division between a and b
method divide(a:int,b:int)returns (q:int,r:int)
requires b > 0
ensures a == b*q+r
{return a/b, a%b;}


//Specify a method that returns a copy of the argument x
 method copy(x:int) returns (y:int)
 ensures y == x
 {return x;}
 

 //Specify a method that returns the maximum of three integers
 method max3(x:int, y:int,z:int) returns (m:int)
 ensures m >= x && m >= y && m >= z
 {
 if (x>=y && x>=z) {return x;}
 else if (y>=x && y>=z) {return y;}
 else {return z;}
}

//Specify a method that returns a position of the maximum of the array
 method posMax1(v:array<int>) returns (i:int)
 requires v.Length>0
 ensures 0<=i<v.Length
 ensures forall index :: 0<=index<v.Length ==> v[index] <= v[i]
 {
    var max : int := 0;
    var idx : int := 0;
    while(idx<v.Length)
    invariant 0<=max<v.Length;
    invariant forall index :: 0 <= index < idx && 0 <= index < v.Length ==> v[index] <= v[max];
    {        
        if v[idx]>v[max] {max:=idx;}
        idx:=idx+1;
    }
    return max;
 }
 
 //Specify a method that returns a position of the maximum of the array
 //in segment [c,f)
 method posMax(v:array<int>, c:int, f:int) returns (i:int)
 requires v.Length>0
 ensures 0 <= c <= i < f <= v.Length
 ensures forall index :: c <= index < f ==> v[index] <= v[i]
 {
    var max : int := c;
    var idx : int := c;
    while(idx<f)
    decreases f-idx;
    invariant c <= max <= idx ;
    invariant forall index :: 0<=c <= index <= max <= idx < f <= v.Length ==> v[index] <= v[max];
    {        
        if v[idx]>v[max] {max:=idx;}
        idx:=idx+1;
    }
    return max;
 }

//Specify a method that swaps the values in v in indexes i and j
 method swap(v:array<int>,i:int,j:int) 
 
//Specify a method that modifies v such that all the negative values are assign value 0
// and the positive values are unchanged
 method positivize(v:array<int>,n:int)
  


