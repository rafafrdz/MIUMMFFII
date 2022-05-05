
//Specify a method that computes the quotient q and the remain r
//of integer division between a and b
method divide(a:int,b:int)returns (q:int,r:int)
requires b != 0
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
 requires 0 <= c < v.Length && c < f <= v.Length;
 ensures c <= i < f;
 ensures forall index :: c <= index < f ==> v[index] <= v[i];
 {
    var max := c;
    var idx := c;
    while(idx<f)
        decreases f-idx;
        invariant c <= max <= idx && max < f;
        invariant forall index :: c <= index < idx && index < f ==> v[index] <= v[max];
    {        
        if v[idx]>v[max] {max:=idx;}
        idx:=idx+1;
    }
    return max;
 }

//Specify a method that swaps the values in v in indexes i and j
 method swap(v:array<int>,i:int,j:int)
 requires 0 <= i < v.Length && 0 <= j < v.Length;
 modifies v;
 {
     var c: int := v[i];
     v[i]:=v[j];
     v[j]:=c;
 }
 
//Specify a method that modifies v such that all the negative values are assign value 0
// and the positive values are unchanged
 method positivize(v:array<int>,n:int)
 modifies v;
{
    var idx := 0;
    while (idx < v.Length)
    decreases v.Length - idx;
    {
        if(v[idx]<0){v[idx]:=0;}
        idx := idx +1;
    }
}


