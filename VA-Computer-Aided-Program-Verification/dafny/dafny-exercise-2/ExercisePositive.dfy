predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
   var i: nat := 0;
   var n: nat := v.Length;
   while i < n
    decreases n - i;
    invariant i<=n;
    invariant positive(v[0..i]);
    {
        if v[i]<0 {return false;}
        i := i +1;
    }
   return true;
} 


// para secuencias
lemma positiveL(s:seq<int>, i:int)
requires 0<=i<=|s|
ensures !positive(s[..i]) ==> !positive(s[..|s|])

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
   var i: nat := 0;
   b:=true;
   var n: nat := v.Length;
   while (i < n && b)
    decreases n - i;
    invariant i<=n;
    invariant b==positive(v[0..i]);
    {
        b:=v[i]>=0;
        i := i +1;
    }
   positiveL(v[..],i);
} 

method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
   var i: nat := 0;
   b:=true;
   var n: nat := v.Length;
   while (i < n && b)
    // decreases v.Length-1+(if b then 1 else 0);
    decreases v.Length-i,b // esto es una tupla, y dice que el primero decrece y en caso contrario de que no, decrece la segunda componente, que es un bool y que se considera como 0 o 1
    invariant i<=n;
    invariant b==>positive(v[0..i]);
    invariant !b ==> 0<=i<v.Length && v[i]<0;
    {
        if(v[i]<0){b:=false;}
        else {i:=i+1;}
    }
   positiveL(v[..],i);
} 