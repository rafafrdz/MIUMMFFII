function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method fibonacci1(n:nat) returns (f:nat)
// como f es natural, no hace falta añadir la condicion >0
ensures f==fib(n)
{
   var i := 0;
   f := 0;
   var fsig := 1;
   while i < n
      decreases n-i; // esto es poque n>0 e i=0 (porque lo que decrece debe ser >0)
      invariant 0 <= i <= n; // este invariante es <= n porque el último estado es == n
      // debemos definir invariantes para las variables previamente definidas que participan en el bucle
      invariant f == fib(i)
      invariant fsig == fib(i+1)
   {
      f, fsig := fsig, f + fsig;
      i := i + 1;
   }
}

method fibonacci2(n:nat) returns (f:nat)
ensures f==fib(n)
{
if (n==0) {f:=0;}
else{
   var i := 1;
   var fant := 0;
   f := 1;
   while i < n
      decreases n-i;
      invariant  i<=n;
      invariant fant == fib(i-1);
      invariant f == fib(i);
   {
      fant, f := f, fant + f;
      i := i + 1;
   }
}

}

method fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
{

{
   var i: int := 0;
   var a := 1;
       f := 0;
   while i < n
    decreases n-i;
    invariant i<=n;
    invariant f == fib(i)
   //  invariant i==0 ==> a == 1 // (1)
   //  invariant i>0 ==> a==fib(i-1) // (1)
   //  invariant if (i==0) then a==1 else a==fib(i-1) // (2)
    invariant fib(i+1) == a + f // (3)

   {
      a, f := f, a + f;
      i := i + 1;
   }
}
}
