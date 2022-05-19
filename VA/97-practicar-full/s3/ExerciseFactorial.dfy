
function exp(x:int, e:int):int
    decreases e
	requires e >= 0
{
if e == 0 then 1 else x*exp(x,e-1)
}

function factorial(n:int):(f:int)
  decreases n
	requires n >= 0
  ensures f > 0
{
if n == 0 then 1 else n*factorial(n-1)
}




method mfactorial1(n:int) returns (f:int)
requires n>=0
ensures f==factorial(n)
{
 f:=1;
 var i:=n;
 while (i>0)
 decreases i
 invariant f * factorial(i) == factorial(n);
 {     
  f,i:=i*f,i-1;
 }


}

method mfactorial2(n:int) returns (f:int)
requires n>=0
ensures f==factorial(n)
{
 f:=1;
 var i:=1;
 while (i<=n)
   decreases n+1-i
   invariant i <= n + 1
   invariant i <= n ==> f == factorial(i-1);
   invariant i == n + 1 ==> f == factorial(n);

  { 
   f, i := i*f ,i+1;
  }
}

method mfactorial3(n:int) returns (f:int)
requires n>=0
ensures f==factorial(n)
{
 f:=1;
 var i:=0;
 while (i < n)
  decreases n - i
  invariant i <= n
  invariant i <= n ==> f == factorial(i);
  invariant i == n + 1 ==> f == factorial(n);
  {  
   f,i := (i+1)*f, i+1;
  }
}


//Use calculations to prove this lemma
lemma {:induction n} exp2n_Lemma(n:int)
  decreases n
	requires n >= 1
	ensures factorial(2*n) < exp(2,2*n)*exp(factorial(n),2)
  {
    if n > 1 {
      calc == {
        factorial(2*(n+1));
        {assert factorial(2 * (n+1)) == 2  * factorial(n);}
        2 * factorial(n + 1);
        2 * (n + 1) * factorial(n);
        (n + 1) * factorial(2*n);
        < { exp2n_Lemma(n);}
        (n + 1) * exp(2,2*n) * exp(factorial(n),2);
        < {assert (n + 1) * exp(2,2*n) * exp(factorial(n),2) < (n + 1) * (n + 1) * exp(2,2*n) * exp(factorial(n),2);}
        {assert exp(factorial(n),2) == factorial(n) * factorial(n);}
        {assert (n+1) * factorial(n) == factorial(n+1);}
        exp(2,2*n) * exp(factorial(n+1),2);
        
        // exp(2,2*(n+1))*exp(factorial(n+1),2);

      }
    }
  }
