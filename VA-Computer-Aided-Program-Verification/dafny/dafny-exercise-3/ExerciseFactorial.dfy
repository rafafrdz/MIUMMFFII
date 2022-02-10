
function exp(x:int, e:int):int
    decreases e
	requires e >= 0
{
if e == 0 then 1 else x*exp(x,e-1)
}

function factorial(n:int):(r:int)
    decreases n
	requires n >= 0
  ensures r >0
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
  invariant i>=0
  invariant factorial(n) == f * factorial(i)
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
   decreases n-i
   invariant i >= 0
   invariant f == factorial(i-1)
   invariant n + 1 >= i
  { 
   f,i:=i*f,i+1;
  }
}

method mfactorial3(n:int) returns (f:int)
requires n>=0
ensures f==factorial(n)
{
 f:=1;
 var i:=0;
 while (i<n)
  decreases n-i
  invariant  i >= 0
  invariant f == factorial(i)
  invariant n >= i

  {  
   f,i:=(i+1)*f,i+1;
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
      factorial(2 * n);
      (2 * n) * (2 * n -1) * factorial(2 * (n - 1));
      < {exp2n_Lemma(n-1);}
      (2 * n) * (2 * n - 1) * exp(2, 2 * (n - 1))*exp(factorial(n - 1), 2);
      < {assert 2*n * (2*n-1) < 2*n * (2*n) == 4 * n * n;}
        4 * n * n * exp(2, 2 * (n - 1)) * exp(factorial(n - 1), 2);
       {assert n * n * exp(factorial(n - 1), 2) == exp(factorial(n), 2);}
       4 * exp(2, 2 * (n - 1)) * exp(factorial(n), 2);
       { assert 4 * exp(2, 2 * (n - 1)) == exp(2, 2 * n); }
       exp(2, 2 * n)*exp(factorial(n), 2);
    }
  }
  }
