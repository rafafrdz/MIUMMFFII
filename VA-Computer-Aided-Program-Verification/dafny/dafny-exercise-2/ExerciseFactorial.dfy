include "ExerciseExp.dfy"

function factorial(n:int):(r:int)
    decreases n
	requires n >= 0
	ensures r >= 1
{ if n == 0 then 1 else n*factorial(n-1) }

lemma {:induction n} factorial_Lemma(n:int)
    decreases n;
	requires n >= 7
	ensures exp(3,n) < factorial(n)
	{ if n>7 { factorial_Lemma(n-1);} }


lemma {:induction n} fact_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures factorial(n) <= exp(n,n)
	{ 
		if (n > 1) {
			fact_Lemma(n-1);
			expBase_Lemma(n-1, n, n-1); // necesario este lemma
			assert factorial(n) == factorial(n-1) * n  <= exp(n-1,n-1) * n <= exp(n,n-1) * n == exp(n,n);
		}
	}