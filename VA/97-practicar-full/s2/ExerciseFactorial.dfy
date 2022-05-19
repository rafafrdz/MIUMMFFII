include "ExerciseExp.dfy"

function factorial(n:int):int
    decreases n
	requires n >= 0
{
if n == 0 then 1 else n*factorial(n-1)
}

lemma  factorial_Lemma(n:int)
    decreases n
	requires n >= 7
	ensures exp(3,n) < factorial(n)

lemma fact_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures factorial(n) <= exp(n,n)