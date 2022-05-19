function exp(x:int, e:int):(r:int)
    decreases e
	requires e >= 0
    ensures x > 0 ==> r > 0
    ensures x >= 1 ==> r >= 1
{
if e == 0 then 1 else x*exp(x,e-1)
}

lemma {:induction n} exp3_Lemma(n:int) 
    decreases n
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
    {}
    
 
lemma {:induction n} mult8_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
    {
        if n>1 {
            mult8_Lemma(n-1);
        }
    }
