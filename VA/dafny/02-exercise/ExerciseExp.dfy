function exp(x:int, e:int):(r:int)
    decreases e
	requires e >= 0
    ensures x>0 ==> r>0; // fundamental para el lemma expBase
    ensures x>=1 ==> r>=1; // idem
{ if e == 0 then 1 else x*exp(x,e-1) }

lemma   {:induction n} exp3_Lemma(n:int) 
    decreases n
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
    {
        if(n==1) {assert (exp(3,1)-1)%2==0;}
        else {
            exp3_Lemma(n-1);
            assert((exp(3,n)-1)%2==0); // Induction hypoteshis
            assert exp(3,n+1)-1 == 2*exp(3,n) + exp(3,n) - 1;
        }
    }
    

    

lemma  {:induction n} mult8_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
    {
        if(n==1) {assert (exp(3,2*n)-1)%2==0;}
        else{
            mult8_Lemma(n-1);
            assert((exp(3,2*n)-1)%8==0); // Induction hypoteshis
            assert exp(3,2*(n+1))-1 == 8*exp(3,2*n) + exp(3,2*n) - 1;
        }
    }

lemma  {:induction n} exp_1_Lemma(n:int, x:int)
    decreases n
    requires x >= 0
	requires n >= 1
	ensures exp(x,n)<=exp(x,n+1)
    {
        if(n>1){
            exp_1_Lemma(n-1, x);
        }
    }

// Este lemma mantiene la relacion de orden de la exponencial
// en función de la relacion de orden de la base
lemma expBase_Lemma(x:int, y:int, n:int)
    decreases n;
    requires n > 0;
    requires x >= 1
    requires y > x;
	ensures exp(x,n)<exp(y,n);
    {
        if(n>1){
            expBase_Lemma(x,y, n-1);
            assert exp(x,n) == x * exp(x,n-1) < y * exp(y,n-1) == exp(y,n);
        }
    }
