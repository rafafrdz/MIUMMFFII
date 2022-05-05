//Author: Clara Segura
include "List.dfy"


method replace(l:List,x:int,y:int)
modifies l,l.Repr()
requires l.Valid()
requires forall x | x in l.Repr() :: allocated(x)

ensures l.Valid() 

//ensures: write the properties concerning the model
//replace each occurrence of x by y, and leave the rest unchanged 

ensures l.Iterators() >= old(l.Iterators())

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)



