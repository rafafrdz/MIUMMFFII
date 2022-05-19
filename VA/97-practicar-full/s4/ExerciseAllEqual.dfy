predicate allEqual(s:seq < int>)
{forall i,j::0 <= i < |s| && 0 <= j < |s| ==> s[i]==s[j] }
//{forall i,j::0 < =i < =j < |s| ==> s[i]==s[j] }
//{forall i::0 < i < |s| ==> s[i-1]==s[i]} 
//{forall i::0 < =i < |s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
lemma equivalenceNoOrder(s:seq < int>)
ensures allEqual(s)  <==> forall i,j::0 <= i <= j < |s| ==> s[i]==s[j]
{}

//All equal to first
lemma equivalenceEqualtoFirst(s:seq < int>)
requires s!=[]
ensures allEqual(s)  <==> (forall i::0 <= i < |s| ==> s[0]==s[i])
{}



lemma {:induction |s|} equivalenceContiguous(s:seq < int>)
ensures (allEqual(s)  <==> forall i::0 <=i < |s|-1 ==> s[i]==s[i+1])
{
  if |s| > 1 {
    equivalenceContiguous(s[..|s| - 1]);

    assert (forall i : nat :: i < |s| - 2 ==> s[i] == s[i + 1]) && allEqual(s[..|s| - 1]) && (forall j : nat :: j < |s| - 1 ==> s[j] == s[|s| - 1])
       ==> (forall i : nat :: i < |s| - 2 ==> s[i] == s[i + 1]) && s[|s| - 2] == s[|s| - 1]
       ==> (forall i : nat :: i < |s| - 1 ==> s[i] == s[i + 1]);

    assert (forall i : nat, j : nat :: 0 <= i < |s| - 1 && 0 <= j < |s| - 1 ==> s[i] == s[j]) && (forall i : nat :: i < |s| - 2 ==> s[i] == s[i + 1])   && s[|s| - 2] == s[|s| - 1]
       ==> (forall i : nat, j : nat :: 0 <= i < |s| - 1 && 0 <= j < |s| - 1 ==> s[i] == s[j]) && (forall j : nat :: j < |s| - 1 ==> s[j] == s[|s| - 1])
       ==> (forall i : nat, j : nat :: 0 <= i < |s|     && 0 <= j < |s|     ==> s[i] == s[j]);
  }
}



method mallEqual1(v:array < int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    var i := 0;
    b := true;

    while (i  <  v.Length && b) 
    decreases v.Length - i, b;
    invariant i <= v.Length
    invariant forall k:nat :: k < i && b==true ==> v[k] == v[0];
    invariant !b ==> exists k: nat :: k < v.Length && v[k] != v[0];
	  { 
       b:=(v[i]==v[0]);
       i := i+1;
	  }
}

method mallEqual2(v:array < int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  var i:int; 
  b:=true;
  i:=0;
  
  while (i < v.Length && v[i]==v[0])
  invariant i <= v.Length
  decreases v.Length - i
	invariant i > 0 ==> allEqual(v[0..i])
  {
    i:=i+1;
	}
	
  b:=(i==v.Length);
}



method mallEqual3(v:array < int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  equivalenceContiguous(v[..]);
  var i:int;
  b:=true;
  if v.Length > 0
  {
    i:=0;
    while (i < v.Length-1 && v[i]==v[i+1])
    invariant i < v.Length
	  decreases v.Length - i;
    invariant i > 0 ==> v[i-1] == v[i];
    invariant i > 0 ==> allEqual(v[0..i]);
    {
     i:=i+1;
    }
    
    b:=(i==v.Length-1);
 }

 }


//  method mallEqual4(v:array < int>) returns (b:bool)
// ensures b==allEqual(v[0..v.Length])
// {
//  var i:int;
//  b:=true;
//  if (v.Length>0){
//     i:=0;
//     while (i < v.Length-1 && b)
//       invariant //
// 	  decreases //
//     {
// 	 b:=(v[i]==v[i+1]);
// 	 i:=i+1;
//     }
//   }
//  }


//  method mallEqual5(v:array < int>) returns (b:bool)
// ensures b==allEqual(v[0..v.Length])
// {
//      var i := 0;
//      b := true;
//     while (i  <  v.Length && b) 
// 	    invariant //
//     	decreases //
// 	  { 
//        if (v[i] != v[0]) { b := false; }
//        else { i := i+1;}
//   	}
    
// }



