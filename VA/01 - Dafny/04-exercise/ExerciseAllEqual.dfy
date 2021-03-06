predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
lemma equivalenceNoOrder(s:seq<int>)
ensures allEqual(s) <==> forall i,j::0<=i<=j<|s| ==> s[i]==s[j]
{}

//All equal to first
lemma equivalenceEqualtoFirst(s:seq<int>)
requires s!=[]
ensures allEqual(s) <==> (forall i::0<=i<|s| ==> s[0]==s[i])
{}



lemma equivalenceContiguous(s:seq<int>)
ensures (allEqual(s) <==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
//Prove this!!



method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
     var i := 0;
     b := true;
    while (i < v.Length && b) 
      decreases v.Length - i;
      invariant 0 <= i <= v.Length;
      invariant b ==> allEqual(v[..i])
      invariant !b ==> i>1 && v[i-2]!=v[i-1]
	  { 
       b:=(v[i]==v[0]);
       i := i+1;
    
	  }
}

method mallEqual2(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  var i:int; 
  b:=true;
  i:=0;
  while (i<v.Length && v[i]==v[0])
	 decreases v.Length - i;
   invariant 0 <= i <= v.Length;
   invariant b ==> allEqual(v[..i]);
	 {i:=i+1;}
	 b:=(i==v.Length);

}



method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  equivalenceContiguous(v[..]);
  var i:int;
  b:=true;
  if (v.Length >0){
    i:=0;
    while (i<v.Length-1 && v[i]==v[i+1])
      decreases v.Length - i;
      invariant 0 <= i <= v.Length;
      invariant i < v.Length - 1 ==> allEqual(v[..i]);
      invariant forall k:int :: 0<=k<=i ==> v[k]==v[k+1];
      { i:=i+1; }
      b:=(i==v.Length-1);
    }
 }


//  method mallEqual4(v:array<int>) returns (b:bool)
// ensures b==allEqual(v[0..v.Length])
// {
//  var i:int;
//  b:=true;
//  if (v.Length>0){
//     i:=0;
//     while (i<v.Length-1 && b)
//       invariant //
// 	  decreases //
//     {
// 	 b:=(v[i]==v[i+1]);
// 	 i:=i+1;
//     }
//   }
//  }


//  method mallEqual5(v:array<int>) returns (b:bool)
// ensures b==allEqual(v[0..v.Length])
// {
//      var i := 0;
//      b := true;
//     while (i < v.Length && b) 
// 	    invariant //
//     	decreases //
// 	  { 
//        if (v[i] != v[0]) { b := false; }
//        else { i := i+1;}
//   	}
    
// }



