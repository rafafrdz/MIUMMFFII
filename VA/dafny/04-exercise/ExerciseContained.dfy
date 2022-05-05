


predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


// merge-sorts algorithm
method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires strictSorted(v[..]) && strictSorted(w[..])
requires 0 <= n <= v.Length && 0 <= m <= w.Length
ensures b <==> forall k: nat :: k < n ==> v[k] in w[0..m]

{
	var idx: nat := 0;
	b:=true;
	while (idx<n && b)
	decreases n-idx, b;
	invariant idx <= n;
	invariant b <==> forall k: nat :: k < idx ==> v[k] in w[0..m];
	{
		b := v[idx] in w[0..m];
		idx := idx + 1;
	}
}
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w


method main()
{
	var a:array<int>;
	a:=new[3];
	a[0]:=1; a[1]:=3; a[2]:=4;

	var b:array<int>;
	b:=new[6];
	b[0]:=1; b[1]:=2; b[2]:=3; b[3]:=4; b[4]:=8; b[5]:=9;

	assert a[0]==1;
	assert a[1]==3;
	assert a[2]==4;
	assert b[0]==1;
	assert b[1]==2;
	assert b[2]==3;
	assert b[3]==4;
	assert b[4]==8;

	var result := mcontained(a,b,3, 5);
	assert result;
}