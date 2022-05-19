


predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires strictSorted(v[..]) && strictSorted(w[..])
requires 0 <= n < v.Length && 0 <= m < w.Length
ensures b <==> forall k:nat :: k < n ==> v[k] in w[0..m] 
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
{
	var idx:= 0;
	var vn := v[0..n];
	var wm := w[0..m];
	b := true;
	while(idx<|vn|)
	decreases |vn| - idx;
	{
		if !(v[idx] in wm) {b:=false;}
		idx := idx + 1;
	}
}