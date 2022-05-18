
//Final Exam, June 10th, 2021
//We want to specify and verify a method that, given an array of distinct elements, 
//computes the number of elements that have a smaller element on their right. 
//Example: given the array elements [2,6,8,4,9,5,10], the method must return 3
//because elements 9, 8 and 6 have smaller elements on their right.

//Your tasks are:

//1.Define a predicate oneBiggerOnRight that given an array v and a valid index i
//on that array, determines if there exists an element on i's right that is smaller 
//than v[i]
predicate oneBiggerOnRight(v:array<int>,i:int)
reads v
requires 0 <= i < v.Length
{
	exists j :: i < j < v.Length && v[i] > v[j]
}

//2.Define a function countBiggerOnRight that given an array v and a valid index i
//on that array, returns the number of elements in segment [i..v.Length] that meet 
//the property oneBiggerOnRight previously defined
function countBiggerOnRight(v:array<int>,i:int):int
reads v
requires 0 <= i < v.Length
decreases v.Length - i
{
	if i == v.Length-1 then 0
	else 
		if oneBiggerOnRight(v,i) then 1 + countBiggerOnRight(v,i+1)
		else countBiggerOnRight(v,i+1)
}

//3.Using function countBiggerOnRight, specify a method
//that receives an array v of distinct elements and returns  
//the number of elements that have a smaller element on the right 
method count(v:array<int>) returns (c:int)
requires forall i,j :: 0 <= i < v.Length && 0 <= j < v.Length && i != j ==> v[i] != v[j]
requires v.Length > 0
ensures c == countBiggerOnRight(v,0)
{
	var i := v.Length-1;
	var min := v[v.Length-1];
	c := 0;

	while (i > 0)
		decreases i
		invariant 0 <= i < v.Length
		invariant c >= 0
		invariant forall j :: i <= j < v.Length ==> min <= v[j]
		invariant exists j :: i <= j < v.Length && v[j] == min
		invariant c == countBiggerOnRight(v,i)
	{
		if v[i-1] > min {
			c := c+1;
		}
		else { //v[i-1]<min
			min := v[i-1];
		}
		i := i-1;
	}
}

//4. Implement and verify an algorithm that solves this problem.
//A linear time algorithm will be better valued.  
