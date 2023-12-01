/* Question 1 2022 */

/*
Execution 

when x == 4
| z | c | x |
|---|---|---|
| 0 | 4 | 4 |
| 1 | 3 | 4 |
| 0 | 2 | 4 |
| 1 | 1 | 4 |
| 0 | 0 | 4 |

when x == 5
| z | c | x |
|---|---|---|
| 0 | 5 | 5 |
| 1 | 4 | 5 |
| 0 | 3 | 5 |
| 1 | 2 | 5 |
| 0 | 1 | 5 |
| 1 | 0 | 5 |
*/

predicate isEven(i: nat)
{
    i % 2 == 0
}

predicate isOdd(i: nat)
{
    !isEven(i)
}

predicate postcondition(i: nat)
{
    forall c :: 0 <= c <= i && (isEven(i) || isOdd(i)) ==> (isEven(c) || isOdd(c))
}

// To prevent dafny from complaining I ensured x is a natural number. For (iv) the precondition would be x >= 0
method Par(x: nat) returns (z: nat)
//requires 0 <= x // For total correctness, x can be int
requires true
ensures x % 2 == z
{
    assert true;
    assert 0 % 2 == 0;
    z := 0;
    assert 0 % 2 == z;
    assert (x - x) % 2 == z;
    var c := x; 
    assert (x - c) % 2 == z;
    while c != 0 
    decreases c
    invariant (x - c) % 2 == z
    {
        assert (x - c) % 2 == z && (c != 0);
        assert (x - c) % 2 == z;
        assert ( (z == 0) ==> (x - c - 1) % 2 == 1 ) && ( !(z == 0) ==> (x - c - 1) % 2 == 0 );
        c := c - 1;
        assert ( (z == 0) ==> (x - c) % 2 == 1 ) && ( !(z == 0) ==> (x - c) % 2 == 0 );
        if z == 0 {
            assert (x - c) % 2 == 1;
            z := 1;
            assert (x - c) % 2 == z;
        } else {
            assert (x - c) % 2 == 0;
            z := 0;
            assert (x - c) % 2 == z;
        }
        assert (x - c) % 2 == z;
    }
    assert (x - c) % 2 == z && !(c != 0);
    assert (x - c) % 2 == z && c == 0;
    assert (x - 0) % 2 == z;
    assert x % 2 == z;
}

/* Question 1 2021 */

/*
Execution 

when s is sorted
| f    | ind | s         |
|------|-----|-----------|
| true | 0   | [1,2,3,4] |
| true | 1   | [1,2,3,4] |
| true | 2   | [1,2,3,4] |
| true | 3   | [1,2,3,4] |

when s is not sorted
| f     | ind | s         |
|-------|-----|-----------|
| true  | 0   | [4,3,2,1] |
| false | 1   | [4,3,2,1] |
| false | 2   | [4,3,2,1] |
| false | 3   | [4,3,2,1] |
*/

predicate issortedPred(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

/* A <==> B is equivalent to A ==> B && !A ==> !B, therefore I will prove them separately */
method issorted(s: seq<int>) returns (f: bool)
requires 0 < |s|
ensures f <==> issortedPred(s)
{
    f := true;
    var ind := 0;
    while ind < |s| - 1 
    decreases |s| - ind
    invariant 0 <= ind <= |s| - 1
    invariant f ==> issortedPred(s[..ind+1])
    invariant !f ==> !issortedPred(s[..ind+1])
    {
        if s[ind] > s[ind+1] {
            f := false;
        }
        ind := ind + 1;
    }
}

/* Proving postcondition when A ==> B */
method issortedFirst(s: seq<int>) returns (f: bool)
requires 0 < |s|
ensures f ==> issortedPred(s)
{
    assert 0 < |s|;
    assert 0 < |s| && true;
    assert 0 < |s| && (false ==> issortedPred(s[..0+1])); 
    f := true;
    assert 0 < |s| && (f ==> issortedPred(s[..0+1])); 
    assert 0 <= 0 <= |s| - 1 && (f ==> issortedPred(s[..0+1])); 
    var ind := 0;
    assert 0 <= ind <= |s| - 1 && (f ==> issortedPred(s[..ind+1])); 
    while ind < |s| - 1 
    decreases |s| - ind
    invariant 0 <= ind <= |s| - 1 && (f ==> issortedPred(s[..ind+1]))
    {
        assert 0 <= ind <= |s| - 1 && (f ==> issortedPred(s[..ind+1])) && (ind < |s| - 1);
        assert ( (s[ind] > s[ind+1]) ==> 0 <= ind + 1 <= |s| - 1) && ( !(s[ind] > s[ind+1]) ==> 0 <= ind + 1 <= |s| - 1 && (f ==> issortedPred(s[..ind+1+1])));
        if s[ind] > s[ind+1] {
            assert 0 <= ind + 1 <= |s| - 1;
            assert 0 <= ind + 1 <= |s| - 1 && true;
            assert 0 <= ind + 1 <= |s| - 1 && (false ==> issortedPred(s[..ind+1+1]));
            f := false;
            assert 0 <= ind + 1 <= |s| - 1 && (f ==> issortedPred(s[..ind+1+1]));
        }
        assert 0 <= ind + 1 <= |s| - 1 && (f ==> issortedPred(s[..ind+1+1]));
        ind := ind + 1;
        assert 0 <= ind <= |s| - 1 && (f ==> issortedPred(s[..ind+1]));
    }
    assert 0 <= ind <= |s| - 1 && (f ==> issortedPred(s[..ind+1])) && !(ind < |s| - 1);
    assert 0 <= ind <= |s| - 1 && (f ==> issortedPred(s[..ind+1])) && ind >= |s| - 1;
    assert 0 <= ind == |s| - 1 && (f ==> issortedPred(s[..ind+1]));
    assert 0 <= ind == |s| - 1 && (f ==> issortedPred(s[..|s|-1+1]));
    assert 0 <= ind == |s| - 1 && (f ==> issortedPred(s));
    assert f ==> issortedPred(s);
}

/* Proving postcondition when !A ==> !B */
method issortedSecond(s: seq<int>) returns (f: bool)
requires 0 < |s|
ensures !f ==> !issortedPred(s)
{
    assert 0 < |s|;
    assert 0 < |s| && true;
    assert 0 < |s| && (false ==> !issortedPred(s[..1]));
    f := true;
    assert 0 < |s| && (!f ==> !issortedPred(s[..1]));
    assert 0 <= 0 <= |s| - 1 && (!f ==> !issortedPred(s[..0+1]));
    var ind := 0;
    assert 0 <= ind <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1]));
    while ind < |s| - 1 
    decreases |s| - ind
    invariant 0 <= ind <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1]))
    {
        assert 0 <= ind <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1])) && (ind < |s| - 1);
        assert ( (s[ind] > s[ind+1]) ==> 0 <= ind + 1 <= |s| - 1 && (true ==> !issortedPred(s[..ind+1+1]))) && 
               ( !(s[ind] > s[ind+1]) ==> 0 <= ind + 1 <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1+1]))); 
        if s[ind] > s[ind+1] {
            assert 0 <= ind + 1 <= |s| - 1 && (true ==> !issortedPred(s[..ind+1+1])); 
            f := false;
            assert 0 <= ind + 1 <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1+1])); 
        }
        assert 0 <= ind + 1 <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1+1])); 
        ind := ind + 1;
        assert 0 <= ind <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1])); 
    }
    assert 0 <= ind <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1])) && !(ind < |s| - 1);
    assert 0 <= ind <= |s| - 1 && (!f ==> !issortedPred(s[..ind+1])) && ind >= |s| - 1;
    assert 0 <= ind == |s| - 1 && (!f ==> !issortedPred(s[..ind+1]));
    assert 0 <= ind == |s| - 1 && (!f ==> !issortedPred(s[..|s|-1+1]));
    assert 0 <= ind == |s| - 1 && (!f ==> !issortedPred(s));
    assert !f ==> !issortedPred(s);
}


/* Question 1 2020 */

/*
Execution 

when y == 3, x = 3
| z             | c | x |
|---------------|---|---|
| 1             | 3 | 3 |
| 1 * 3         | 2 | 3 |
| 1 * 3 * 3     | 1 | 3 |
| 1 * 3 * 3 * 3 | 0 | 3 |
| 27            | 0 | 3 | // rewritten

This programe computes the power of a number, 3^3 == 27
*/

function Pow(x: int, n: nat): int
decreases n
{
    if n == 0 then 1 else x * Pow(x, n - 1)
}

// requires 0 <= y is the same thing as saying y: nat
// Dafny does not have a built in ^ Pow function which means I created one, however I'm assuming it terminates by making y nat
// I could have created a different Pow function which does the multiplication with negative numbers however the exam allows us to use ^ so it's fine
method Pwr(x: int, y: int) returns (z: int)
requires 0 <= y
ensures z == Pow(x, y)
{
    assert 0 <= y;
    assert true && 0 <= y; 
    assert 1 == 1 && 0 <= y; 
    assert 1 == Pow(x, 0) && 0 <= y; 
    z := 1;
    assert z == Pow(x, 0) && 0 <= y;
    assert z == Pow(x, y - y) && 0 <= y;
    var c := y;
    assert z == Pow(x, y - c) && 0 <= y;
    while c != 0 
    decreases c
    invariant z == Pow(x, y - c) && 0 <= y
    {
        assert z == Pow(x, y - c) && 0 <= y && (c != 0);
        assert z * x == Pow(x, y - (c - 1)) && 0 <= y;
        z := z * x;
        assert z == Pow(x, y - (c - 1)) && 0 <= y;
        c := c - 1;
        assert z == Pow(x, y - c) && 0 <= y;
    }
    assert z == Pow(x, y - c) && 0 <= y && !(c != 0);
    assert z == Pow(x, y - c) && 0 <= y && c == 0;
    assert z == Pow(x, y); 
}


/* Question 1 2019 */

/*
Execution 

when n == 3
| x                               | i | n |
|---------------------------------|---|---|
| 1                               | 0 | 3 |
| 1 + 2^(1-1)                     | 1 | 3 |
| 1 + 2^(1-1) + 2^(2-1)           | 2 | 3 |
| 1 + 2^(1-1) + 2^(2-1) + 2^(3-1) | 3 | 3 |
*/

/* I will be using my pow function from the previous exam solution */
method Exp(n: int) returns (x: int)
requires 0 <= n // same thing as saying n: nat
ensures x == Pow(2,n)
{
    assert 0 <= n; 
    assert 0 <= n && true; 
    assert 0 <= n && 1 == Pow(2,0);
    x := 1;
    assert 0 <= n && x == Pow(2,0);
    assert 0 <= 0 <= n && x == Pow(2,0);
    var i := 0;
    assert 0 <= i <= n && x == Pow(2,i);
    while i < n 
    decreases n - i
    invariant 0 <= i <= n && x == Pow(2,i)
    {
        assert 0 <= i <= n && x == Pow(2,i);
        assert 0 <= i + 1 <= n && x + Pow(2, i) == Pow(2,i+1);
        assert 0 <= i + 1 <= n && x + Pow(2, i+1-1) == Pow(2,i+1);
        i := i + 1;
        assert 0 <= i <= n && x + Pow(2, i-1) == Pow(2,i);
        x := x + Pow(2,i-1);
        assert 0 <= i <= n && x == Pow(2,i);
    }
    assert 0 <= i <= n && x == Pow(2,i) && !(i < n);
    assert 0 <= i <= n && x == Pow(2,i) && i >= n;
    assert 0 <= i == n && x == Pow(2,i);
    assert 0 <= n && x == Pow(2,n);
    assert x == Pow(2,n);
}

/* Question 3 2019 */

/* 
Execution 

when x == 3
| a | y  | x |
|---|----|---|
| 3 | 0  | 3 |
| 2 | -1 | 3 |
| 1 | -2 | 3 |
| 0 | -3 | 3 |
*/

function negate(x: int): int
{
    -x
}

// x: nat only so dafny doesn't complain but it should be int for partial correctness
method NegPartial(x: nat) returns (y: int)
requires true
ensures negate(x) == y // -x == y
{
    assert true;
    assert negate(0) == 0;
    assert negate(x - x) == 0;
    var a := x;
    assert negate(x - a) == 0;
    y := 0;
    assert negate(x - a) == y;
    while a != 0
    invariant negate(x - a) == y
    {
        assert negate(x - a) == y && (a != 0);
        assert negate(x - (a - 1)) == y - 1;
        y := y - 1;
        assert negate(x - (a - 1)) == y;
        a := a - 1;
        assert negate(x - a) == y;
    }
    assert negate(x - a) == y && !(a != 0);
    assert negate(x - a) == y && a == 0;
    assert negate(x - 0) == y;
    assert negate(x) == y;
}

// This time we will prove total correctness, so I will be explicit about my precondition
method NegTotal(x: int) returns (y: int)
requires 0 <= x // same as x: nat
ensures true
{
    assert 0 <= x;
    var a := x;
    assert 0 <= a;
    y := 0;
    assert 0 <= a;
    while a != 0
    decreases a
    {
        ghost var E0 := a;
        assert 0 <= a; 
        assert 0 <= a - 1 && a - 1 < E0;
        y := y - 1;
        assert 0 <= a - 1 && a - 1 < E0;
        a := a - 1;
        assert 0 <= a && a < E0;
    }
    assert true && !(a != 0); 
    assert true;
}

/* Question 3 2018 (December) */

/* 
Execution

when x = 3
| a | y | x |
|---|---|---|
| 3 | 0 | 3 |
| 2 | 1 | 3 |
| 1 | 2 | 3 |
| 0 | 3 | 3 |
*/

method CopyPartial(x: int) returns (y: int)
requires 0 <= x
ensures x == y
{
    assert 0 <= x;
    assert true && 0 <= x;
    assert (x - x) == 0 && 0 <= x;
    var a := x;
    assert (x - a) == 0 && 0 <= a;
    y := 0;
    assert (x - a) == y && 0 <= a;
    while a != 0
    invariant (x - a) == y && 0 <= a
    {
        assert (x - a) == y && 0 <= a && (a != 0);
        assert (x - (a - 1)) == (y + 1) && 0 <= a; 
        y := y + 1;
        assert (x - (a - 1)) == y && 0 <= a; 
        a := a - 1;
        assert (x - a) == y && 0 <= a; 
    }
    assert (x - a) == y && 0 <= a && !(a != 0);
    assert (x - a) == y && 0 <= a && a == 0;
    assert (x - a) == y && a == 0;
    assert (x - 0) == y;
    assert x == y;
}

/* Proving (|0 <= x|) CopyTotal (|T|) and (|0 <= x|) CopyPartial (|x == y|) implies (|0 <= x|) CopyTotal (|x == y|)  */
method CopyTotal(x: int) returns (y: int)
requires 0 <= x
ensures true
{
    assert 0 <= x;
    var a := x;
    assert 0 <= a;
    y := 0;
    assert 0 <= a;
    while a != 0
    decreases a
    {
        ghost var E0 := a;
        assert 0 <= a - 1 && a - 1 < E0 && (a != 0);
        assert 0 <= a - 1 && a - 1 < E0;
        y := y + 1;
        assert 0 <= a - 1 && a - 1 < E0;
        a := a - 1;
        assert 0 <= a && a < E0;
    }
    assert true && !(a != 0);
    assert true && a == 0;
    assert true;
}

/* Question 3 2018 (January) */

/* 
Execution

when a = 17
| n | m  | k  | a  |
|---|----|----|----|
| 0 | 0  | 0  | 17 |
| 1 | 2  | 1  | 17 |
| 2 | 4  | 4  | 17 |
| 3 | 6  | 9  | 17 |
| 4 | 8  | 16 | 17 |
| 5 | 10 | 25 | 17 |

End of loop: sqrt(a) == round(n)
*/

function iMinusOneSquared(i: int): int
{
    // (n - 1)^2
    (i * i) - (2 * i) + 1
}

predicate isCloseSqrt(a:int, n:int)
requires 0 < a
{
    // (n - 1)^2 < a <= n^2
    iMinusOneSquared(n) < a <= (n * n) 
}

method SqrtPartial(a: int) returns (n: nat)
requires 0 < a 
ensures isCloseSqrt(a, n)
{
    assert 0 < a;
    assert true && 0 < a;
    assert ( false ==> isCloseSqrt(a, 0) ) && 0 < a;
    assert ( 0 >= a ==> isCloseSqrt(a, 0) ) && 0 < a;
    assert ( 0 == 0 ) && ( 0 + 0 + 1 == 1 * 1 ) && ( 0 >= a ==> isCloseSqrt(a, 0) );
    n := 0;
    assert ( 0 == (n * n) ) && ( 0 + 0 + 1 == (n+1) * (n+1) ) && ( 0 >= a ==> isCloseSqrt(a, n) );
    var m := 0;
    assert ( 0 == (n * n) ) && ( 0 + m + 1 == (n+1) * (n+1) ) && ( 0 >= a ==> isCloseSqrt(a, n) );
    var k := 0;
    assert ( k == (n * n) ) && ( k + m + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) );
    while k < a 
    invariant ( k == (n * n) ) && ( k + m + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) ) && 0 < a
    {
        assert ( k == (n * n) ) && ( k + m + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) ) && (k < a);
        assert ( (k + m + 1) == ((n+1) * (n+1)) ) && ( (k + (m+2) + 1) + m + 1 == ((n+1)+1) * ((n+1)+1) ) && ( (k + m + 1) >= a ==> isCloseSqrt(a, (n+1)) ) && 0 < a;
        n := n + 1;
        assert ( (k + m + 1) == (n * n) ) && ( (k + (m+2) + 1) + m + 1 == (n+1) * (n+1) ) && ( (k + m + 1) >= a ==> isCloseSqrt(a, n) ) && 0 < a;
        k := k + m + 1;
        assert ( k == (n * n) ) && ( k + (m+2) + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) ) && 0 < a; 
        m := m + 2;
        assert ( k == (n * n) ) && ( k + m + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) ) && 0 < a; 
    }
    assert ( k == (n * n) ) && ( k + m + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) ) && 0 < a && !(k < a);
    assert ( k == (n * n) ) && ( k + m + 1 == (n+1) * (n+1) ) && ( k >= a ==> isCloseSqrt(a, n) ) && 0 < a && k >= a;
    assert ( k >= a ==> isCloseSqrt(a, n) ) && 0 < a && k >= a; 
    assert ( k >= a ==> isCloseSqrt(a, n) ) && k >= a; 
    assert isCloseSqrt(a, n); // ==> e 513
}

// |-total (|0 < a|) C (|T|) && |-partial (| 0 < a |) C (|isCloseSqrt(a,n)|) ==> |-total (|0 < a|) C (|isCloseSqrt(a, n))
method SqrtTotal(a: int) returns (n: nat)
requires 0 < a 
ensures true
{
    assert 0 < a;
    n := 0;
    var m := 0;
    var k := 0;
    assert 0 < a;
    while k < a 
    decreases a - k // variant
    {
        ghost var E0 := a - k;
        assert 0 < a; // precondition
        assert 0 < a && k < a && 0 < E0;
        assert 0 < a && a - (k + m + 1) < E0;
        n := n + 1;
        assert 0 < a && a - (k + m + 1) < E0;
        k := k + m + 1;
        m := m + 2;
        assert 0 < a && a - k < E0;
    }
    assert true && !(k < a);
    assert true;
}


/* Question 3 2017 */

/*
Execution

when n == 3
| i | x | y | n |
|---|---|---|---|
| 0 | 0 | 1 | 3 |
| 1 | 1 | 1 | 3 |
| 2 | 2 | 3 | 3 |
| 3 | 5 | 8 | 3 |

x = 5, n = 3
5 = fib(2 * 3)
5 = fib(6) // fib = [0, 1, 1, 2, 3, 5]; 5 = fib[6]
x = fib(2n)
*/

function fib(n: int) : int
requires 0 <= n
{
    if n == 0 then 0    
    else if n == 1 then 1
    else fib(n-1) + fib(n - 2)
}

method fibPartial(n: int) returns (x: nat)
requires 0 <= n
ensures x == fib(2 * x)
{
    assert 0 <= n;
    var i := 0;
    assert i <= n;
    assert i <= n && 0 == 0;
    assert i <= n && 0 == fib(0);
    assert i <= n && 0 == fib(2 * 0);
    x := 0;
    var y := 0;
    assert i <= n && x == fib(2 * x);
    while i != n
    decreases n - i  // so dafny doesn't complain about failing to terminate, partial correctness does not require this
    invariant i <= n && x == fib(2 * x) // proving i <= n so that I don't need to for total correctness (is only used later)
    {
        assert i <= n && x == fib(2 * x) && (i != n);
        assert (i+1) <= n && (x + y) == fib(2 * (x + y));
        i := i + 1;
        assert i <= n && (x + y) == fib(2 * (x + y));
        x := x + y;
        y := x + y;
        assert i <= n && x == fib(2 * x);
    }
    assert i <= n && x == fib(2 * x) && !(i != n);
    assert i <= n && x == fib(2 * x) && i == n;
    assert x == fib(2 * x);
}

// I will be using the proof of i <= n for total correctness
// |-total (|0 <= n|) C (|T|) && |-partial (| 0 <= n |) C (|fib(2n)|) ==> |-total (|0 <= n|) C (|fib(2n))
method fibTotal(n: int) returns (x: nat)
requires 0 <= n
ensures true
{
    assert 0 <= n;
    var i := 0;
    x := 0;
    var y := 0;
    assert 0 <= n;
    while i != n
    decreases n - i 
    invariant i <= n 
    {
        ghost var E0 := n - i;
        assert 0 <= n && i != n && 0 <= E0;
        assert 0 <= n && (0 <= n - (i+1) < E0);
        i := i + 1;
        x := x + y;
        y := x + y;
        assert 0 <= n && (0 <= n - i < E0);
    }
    assert true && !(i != n);
    assert true; 
}

/* Question 3 2016 */

/*
Execution

s[i] will be looking at the variable before i is incremented like the code provided
when m is in sequence s
| ind | i | m | s[i] | s         | 
|-----|---|---|------|-----------|
| -1  | 0 | 3 | 4    | [4,2,3,4] | 
| -1  | 1 | 3 | 4    | [4,2,3,4] | 
| -1  | 2 | 3 | 2    | [4,2,3,4] | 
| 2   | 2 | 3 | 3    | [4,2,3,4] | 

when m is not in sequence s
| ind | i | m | s[i] | s         | 
|-----|---|---|------|-----------|
| -1  | 0 | 5 | 4    | [4,2,3,4] | 
| -1  | 1 | 5 | 4    | [4,2,3,4] | 
| -1  | 2 | 5 | 2    | [4,2,3,4] | 
| -1  | 3 | 5 | 3    | [4,2,3,4] | 
| -1  | 4 | 5 | 4    | [4,2,3,4] | 

ind at the end will either be -1 meaning we did not find m in the sequence s, or the index of m in the sequence s
*/

/* This question is incomplete */
method findIndexTotal(s: seq<int>, m: int) returns (ind: int)
requires 0 < |s|
ensures true
{
    assert 0 < |s|;
    ind := -1;
    var i := 0;
    assert 0 < |s|;
    while i < |s| && ind < 0
    decreases |s| - i - ind // unforunately it might decrease to below 0, so the proof is impossible
    {
        ghost var E0 := |s| - i - ind;
        if s[i] == m {
            ind := i;
        } else {
            i := i + 1;
        }
        //assert 0 < |s| && (|s| - (i + ind) < E0);
    }
    assert true && !(i < |s| && ind < 0);
    assert true;
}

predicate NotMember(s: seq<int>, m: int)
{
    forall i :: 0 <= i < |s| ==> m != s[i]
}

method findPartial(s: seq<int>, m: int) returns (ind: int)
requires 0 < |s|
ensures (ind < 0) ==> NotMember(s, m)
{
    assert 0 < |s|;
    assert true && 0 < |s|;
    assert (false ==> (0 <= 0 <= |s| && NotMember(s[..0], m))) && 0 < |s|;
    assert ((-1 < 0) ==> (0 <= 0 <= |s| && NotMember(s[..0], m))) && 0 < |s|;
    ind := -1;
    assert ((ind < 0) ==> (0 <= 0 <= |s| && NotMember(s[..0], m))) && 0 < |s|;
    var i := 0;
    assert ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s|;
    while i < |s| && ind < 0
    invariant ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s|
    {
        assert ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s| && (i < |s| && ind < 0);
        assert ( (s[i] == m) ==> ((i < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s| ) && 
              ( !(s[i] == m) ==> ((ind < 0) ==> (0 <= (i+1) <= |s| && NotMember(s[..(i+1)], m))) && 0 < |s|);
        if s[i] == m {
            assert ((i < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s|;
            ind := i;
            assert ((ind < 0) ==> (0 <= ind <= |s| && NotMember(s[..ind], m))) && 0 < |s|;
        } else {
            assert ((ind < 0) ==> (0 <= (i+1) <= |s| && NotMember(s[..(i+1)], m))) && 0 < |s|;
            i := i + 1;
            assert ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s|;
        }
        assert ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s|;
    }
    assert ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s| && !(i < |s| && ind < 0);
    assert ((ind < 0) ==> (0 <= i <= |s| && NotMember(s[..i], m))) && 0 < |s| && (i >= |s| || ind >= 0);
    assert (ind < 0) ==> NotMember(s, m);
}

/* Question 3 2015 */

/*
Execution

when x = 3 and y = 2
| a | z  | x | y |
|---|----|---|---|
| 3 | 2  | 3 | 2 |
| 2 | 1  | 3 | 2 |
| 1 | 0  | 3 | 2 |
| 0 | -1 | 3 | 2 |

when x = 2 and y = 3
| a | z | x | y |
|---|---|---|---|
| 2 | 3 | 2 | 3 |
| 1 | 2 | 2 | 3 |
| 0 | 1 | 2 | 3 |


z == (y - a) 

Sub method therefore is z = y - x on the condition that x is positive
*/

method SubPartial(x: int, y: int) returns (z: int)
requires x >= 0
ensures z == y - x
{
    assert x >= 0;
    assert true && x >= 0;
    assert y == y && x >= 0;
    assert y == y - 0 && x >= 0;
    assert y == y - (x - x) && x >= 0;
    var a := x;
    assert y == y - (x - a) && x >= 0;
    z := y;
    assert z == y - (x - a) && x >= 0;
    while a != 0
    invariant z == y - (x - a) && x >= 0
    {
        assert z == y - (x - a) && x >= 0 && (a != 0);
        assert (z - 1) == y - (x - (a - 1)) && x >= 0;
        z := z - 1;
        assert z == y - (x - (a - 1)) && x >= 0;
        a := a - 1;
        assert z == y - (x - a) && x >= 0;
    }
    assert z == y - (x - a) && x >= 0 && !(a != 0);
    assert z == y - (x - a) && x >= 0 && a == 0;
    assert z == y - (x - 0);
    assert z == y - x;
}

// |-total (|0 <= x|) C (|T|) && |-partial (| 0 <= x |) C (|z = y - x|) ==> |-total (|0 <= n|) C (|z = y - x|)
// E = x >= 0
// E0 = a
method SubTotal(x: int, y: int) returns (z: int)
requires x >= 0
ensures true
{
    assert x >= 0;
    var a := x;
    z := y;
    assert x >= 0;
    while a != 0
    decreases a
    {
        ghost var E0 := a;
        assert x >= 0 && a != 0 && (0 <= E0);
        assert x >= 0 && (0 <= (a-1) < E0);
        z := z - 1;
        assert x >= 0 && (0 <= (a-1) < E0);
        a := a - 1;
        assert x >= 0 && (0 <= a < E0);
    }
    assert true && !(a != 0);
    assert true;
}