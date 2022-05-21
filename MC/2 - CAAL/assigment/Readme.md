# Behavioural Equivalences and Preorders

This activity can be understood as a classic questionnaire where you 
have to provide answers to questions. There are two important difference 
though:

1. Answers from other students are public, once you send your own
answer you can check and comment your peers' answers.
2. You can add questions.

Define a CAAL project to properly define and prove your statements. Look for 
interesting solutions and help yourself with the different features of 
CAAL.

## Simulation

Consider process A = a.(b.c.0 + b.d.0); and define processes  S, S1 and S2 such that

- A is simulation equivalent to S, but A is not bisimilar to S.
- A is simulated by S2  and   S2 is not simulation equivalent to A
- S1 is simulated by A and S1 is not simulation equivalente to A

Type your answer but don't forget also to upload your CAAL project.

**Sol1.**

```
A = a.(b.c.0 + b.d.0);

S = a.(b.c.0 + b.d.0) + a.0;

S1 = a.b.c.0 + a.b.d.0;

S2 = a.b.(c.0 + d.0);
```

**Sol2.**

```
Adding an already existing trace as a choice:

S = a.(b.c.0 + b.d.0) + a.b.c.0;

S2 does not discards possible actions until performing b:

S2 = a.b.(c.0 + d.0);

The first choice of S1 discards an entire branch:

S1 = a.b.c.0 + a.b.d.0;
```

**Sol3.**

```
A = a.(b.c.0 + b.d.0);
S = A + a.b.c.0;
S2 = A + a.c.0;
S1 = a.b.c.0;
```

## Bisimulation

Consider the process A = a.(b.c.0 + b.d.0);

Define processes B1 and B2 bisimilars to A.  A ~ B1 ~ B2

Type your answer but don't forget also to upload your CAAL project.

**Sol1.**

```
A = a.(b.c.0 + b.d.0);
B1 = a.(b.(c.0 + c.0) + b.d.0);
B2 = a.(b.c.0 + b.(d.0 + d.0));
*B1 = A + A;  * another bisimilar process
```

**Sol2.**

```
A = a.(b.c.0 + b.d.0);

B1 = a.(b.c.(0 + 0) + b.d.0);

B2 = a.(b.c.0 + b.d.(0 + 0));
```

**Sol3.**

```
Parallel but restricted action:

B1 = (A|f.0)\{f};

Choice between the same process:

B2 = A + A;
```

**Sol4.**

```
A = a.(b.c.0 + b.d.0);
B1 = a.(b.(c.0 + c.0) + b.(d.0 + d.0));
B2 = a.((b.c.0 + b.c.0) + (b.d.0 + b.d.0));

B3 = a.((b.c.0 + b.c.0) + b.(d.0 + d.0));
```

## Traces

Consider the process T = a.b.e.0 + a.(b.c.0 + b.d.0); and define processes T', T1 and T2 such that

- T and T' are trace equivalent but T is not simulated by T'
- traces of T1 are included in T but T1 and T are not trace equivalent
- traces of T are included in T2 but  T2 and  T are not trace equivalent

Type your answer but don't forget also to upload your CAAL project.

**Sol1.**

```
T = a.b.e.0 + a.(b.c.0 + b.d.0);

** T' is trace equivalence to T but T is not simulated by T'.
T' = tau.a.b.e.0 + a.(b.c.0 + b.d.0);

** T1 traces are included in T traces but T1 and T are not trace equivalent
T1 = a.b.e.0 + a.b.c.0;

** T traces are included in T2 traces but T1 and T2 are not trace equivalent
T2 = a.b.e.0 + a.(b.c.0 + b.d.0) + g.0 ;
```

**Sol2.**

```
T = a.b.e.0 + a.(b.c.0 + b.d.0);
T' = a.b.e.0 + a.b.c.0 + a.b.d.0;
T1 = 0;
T2 = a.b.(c.0 + d.0 + e.0 + f.0);
```

**Sol3.**

```
Now T' is unable to simulate T:

T' = a.b.e.0 + a.b.c.0 + a.b.d.0;

T1 can just perform one of the traces of T:

T1 = a.b.e.0;

Adding a new action at the end of one choice branch:

T2 = a.b.(e.f.0 + c.0 + d.0);
```

## Recursive HML

Define HML formulas that represents the following statements:

1. Formula **f** such that, **f** is satisfied by process **p** iff **p** is process **0.**
2. It is possible to arrive to **0**
3. Always immediately after and action **d** we find **0**
4. Exists the sequence of actions **c.d**
5. Always immediately after and action **b** there is a **c**
6. Any sequence of **b** actions leads to a **c**

NOTE: Consider, if necessary  that the alphabet of actions is **L={a,b,c,d}**

Upload a CAAL project with the formulas defined above and some examples of processes to test the formulas.

## TODO. Pedir a esta ente