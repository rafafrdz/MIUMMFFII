The algorithm has been modeled by a Petri net with the following tools:

  - PIPE v4.3.0: lamport.xml
  - LoLA 2.0: lamport.lola

Notes:

  - pxln (or PxLn) means 'process x line n'.
  - I have omitted to give a place to the 'while True' and 'goto' statements
    as they are unconditional control structures and they are reflected
    in the model as the corresponding transitions and arcs.

LoLa verifications:
  
  i) Deadlock-free:
  
    It can be queried to LoLa with the command

      lola lamport.lola -f "REACHABLE DEADLOCK"

    and the result is: The net does not have deadlocks.

  ii) A process can be at multiple program locations at the same time:

    It can be quieried with 

      lola lamport.lola -f "REACHABLE (p1l2 + p1l3 + p1l4 + p1l5 > 1 OR p2l2 + p2l3 + p2l4 + p2l5 + p2l7 + p2l8 > 1)"

    and the result is: The predicate is unreachable.

    It is perhaps more interesting to check the following invariant which 
    means that each process is in exactly one program location at any time:

      lola lamport.lola -f "INVARIANT (p1l2 + p1l3 + p1l4 + p1l5 = 1 AND p2l2 + p2l3 + p2l4 + p2l5 + p2l7 + p2l8 = 1)"

    The result is: The predicate is invariant.

  iii) Both processes can reach their criticial sections simultaneously:

    It can be queried as 

      lola lamport.lola -f "REACHABLE (p1l4 = 1 AND p2l7 = 1)"

    and the result is: The predicate is unreachable.

