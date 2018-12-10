------------------------------- MODULE op_counter ------------------------------
EXTENDS Integers, TLC, Sequences
CONSTANTS 
  N
  P == 1..N

(*
--algorithm op_counter
variables
  msg = [m \in P |-> 0]; \*simulate broadcast

macro Broadcast(v) begin  \*simulate broadcast
  msg := [m \in P |-> v];
end macro; 

fair process Counter \in P
variables
  count = 0; \*local counter
begin Update:
  either Increment:
    count := count + 1;
    Broadcast(count);
  or Decrement:
    count := count - 1;
    Broadcast(count);
  end either;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES msg, pc, count

vars == << msg, pc, count >>

ProcSet == (P)

Init == (* Global variables *)
        /\ msg = [m \in P |-> 0]
        (* Process Counter *)
        /\ count = [self \in P |-> 0]
        /\ pc = [self \in ProcSet |-> "Update"]

Update(self) == /\ pc[self] = "Update"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "Increment"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "Decrement"]
                /\ UNCHANGED << msg, count >>

Increment(self) == /\ pc[self] = "Increment"
                   /\ count' = [count EXCEPT ![self] = count[self] + 1]
                   /\ msg' = [m \in P |-> count'[self]]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]

Decrement(self) == /\ pc[self] = "Decrement"
                   /\ count' = [count EXCEPT ![self] = count[self] - 1]
                   /\ msg' = [m \in P |-> count'[self]]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]

Counter(self) == Update(self) \/ Increment(self) \/ Decrement(self)

Next == (\E self \in P: Counter(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in P : WF_vars(Counter(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Eventual Convergence:
\* Safety: ∀i, j : C(xi) = C(xj) implies that the abstract states of i and j are equivalent.
Safety == (\A k,l \in P: msg[k] = msg[l])
\* Liveness: ∀i, j : f ∈ C(xi) implies that, eventually, f ∈ C(xj). 
Liveness == <>(\A k \in P: count[k] = msg[k])

================================================================================
\* Modification History
\* Last modified Sun Dec 09 19:15:24 PST 2018 by ocosta
\* Created Sat Dec 01 16:58:15 PST 2018 by ocosta
