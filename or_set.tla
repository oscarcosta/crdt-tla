-------------------------------- MODULE or_set --------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS N, Data

Procs == 1..N 

(*
--algorithm or_set
variables
  ops = [j \in Procs |-> <<>>]; \* to broadcast operations

define \* atSource phases
  _Lookup(set, e) == \E s \in set: s.val = e

  _Add(proc, e) == {[key |-> ToString(proc) \o ToString(e), val |-> e]}  

  _Remove(set, e) == IF _Lookup(set, e) THEN 
    {CHOOSE s \in set: s.val = e} 
  ELSE 
    {}
end define;

\* send a operation to all
macro Broadcast(o, s) begin 
  if s /= {} then
    ops := [j \in Procs |-> Append(ops[j], [op |-> o, set |-> s])];
  end if
end macro;

\* receive and process operations, one by one
macro Update(s) begin 
  if Len(ops[self]) > 0 then
    if Head(ops[self]).op = "A" then
      s := s \union Head(ops[self]).set;
    elsif Head(ops[self]).op = "R" then
      s := s \ Head(ops[self]).set;
    end if;
    ops[self] := Tail(ops[self]); \* clear processed operation
  end if;
end macro;

process Set \in Procs
variables
  set = {}; \* local set of pairs [key |-> "", val |-> ""]
begin Main:
  while TRUE do
    Update(set);
    either Add:
      with var \in Data do \* select a random value to add
        Broadcast("A", _Add(self, var));
      end with;
    or Remove:
      with var \in Data do \* select a random value to remove
        Broadcast("R", _Remove(set, var));
      end with;
    end either;
  end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES ops, pc

(* define statement *)
_Lookup(set, e) == \E s \in set: s.val = e

_Add(proc, e) == {[key |-> ToString(proc) \o ToString(e), val |-> e]}

_Remove(set, e) == IF _Lookup(set, e) THEN
  {CHOOSE s \in set: s.val = e}
ELSE
  {}

VARIABLE set

vars == << ops, pc, set >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ ops = [j \in Procs |-> <<>>]
        (* Process Set *)
        /\ set = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "Main"]

Main(self) == /\ pc[self] = "Main"
              /\ IF Len(ops[self]) > 0
                    THEN /\ IF Head(ops[self]).op = "A"
                               THEN /\ set' = [set EXCEPT ![self] = set[self] \union Head(ops[self]).set]
                               ELSE /\ IF Head(ops[self]).op = "R"
                                          THEN /\ set' = [set EXCEPT ![self] = set[self] \ Head(ops[self]).set]
                                          ELSE /\ TRUE
                                               /\ set' = set
                         /\ ops' = [ops EXCEPT ![self] = Tail(ops[self])]
                    ELSE /\ TRUE
                         /\ UNCHANGED << ops, set >>
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "Add"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "Remove"]

Add(self) == /\ pc[self] = "Add"
             /\ \E var \in Data:
                  IF (_Add(self, var)) /= {}
                     THEN /\ ops' = [j \in Procs |-> Append(ops[j], [op |-> "A", set |-> (_Add(self, var))])]
                     ELSE /\ TRUE
                          /\ ops' = ops
             /\ pc' = [pc EXCEPT ![self] = "Main"]
             /\ set' = set

Remove(self) == /\ pc[self] = "Remove"
                /\ \E var \in Data:
                     IF (_Remove(set[self], var)) /= {}
                        THEN /\ ops' = [j \in Procs |-> Append(ops[j], [op |-> "R", set |-> (_Remove(set[self], var))])]
                        ELSE /\ TRUE
                             /\ ops' = ops
                /\ pc' = [pc EXCEPT ![self] = "Main"]
                /\ set' = set

Set(self) == Main(self) \/ Add(self) \/ Remove(self)

Next == (\E self \in Procs: Set(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

================================================================================
\* Modification History
\* Last modified Wed Dec 12 17:54:27 PST 2018 by ocosta
\* Created Sat Dec 01 19:34:11 PST 2018 by ocosta
