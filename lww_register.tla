----------------------------- MODULE lww_register -----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS N

Procs == 1..N

INITIAL == [t |-> 0, val |-> ""] \* initial value [t |-> 0, val |-> ""]

(*
--algorithm lww_register
variables
  msgs = [j \in Procs |-> INITIAL]; \* to send the messages

define
  _Compare(p1, p2) == p1.t <= p2.t
  
  _Merge(p1, p2) == IF _Compare(p1, p2) THEN p1 ELSE p2
end define;

\* assign a value and timestamp into local payload
macro _Assign(v) begin
  payload := [t |-> JavaTime, val |-> v];
  print ToString(self) \o " assigned " \o ToString(payload);
end macro;

\* send the payload 'p' to a random proc
macro _Send(p) begin
  if payload /= INITIAL then
    with j \in Procs \ {self} do
      msgs[j] := payload;
      print ToString(self) \o " sent " \o ToString(msgs[j]) \o " to " \o ToString(j);
    end with;
  end if;
end macro;

\* receive the payload
macro _Receive() begin
  if msgs[self] /= INITIAL then
    print ToString(self) \o " received " \o ToString(msgs[self]);
    if payload = INITIAL then \* payload is empty, just receive the message
      payload := msgs[self];
    else \* merge the payload and received message
      payload := _Merge(payload, msgs[self]);
    end if; 
    msgs[self] := INITIAL;
    print ToString(self) \o " merged " \o ToString(payload);
  end if;
end macro;

fair process Register \in Procs
variables
  i = 0, \* count iterations
  payload = INITIAL; \* local payload
begin Main:
  while i < N do
    either Assign: 
      _Assign(self);
    or Send:
      _Send(payload);
    or Receive:
      _Receive();
    end either;
    Loop:
      i := i + 1;
  end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES msgs, pc

(* define statement *)
_Compare(p1, p2) == p1.t <= p2.t

_Merge(p1, p2) == IF _Compare(p1, p2) THEN p1 ELSE p2

VARIABLES i, payload

vars == << msgs, pc, i, payload >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ msgs = [j \in Procs |-> INITIAL]
        (* Process Register *)
        /\ i = [self \in Procs |-> 0]
        /\ payload = [self \in Procs |-> INITIAL]
        /\ pc = [self \in ProcSet |-> "Main"]

Main(self) == /\ pc[self] = "Main"
              /\ IF i[self] < N
                    THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Assign"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "Receive"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << msgs, i, payload >>

Loop(self) == /\ pc[self] = "Loop"
              /\ i' = [i EXCEPT ![self] = i[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "Main"]
              /\ UNCHANGED << msgs, payload >>

Assign(self) == /\ pc[self] = "Assign"
                /\ payload' = [payload EXCEPT ![self] = [t |-> JavaTime, val |-> self]]
                /\ PrintT(ToString(self) \o " assigned " \o ToString(payload'[self]))
                /\ pc' = [pc EXCEPT ![self] = "Loop"]
                /\ UNCHANGED << msgs, i >>

Send(self) == /\ pc[self] = "Send"
              /\ IF payload[self] /= INITIAL
                    THEN /\ \E j \in Procs \ {self}:
                              /\ msgs' = [msgs EXCEPT ![j] = payload[self]]
                              /\ PrintT(ToString(self) \o " sent " \o ToString(msgs'[j]) \o " to " \o ToString(j))
                    ELSE /\ TRUE
                         /\ msgs' = msgs
              /\ pc' = [pc EXCEPT ![self] = "Loop"]
              /\ UNCHANGED << i, payload >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ IF msgs[self] /= INITIAL
                       THEN /\ PrintT(ToString(self) \o " received " \o ToString(msgs[self]))
                            /\ IF payload[self] = INITIAL
                                  THEN /\ payload' = [payload EXCEPT ![self] = msgs[self]]
                                  ELSE /\ payload' = [payload EXCEPT ![self] = _Merge(payload[self], msgs[self])]
                            /\ msgs' = [msgs EXCEPT ![self] = INITIAL]
                            /\ PrintT(ToString(self) \o " merged " \o ToString(payload'[self]))
                       ELSE /\ TRUE
                            /\ UNCHANGED << msgs, payload >>
                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                 /\ i' = i

Register(self) == Main(self) \/ Loop(self) \/ Assign(self) \/ Send(self)
                     \/ Receive(self)

Next == (\E self \in Procs: Register(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(Register(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

================================================================================
\* Modification History
\* Last modified Fri Dec 14 17:44:05 PST 2018 by ocosta
\* Created Fri Dec 14 16:18:39 PST 2018 by ocosta
