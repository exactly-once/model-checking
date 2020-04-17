---- MODULE exactly_once ----
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANTS MaxQueue, MaxRetry, NULL, EMPTY

Range(T) == { T[x] : x \in DOMAIN T }
IsEmpty(T) == Cardinality(T) = 0

(*--algorithm outbox
variables
    inputQueue = { [id |-> x, retryNo |-> 0] : x \in 1..MaxQueue },
    store = [log    |-> <<[ver |-> 0, msgId |-> 0]>>, 
             outbox |-> [r \in 1..MaxQueue |-> NULL]],
    output = { },
    processed = { }


define 
    Processes == 1..2
    MessageIds == 1..MaxQueue
    IdRange == 0..MaxQueue
    OutputMessages == {[id |-> i, ver |-> v] : i \in MessageIds, v \in IdRange }
    OutboxEntries == {NULL, EMPTY} \union OutputMessages
    TypeInvariant == 
        /\ \A le \in Range(store.log) : le \in {[ver |-> v, msgId |-> i]: v \in IdRange, i \in IdRange }
        /\ \A oe \in Range(store.outbox) : oe \in OutboxEntries
        /\ inputQueue \in SUBSET [id : 1..MaxQueue, retryNo : 0..MaxRetry]
        /\ output \in SUBSET OutputMessages
    
    AtMostOneStateChange ==
        \A id \in MessageIds : Cardinality({le \in Range(store.log) : le.msgId = id}) <= 1
    
    AtMostOneOutputMsg ==
        \A id \in MessageIds : Cardinality({o \in output: o.id = id}) <= 1
    
    ConsistentStateAndOutput ==
        LET s(id) == CHOOSE le \in Range(store.log) : le.msgId = id 
            o(id) == CHOOSE o \in output : o.id = id
        IN \A m \in processed: s(m.id).ver = o(m.id).ver
    
    Safety == AtMostOneStateChange /\ AtMostOneOutputMsg /\ ConsistentStateAndOutput

    Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                      /\ IsEmpty(inputQueue))
end define;

macro Rollback() begin
    if msg.retryNo < MaxRetry then
        msg.retryNo := msg.retryNo + 1;  
        inputQueue := inputQueue \union {msg};
    end if; 
    goto MainLoop;
end macro;

fair process HandlerThread \in Processes
variables
    msg,
    pState, 
begin
MainLoop:
    while TRUE do
    LockInMsg:
        await ~ IsEmpty(inputQueue);

        with m \in inputQueue do
            inputQueue := { i \in inputQueue : i /= m};
            msg := m;
        end with;

    LoadState:
        pState := store;

        if pState.outbox[msg.id] = NULL then            
        ProcessAndCommit:
            with v = Head(pState.log).ver do
                pState.log := <<[msgId |-> msg.id, ver |-> v + 1]>> \o pState.log ||
                pState.outbox[msg.id] := [id |-> msg.id, ver |-> v + 1];
            end with;

            if Head(store.log).ver + 1 = Head(pState.log).ver then
                either
                    store := pState
                or
                    Rollback();
                end either;
            else 
                Rollback();
            end if;    
        end if;

    SendOutMsg:
        if pState.outbox[msg.id] /= EMPTY then
            either
                output := output \union {pState.outbox[msg.id]};
            or
                Rollback();
            end either;
        end if;

    UpdateOutbox:
        either
            store.outbox[msg.id] := EMPTY
        or
            Rollback();
        end either;
            
    AckInMsg:
        either
            processed := processed \union {msg};
        or 
            Rollback();
        end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES inputQueue, store, output, processed, pc

(* define statement *)
Processes == 1..2
MessageIds == 1..MaxQueue
IdRange == 0..MaxQueue
OutputMessages == {[id |-> i, ver |-> v] : i \in MessageIds, v \in IdRange }
OutboxEntries == {NULL, EMPTY} \union OutputMessages
TypeInvariant ==
    /\ \A le \in Range(store.log) : le \in {[ver |-> v, msgId |-> i]: v \in IdRange, i \in IdRange }
    /\ \A oe \in Range(store.outbox) : oe \in OutboxEntries
    /\ inputQueue \in SUBSET [id : 1..MaxQueue, retryNo : 0..MaxRetry]
    /\ output \in SUBSET OutputMessages

AtMostOneStateChange ==
    \A id \in MessageIds : Cardinality({le \in Range(store.log) : le.msgId = id}) <= 1

AtMostOneOutputMsg ==
    \A id \in MessageIds : Cardinality({o \in output: o.id = id}) <= 1

ConsistentStateAndOutput ==
    LET s(id) == CHOOSE le \in Range(store.log) : le.msgId = id
        o(id) == CHOOSE o \in output : o.id = id
    IN \A m \in processed: s(m.id).ver = o(m.id).ver

Safety == AtMostOneStateChange /\ AtMostOneOutputMsg /\ ConsistentStateAndOutput

Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                  /\ IsEmpty(inputQueue))

VARIABLES msg, pState

vars == << inputQueue, store, output, processed, pc, msg, pState >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ inputQueue = { [id |-> x, retryNo |-> 0] : x \in 1..MaxQueue }
        /\ store = [log    |-> <<[ver |-> 0, msgId |-> 0]>>,
                    outbox |-> [r \in 1..MaxQueue |-> NULL]]
        /\ output = { }
        /\ processed = { }
        (* Process HandlerThread *)
        /\ msg = [self \in Processes |-> defaultInitValue]
        /\ pState = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ pc' = [pc EXCEPT ![self] = "LockInMsg"]
                  /\ UNCHANGED << inputQueue, store, output, processed, msg, 
                                  pState >>

LockInMsg(self) == /\ pc[self] = "LockInMsg"
                   /\ ~ IsEmpty(inputQueue)
                   /\ \E m \in inputQueue:
                        /\ inputQueue' = { i \in inputQueue : i /= m}
                        /\ msg' = [msg EXCEPT ![self] = m]
                   /\ pc' = [pc EXCEPT ![self] = "LoadState"]
                   /\ UNCHANGED << store, output, processed, pState >>

LoadState(self) == /\ pc[self] = "LoadState"
                   /\ pState' = [pState EXCEPT ![self] = store]
                   /\ IF pState'[self].outbox[msg[self].id] = NULL
                         THEN /\ pc' = [pc EXCEPT ![self] = "ProcessAndCommit"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "SendOutMsg"]
                   /\ UNCHANGED << inputQueue, store, output, processed, msg >>

ProcessAndCommit(self) == /\ pc[self] = "ProcessAndCommit"
                          /\ LET v == Head(pState[self].log).ver IN
                               pState' = [pState EXCEPT ![self].log = <<[msgId |-> msg[self].id, ver |-> v + 1]>> \o pState[self].log,
                                                        ![self].outbox[msg[self].id] = [id |-> msg[self].id, ver |-> v + 1]]
                          /\ IF Head(store.log).ver + 1 = Head(pState'[self].log).ver
                                THEN /\ \/ /\ store' = pState'[self]
                                           /\ pc' = [pc EXCEPT ![self] = "SendOutMsg"]
                                           /\ UNCHANGED <<inputQueue, msg>>
                                        \/ /\ IF msg[self].retryNo < MaxRetry
                                                 THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                                      /\ inputQueue' = (inputQueue \union {msg'[self]})
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << inputQueue, 
                                                                      msg >>
                                           /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                           /\ store' = store
                                ELSE /\ IF msg[self].retryNo < MaxRetry
                                           THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                                /\ inputQueue' = (inputQueue \union {msg'[self]})
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << inputQueue, 
                                                                msg >>
                                     /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                     /\ store' = store
                          /\ UNCHANGED << output, processed >>

SendOutMsg(self) == /\ pc[self] = "SendOutMsg"
                    /\ IF pState[self].outbox[msg[self].id] /= EMPTY
                          THEN /\ \/ /\ output' = (output \union {pState[self].outbox[msg[self].id]})
                                     /\ pc' = [pc EXCEPT ![self] = "UpdateOutbox"]
                                     /\ UNCHANGED <<inputQueue, msg>>
                                  \/ /\ IF msg[self].retryNo < MaxRetry
                                           THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                                /\ inputQueue' = (inputQueue \union {msg'[self]})
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << inputQueue, 
                                                                msg >>
                                     /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                     /\ UNCHANGED output
                          ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateOutbox"]
                               /\ UNCHANGED << inputQueue, output, msg >>
                    /\ UNCHANGED << store, processed, pState >>

UpdateOutbox(self) == /\ pc[self] = "UpdateOutbox"
                      /\ \/ /\ store' = [store EXCEPT !.outbox[msg[self].id] = EMPTY]
                            /\ pc' = [pc EXCEPT ![self] = "AckInMsg"]
                            /\ UNCHANGED <<inputQueue, msg>>
                         \/ /\ IF msg[self].retryNo < MaxRetry
                                  THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                       /\ inputQueue' = (inputQueue \union {msg'[self]})
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << inputQueue, msg >>
                            /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                            /\ store' = store
                      /\ UNCHANGED << output, processed, pState >>

AckInMsg(self) == /\ pc[self] = "AckInMsg"
                  /\ \/ /\ processed' = (processed \union {msg[self]})
                        /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                        /\ UNCHANGED <<inputQueue, msg>>
                     \/ /\ IF msg[self].retryNo < MaxRetry
                              THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                   /\ inputQueue' = (inputQueue \union {msg'[self]})
                              ELSE /\ TRUE
                                   /\ UNCHANGED << inputQueue, msg >>
                        /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                        /\ UNCHANGED processed
                  /\ UNCHANGED << store, output, pState >>

HandlerThread(self) == MainLoop(self) \/ LockInMsg(self) \/ LoadState(self)
                          \/ ProcessAndCommit(self) \/ SendOutMsg(self)
                          \/ UpdateOutbox(self) \/ AckInMsg(self)

Next == (\E self \in Processes: HandlerThread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(HandlerThread(self))

\* END TRANSLATION

====
