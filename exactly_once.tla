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
    output = { }


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
    
    SingleStateChange ==
        \A id \in MessageIds : Cardinality({le \in Range(store.log) : le.msgId = id}) <= 1
    
    SingleOutputMsg ==
        \A id \in MessageIds : Cardinality({o \in output: o.id = id}) <= 1
    
    ConsistentStateAndOutput ==
        \A id \in MessageIds : (\E le \in Range(store.log) : le.msgId = id /\ \E o \in output : o.id = id) 
                                => 
                               (CHOOSE x \in Range(store.log) : x.msgId = id).ver = (CHOOSE x \in output : x.id = id).ver
    
    
    Safety == SingleStateChange /\ SingleOutputMsg /\ ConsistentStateAndOutput

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
    state, 
    nState,
    outbox,
    outboxRecord,
    outputMsg
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
        state := Head(store.log);
        outbox := store.outbox;

        if outbox[msg.id] = NULL then
        Process:
            outputMsg := [id |-> msg.id, ver |-> state.ver + 1];
            nState := [msgId |-> msg.id, ver |-> state.ver + 1];

            if Head(store.log).ver = state.ver then
                either
                    store.log := Append(store.log, nState);
                    outbox[msg.id] := outputMsg;
                or
                    Rollback();
                end either;
            else 
                Rollback();
            end if;    
        end if;

    SendOutMsg:
        if outbox[msg.id] /= EMPTY then
            either
                output := output \union {outputMsg};
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
            skip;
        or 
            Rollback();
        end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES inputQueue, store, output, pc

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

SingleStateChange ==
    \A id \in MessageIds : Cardinality({le \in Range(store.log) : le.msgId = id}) <= 1

SingleOutputMsg ==
    \A id \in MessageIds : Cardinality({o \in output: o.id = id}) <= 1

ConsistentStateAndOutput ==
    \A id \in MessageIds : (\E le \in Range(store.log) : le.msgId = id /\ \E o \in output : o.id = id)
                            =>
                           (CHOOSE x \in Range(store.log) : x.msgId = id).ver = (CHOOSE x \in output : x.id = id).ver


Safety == SingleStateChange /\ SingleOutputMsg /\ ConsistentStateAndOutput

Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                  /\ IsEmpty(inputQueue))

VARIABLES msg, state, nState, outbox, outboxRecord, outputMsg

vars == << inputQueue, store, output, pc, msg, state, nState, outbox, 
           outboxRecord, outputMsg >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ inputQueue = { [id |-> x, retryNo |-> 0] : x \in 1..MaxQueue }
        /\ store = [log    |-> <<[ver |-> 0, msgId |-> 0]>>,
                    outbox |-> [r \in 1..MaxQueue |-> NULL]]
        /\ output = { }
        (* Process HandlerThread *)
        /\ msg = [self \in Processes |-> defaultInitValue]
        /\ state = [self \in Processes |-> defaultInitValue]
        /\ nState = [self \in Processes |-> defaultInitValue]
        /\ outbox = [self \in Processes |-> defaultInitValue]
        /\ outboxRecord = [self \in Processes |-> defaultInitValue]
        /\ outputMsg = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ pc' = [pc EXCEPT ![self] = "LockInMsg"]
                  /\ UNCHANGED << inputQueue, store, output, msg, state, 
                                  nState, outbox, outboxRecord, outputMsg >>

LockInMsg(self) == /\ pc[self] = "LockInMsg"
                   /\ ~ IsEmpty(inputQueue)
                   /\ \E m \in inputQueue:
                        /\ inputQueue' = { i \in inputQueue : i /= m}
                        /\ msg' = [msg EXCEPT ![self] = m]
                   /\ pc' = [pc EXCEPT ![self] = "LoadState"]
                   /\ UNCHANGED << store, output, state, nState, outbox, 
                                   outboxRecord, outputMsg >>

LoadState(self) == /\ pc[self] = "LoadState"
                   /\ state' = [state EXCEPT ![self] = Head(store.log)]
                   /\ outbox' = [outbox EXCEPT ![self] = store.outbox]
                   /\ IF outbox'[self][msg[self].id] = NULL
                         THEN /\ pc' = [pc EXCEPT ![self] = "Process"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "SendOutMsg"]
                   /\ UNCHANGED << inputQueue, store, output, msg, nState, 
                                   outboxRecord, outputMsg >>

Process(self) == /\ pc[self] = "Process"
                 /\ outputMsg' = [outputMsg EXCEPT ![self] = [id |-> msg[self].id, ver |-> state[self].ver + 1]]
                 /\ nState' = [nState EXCEPT ![self] = [msgId |-> msg[self].id, ver |-> state[self].ver + 1]]
                 /\ IF Head(store.log).ver = state[self].ver
                       THEN /\ \/ /\ store' = [store EXCEPT !.log = Append(store.log, nState'[self])]
                                  /\ outbox' = [outbox EXCEPT ![self][msg[self].id] = outputMsg'[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "SendOutMsg"]
                                  /\ UNCHANGED <<inputQueue, msg>>
                               \/ /\ IF msg[self].retryNo < MaxRetry
                                        THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                             /\ inputQueue' = (inputQueue \union {msg'[self]})
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << inputQueue, msg >>
                                  /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ UNCHANGED <<store, outbox>>
                       ELSE /\ IF msg[self].retryNo < MaxRetry
                                  THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                       /\ inputQueue' = (inputQueue \union {msg'[self]})
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << inputQueue, msg >>
                            /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                            /\ UNCHANGED << store, outbox >>
                 /\ UNCHANGED << output, state, outboxRecord >>

SendOutMsg(self) == /\ pc[self] = "SendOutMsg"
                    /\ IF outbox[self][msg[self].id] /= EMPTY
                          THEN /\ \/ /\ output' = (output \union {outputMsg[self]})
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
                    /\ UNCHANGED << store, state, nState, outbox, outboxRecord, 
                                    outputMsg >>

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
                      /\ UNCHANGED << output, state, nState, outbox, 
                                      outboxRecord, outputMsg >>

AckInMsg(self) == /\ pc[self] = "AckInMsg"
                  /\ \/ /\ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                        /\ UNCHANGED <<inputQueue, msg>>
                     \/ /\ IF msg[self].retryNo < MaxRetry
                              THEN /\ msg' = [msg EXCEPT ![self].retryNo = msg[self].retryNo + 1]
                                   /\ inputQueue' = (inputQueue \union {msg'[self]})
                              ELSE /\ TRUE
                                   /\ UNCHANGED << inputQueue, msg >>
                        /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                  /\ UNCHANGED << store, output, state, nState, outbox, 
                                  outboxRecord, outputMsg >>

HandlerThread(self) == MainLoop(self) \/ LockInMsg(self) \/ LoadState(self)
                          \/ Process(self) \/ SendOutMsg(self)
                          \/ UpdateOutbox(self) \/ AckInMsg(self)

Next == (\E self \in Processes: HandlerThread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(HandlerThread(self))

\* END TRANSLATION

====
