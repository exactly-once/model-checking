---- MODULE exactly_once_none_atomic ----
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANTS MessageCount, DupCount, NULL, EMPTY, COMMITTED

Range(T) == { T[x] : x \in DOMAIN T }
IsEmpty(T) == Cardinality(T) = 0
WithId(T, id) == { x \in T: x.msgId = id }

Processes == 1..2
MessageIds == 1..MessageCount
DupIds == 1..DupCount
VersionIds == 0..2*MessageCount
TxIdx == 1..MessageCount*DupCount

(*--algorithm outbox
variables
    inputQueue = [id : MessageIds, dupId : DupIds],
    outQueue = { },
    store = [history |-> <<>>, ver |-> 0, tx |-> NULL], 
    outbox = [r \in MessageIds |-> NULL],
    outboxStagging = [t \in TxIdx |-> NULL],
    processed = { }

define 
    InputMessages == [id : MessageIds, dupId : DupIds]
    outQueueMessages == [msgId : MessageIds, ver : VersionIds]
    TypeInvariant == 
        /\ inputQueue \in SUBSET InputMessages
        /\ outQueue \in SUBSET outQueueMessages
        /\ processed \in SUBSET InputMessages
        /\ store.ver \in VersionIds
        /\ store.tx \in (TxIdx \union {NULL})
        /\ Range(store.history) \in SUBSET [ver : VersionIds, msgId : MessageIds ]
        /\ Range(outbox) \in SUBSET (outQueueMessages \union {NULL})
        /\ Range(outboxStagging) \in SUBSET (outQueueMessages \union {NULL})

    AtMostOneStateChange ==
        \A id \in MessageIds : Cardinality(WithId(Range(store.history),id)) <= 1
    
    AtMostOneoutQueueMsg ==
        \A id \in MessageIds : Cardinality(WithId(outQueue, id)) <= 1

    ConsistentStateAndoutQueue ==
        LET InState(id)  == CHOOSE x \in WithId(Range(store.history), id) : TRUE
            InoutQueue(id) == CHOOSE x \in WithId(outQueue, id) : TRUE
        IN \A m \in processed: InState(m.id).ver = InoutQueue(m.id).ver
    
    Safety == AtMostOneStateChange /\ AtMostOneoutQueueMsg /\ ConsistentStateAndoutQueue

    Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                      /\ IsEmpty(inputQueue))
end define;

macro Fail() begin
    goto MainLoop;
end macro;

macro CommitOutbox(txId) begin
    with msgId = outboxStagging[txId].msgId do
        outbox[msgId] := outboxStagging[txId];
    end with;
end macro;

macro CommitState(state) begin
    if store.ver + 1 = state.ver then
        either
            store := state;
        or
            Fail();
        end either;
    else
        Fail();
    end if;
end macro;

macro CleanupState(state) begin
    if store.ver = state.ver then
        either
            store.tx := NULL || store.ver := store.ver + 1;
        or
            Fail();
        end either;
    else
        Fail();
    end if;
end macro;

fair process HandlerThread \in Processes
variables
    txId,
    msg,
    state, 
    nextState
begin
MainLoop:
    while TRUE do
    LockInMsg:
        await ~ IsEmpty(inputQueue);

        with m \in inputQueue do
            inputQueue := { i \in inputQueue : i /= m};
            msg := m;
        end with;

        state := store;

        if(state.tx /= NULL) then
        Redo_OutboxCommit:
            CommitOutbox(state.tx);
        Redo_StateCommit:
            CleanupState(state);
        end if;

    Process:
        if outbox[msg.id] = NULL then
            txId := (msg.id-1)*DupCount + msg.dupId;

            state.history := <<[msgId |-> msg.id, ver |-> state.ver + 1]>> \o state.history ||
            state.tx := txId ||
            state.ver := state.ver + 1;

        StageOutbox:
            outboxStagging[txId] := [msgId |-> msg.id, ver |-> state.ver];

        StateCommit:
            CommitState(state);
            
        OutboxCommit:
            CommitOutbox(txId);

        StateCleanup:
            CleanupState(state);
        end if;

    SendAndAck:
        outQueue := outQueue \union {outbox[msg.id]};
        processed := processed \union {msg};
            
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4f58ef387108de1fcc75c2eaf85ad2a0
CONSTANT defaultInitValue
VARIABLES inputQueue, outQueue, store, outbox, outboxStagging, processed, pc

(* define statement *)
InputMessages == [id : MessageIds, dupId : DupIds]
outQueueMessages == [msgId : MessageIds, ver : VersionIds]
TypeInvariant ==
    /\ inputQueue \in SUBSET InputMessages
    /\ outQueue \in SUBSET outQueueMessages
    /\ processed \in SUBSET InputMessages
    /\ store.ver \in VersionIds
    /\ store.tx \in (TxIdx \union {NULL})
    /\ Range(store.history) \in SUBSET [ver : VersionIds, msgId : MessageIds ]
    /\ Range(outbox) \in SUBSET (outQueueMessages \union {NULL})
    /\ Range(outboxStagging) \in SUBSET (outQueueMessages \union {NULL})

AtMostOneStateChange ==
    \A id \in MessageIds : Cardinality(WithId(Range(store.history),id)) <= 1

AtMostOneoutQueueMsg ==
    \A id \in MessageIds : Cardinality(WithId(outQueue, id)) <= 1

ConsistentStateAndoutQueue ==
    LET InState(id)  == CHOOSE x \in WithId(Range(store.history), id) : TRUE
        InoutQueue(id) == CHOOSE x \in WithId(outQueue, id) : TRUE
    IN \A m \in processed: InState(m.id).ver = InoutQueue(m.id).ver

Safety == AtMostOneStateChange /\ AtMostOneoutQueueMsg /\ ConsistentStateAndoutQueue

Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                  /\ IsEmpty(inputQueue))

VARIABLES txId, msg, state, nextState

vars == << inputQueue, outQueue, store, outbox, outboxStagging, processed, pc, 
           txId, msg, state, nextState >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ inputQueue = [id : MessageIds, dupId : DupIds]
        /\ outQueue = { }
        /\ store = [history |-> <<>>, ver |-> 0, tx |-> NULL]
        /\ outbox = [r \in MessageIds |-> NULL]
        /\ outboxStagging = [t \in TxIdx |-> NULL]
        /\ processed = { }
        (* Process HandlerThread *)
        /\ txId = [self \in Processes |-> defaultInitValue]
        /\ msg = [self \in Processes |-> defaultInitValue]
        /\ state = [self \in Processes |-> defaultInitValue]
        /\ nextState = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ pc' = [pc EXCEPT ![self] = "LockInMsg"]
                  /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                  outboxStagging, processed, txId, msg, state, 
                                  nextState >>

LockInMsg(self) == /\ pc[self] = "LockInMsg"
                   /\ ~ IsEmpty(inputQueue)
                   /\ \E m \in inputQueue:
                        /\ inputQueue' = { i \in inputQueue : i /= m}
                        /\ msg' = [msg EXCEPT ![self] = m]
                   /\ state' = [state EXCEPT ![self] = store]
                   /\ IF (state'[self].tx /= NULL)
                         THEN /\ pc' = [pc EXCEPT ![self] = "Redo_OutboxCommit"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Process"]
                   /\ UNCHANGED << outQueue, store, outbox, outboxStagging, 
                                   processed, txId, nextState >>

Redo_OutboxCommit(self) == /\ pc[self] = "Redo_OutboxCommit"
                           /\ LET msgId == outboxStagging[(state[self].tx)].msgId IN
                                outbox' = [outbox EXCEPT ![msgId] = outboxStagging[(state[self].tx)]]
                           /\ pc' = [pc EXCEPT ![self] = "Redo_StateCommit"]
                           /\ UNCHANGED << inputQueue, outQueue, store, 
                                           outboxStagging, processed, txId, 
                                           msg, state, nextState >>

Redo_StateCommit(self) == /\ pc[self] = "Redo_StateCommit"
                          /\ IF store.ver = state[self].ver
                                THEN /\ \/ /\ store' = [store EXCEPT !.tx = NULL,
                                                                     !.ver = store.ver + 1]
                                           /\ pc' = [pc EXCEPT ![self] = "Process"]
                                        \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                           /\ store' = store
                                ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                     /\ store' = store
                          /\ UNCHANGED << inputQueue, outQueue, outbox, 
                                          outboxStagging, processed, txId, msg, 
                                          state, nextState >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF outbox[msg[self].id] = NULL
                       THEN /\ txId' = [txId EXCEPT ![self] = (msg[self].id-1)*DupCount + msg[self].dupId]
                            /\ state' = [state EXCEPT ![self].history = <<[msgId |-> msg[self].id, ver |-> state[self].ver + 1]>> \o state[self].history,
                                                      ![self].tx = txId'[self],
                                                      ![self].ver = state[self].ver + 1]
                            /\ pc' = [pc EXCEPT ![self] = "StageOutbox"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "SendAndAck"]
                            /\ UNCHANGED << txId, state >>
                 /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                 outboxStagging, processed, msg, nextState >>

StageOutbox(self) == /\ pc[self] = "StageOutbox"
                     /\ outboxStagging' = [outboxStagging EXCEPT ![txId[self]] = [msgId |-> msg[self].id, ver |-> state[self].ver]]
                     /\ pc' = [pc EXCEPT ![self] = "StateCommit"]
                     /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                     processed, txId, msg, state, nextState >>

StateCommit(self) == /\ pc[self] = "StateCommit"
                     /\ IF store.ver + 1 = state[self].ver
                           THEN /\ \/ /\ store' = state[self]
                                      /\ pc' = [pc EXCEPT ![self] = "OutboxCommit"]
                                   \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                      /\ store' = store
                           ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                /\ store' = store
                     /\ UNCHANGED << inputQueue, outQueue, outbox, 
                                     outboxStagging, processed, txId, msg, 
                                     state, nextState >>

OutboxCommit(self) == /\ pc[self] = "OutboxCommit"
                      /\ LET msgId == outboxStagging[txId[self]].msgId IN
                           outbox' = [outbox EXCEPT ![msgId] = outboxStagging[txId[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "StateCleanup"]
                      /\ UNCHANGED << inputQueue, outQueue, store, 
                                      outboxStagging, processed, txId, msg, 
                                      state, nextState >>

StateCleanup(self) == /\ pc[self] = "StateCleanup"
                      /\ IF store.ver = state[self].ver
                            THEN /\ \/ /\ store' = [store EXCEPT !.tx = NULL,
                                                                 !.ver = store.ver + 1]
                                       /\ pc' = [pc EXCEPT ![self] = "SendAndAck"]
                                    \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ store' = store
                            ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                 /\ store' = store
                      /\ UNCHANGED << inputQueue, outQueue, outbox, 
                                      outboxStagging, processed, txId, msg, 
                                      state, nextState >>

SendAndAck(self) == /\ pc[self] = "SendAndAck"
                    /\ outQueue' = (outQueue \union {outbox[msg[self].id]})
                    /\ processed' = (processed \union {msg[self]})
                    /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                    /\ UNCHANGED << inputQueue, store, outbox, outboxStagging, 
                                    txId, msg, state, nextState >>

HandlerThread(self) == MainLoop(self) \/ LockInMsg(self)
                          \/ Redo_OutboxCommit(self)
                          \/ Redo_StateCommit(self) \/ Process(self)
                          \/ StageOutbox(self) \/ StateCommit(self)
                          \/ OutboxCommit(self) \/ StateCleanup(self)
                          \/ SendAndAck(self)

Next == (\E self \in Processes: HandlerThread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(HandlerThread(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-254255f319466daf6b3fe4fd46c5aa00

====
