---- MODULE exactly_once_none_atomic ----
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANTS MessageCount, DupCount, NULL

Range(T) == { T[x] : x \in DOMAIN T }
IsEmpty(T) == Cardinality(T) = 0
WithId(T, id) == { x \in T: x.msgId = id }

Processes == 1..2
MessageIds == 1..MessageCount
DupIds == 1..DupCount
VersionIds == 0..2*MessageCount
TxIdx == 0..MessageCount*DupCount

(*--algorithm outbox
variables
    inputQueue = [id : MessageIds, dupId : DupIds],
    outQueue = {},
    store = <<[ver |-> 0, msgId |-> NULL, txId |-> NULL]>>, 
    outbox = [id \in MessageIds \union TxIdx |-> NULL],
    processed = { },

    gVer = 0,
    lVer = [pid \in Process |-> 0]

define 
    InputMessages == [id : MessageIds, dupId : DupIds]
    OutQueueMessages == [msgId : MessageIds, ver : VersionIds]
    TypeInvariant == 
        /\ inputQueue \in SUBSET InputMessages
        /\ outQueue \in SUBSET outQueueMessages
        /\ processed \in SUBSET InputMessages
        /\ Range(store) \in SUBSET [ver : VersionIds, msgId : MessageIds \union {NULL}, txId : TxIdx \union {NULL} ]
        /\ Range(outbox) \in SUBSET (OutQueueMessages \union {NULL})

    AtMostOneStateChange ==
        \A id \in MessageIds : Cardinality(WithId(Range(store),id)) <= 2
    
    AtMostOneoutQueueMsg ==
        \A id \in MessageIds : Cardinality(WithId(outQueue, id)) <= 1

    ConsistentStateAndoutQueue ==
        LET InState(id)  == CHOOSE x \in WithId(Range(store), id) : TRUE
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
    outbox[outbox[txId].msgId] := outbox[txId];
end macro;

macro CommitState(ver, msgId, txId) begin
    with latest = Head(store) do
        if latest.ver = ver then
            either
                store := <<[ver |-> latest.ver + 1, msgId |-> msgId, txId |-> txId]>> \o store ; 
            or
                Fail();
            end either;
        else
            Fail();
        end if;
    end with;
end macro;

macro CleanupState(ver) begin
    with latest = Head(store) do
        if latest.ver = ver then
            either
                store := <<[ver |-> latest.ver + 1, msgId |-> latest.msgId, txId |-> NULL]>> \o store; 
            or
                Fail();
            end either;
        else
            Fail();
        end if;
    end with;
end macro;

fair process HandlerThread \in Processes
variables
    msg,
    txId,
    stateVer
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
        with s = Head(store) do
            txId := s.txId;
            stateVer := s.ver;
        end with;

        if(txId /= NULL) then
            Redo_OutboxCommit: CommitOutbox(txId);
            Redo_StateCleanup: CleanupState(stateVer);
        end if;

    Process:
        if outbox[msg.id] = NULL then
            txId := (msg.id-1)*DupCount + msg.dupId;

            StageOutbox: outbox[txId] := [msgId |-> msg.id, ver |-> stateVer];

            StateCommit: CommitState(stateVer, msg.id, txId);
            
            OutboxCommit: CommitOutbox(txId);

            StateCleanup: CleanupState(stateVer);
        end if;

    SendAndAck:
        outQueue := outQueue \union {outbox[msg.id]};
        processed := processed \union {msg};
            
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b66170bb80c17cb19a196c70f5a37e21
CONSTANT defaultInitValue
VARIABLES inputQueue, outQueue, store, outbox, outboxStagging, processed, pc

(* define statement *)
InputMessages == [id : MessageIds, dupId : DupIds]
outQueueMessages == [msgId : MessageIds, ver : VersionIds]
TypeInvariant ==
    /\ inputQueue \in SUBSET InputMessages
    /\ outQueue \in SUBSET outQueueMessages
    /\ processed \in SUBSET InputMessages
    /\ Range(store) \in SUBSET [ver : VersionIds, msgId : MessageIds \union {NULL}, txId : TxIdx \union {NULL} ]
    /\ Range(outbox) \in SUBSET (outQueueMessages \union {NULL})
    /\ Range(outboxStagging) \in SUBSET (outQueueMessages \union {NULL})

AtMostOneStateChange ==
    \A id \in MessageIds : Cardinality(WithId(Range(store),id)) <= 2

AtMostOneoutQueueMsg ==
    \A id \in MessageIds : Cardinality(WithId(outQueue, id)) <= 1

ConsistentStateAndoutQueue ==
    LET InState(id)  == CHOOSE x \in WithId(Range(store), id) : TRUE
        InoutQueue(id) == CHOOSE x \in WithId(outQueue, id) : TRUE
    IN \A m \in processed: InState(m.id).ver = InoutQueue(m.id).ver

Safety == AtMostOneStateChange /\ AtMostOneoutQueueMsg /\ ConsistentStateAndoutQueue

Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                  /\ IsEmpty(inputQueue))

VARIABLES msg, txId, stateVer

vars == << inputQueue, outQueue, store, outbox, outboxStagging, processed, pc, 
           msg, txId, stateVer >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ inputQueue = [id : MessageIds, dupId : DupIds]
        /\ outQueue = {}
        /\ store = <<[ver |-> 0, msgId |-> NULL, txId |-> NULL]>>
        /\ outbox = [r \in MessageIds |-> NULL]
        /\ outboxStagging = [t \in TxIdx |-> NULL]
        /\ processed = { }
        (* Process HandlerThread *)
        /\ msg = [self \in Processes |-> defaultInitValue]
        /\ txId = [self \in Processes |-> defaultInitValue]
        /\ stateVer = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ pc' = [pc EXCEPT ![self] = "LockInMsg"]
                  /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                  outboxStagging, processed, msg, txId, 
                                  stateVer >>

LockInMsg(self) == /\ pc[self] = "LockInMsg"
                   /\ ~ IsEmpty(inputQueue)
                   /\ \E m \in inputQueue:
                        /\ inputQueue' = { i \in inputQueue : i /= m}
                        /\ msg' = [msg EXCEPT ![self] = m]
                   /\ pc' = [pc EXCEPT ![self] = "LoadState"]
                   /\ UNCHANGED << outQueue, store, outbox, outboxStagging, 
                                   processed, txId, stateVer >>

LoadState(self) == /\ pc[self] = "LoadState"
                   /\ LET s == Head(store) IN
                        /\ txId' = [txId EXCEPT ![self] = s.txId]
                        /\ stateVer' = [stateVer EXCEPT ![self] = s.ver]
                   /\ IF (txId'[self] /= NULL)
                         THEN /\ pc' = [pc EXCEPT ![self] = "Redo_OutboxCommit"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Process"]
                   /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                   outboxStagging, processed, msg >>

Redo_OutboxCommit(self) == /\ pc[self] = "Redo_OutboxCommit"
                           /\ LET msgId == outboxStagging[txId[self]].msgId IN
                                outbox' = [outbox EXCEPT ![msgId] = outboxStagging[txId[self]]]
                           /\ pc' = [pc EXCEPT ![self] = "Redo_StateCleanup"]
                           /\ UNCHANGED << inputQueue, outQueue, store, 
                                           outboxStagging, processed, msg, 
                                           txId, stateVer >>

Redo_StateCleanup(self) == /\ pc[self] = "Redo_StateCleanup"
                           /\ LET latest == Head(store) IN
                                IF latest.ver = stateVer[self]
                                   THEN /\ \/ /\ store' = <<[ver |-> latest.ver + 1, msgId |-> latest.msgId, txId |-> NULL]>> \o store
                                              /\ pc' = [pc EXCEPT ![self] = "Process"]
                                           \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                              /\ store' = store
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                        /\ store' = store
                           /\ UNCHANGED << inputQueue, outQueue, outbox, 
                                           outboxStagging, processed, msg, 
                                           txId, stateVer >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF outbox[msg[self].id] = NULL
                       THEN /\ txId' = [txId EXCEPT ![self] = (msg[self].id-1)*DupCount + msg[self].dupId]
                            /\ pc' = [pc EXCEPT ![self] = "StageOutbox"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "SendAndAck"]
                            /\ txId' = txId
                 /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                 outboxStagging, processed, msg, stateVer >>

StageOutbox(self) == /\ pc[self] = "StageOutbox"
                     /\ outboxStagging' = [outboxStagging EXCEPT ![txId[self]] = [msgId |-> msg[self].id, ver |-> stateVer[self]]]
                     /\ pc' = [pc EXCEPT ![self] = "StateCommit"]
                     /\ UNCHANGED << inputQueue, outQueue, store, outbox, 
                                     processed, msg, txId, stateVer >>

StateCommit(self) == /\ pc[self] = "StateCommit"
                     /\ LET latest == Head(store) IN
                          IF latest.ver = stateVer[self]
                             THEN /\ \/ /\ store' = <<[ver |-> latest.ver + 1, msgId |-> (msg[self].id), txId |-> txId[self]]>> \o store
                                        /\ pc' = [pc EXCEPT ![self] = "OutboxCommit"]
                                     \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                        /\ store' = store
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ store' = store
                     /\ UNCHANGED << inputQueue, outQueue, outbox, 
                                     outboxStagging, processed, msg, txId, 
                                     stateVer >>

OutboxCommit(self) == /\ pc[self] = "OutboxCommit"
                      /\ LET msgId == outboxStagging[txId[self]].msgId IN
                           outbox' = [outbox EXCEPT ![msgId] = outboxStagging[txId[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "StateCleanup"]
                      /\ UNCHANGED << inputQueue, outQueue, store, 
                                      outboxStagging, processed, msg, txId, 
                                      stateVer >>

StateCleanup(self) == /\ pc[self] = "StateCleanup"
                      /\ LET latest == Head(store) IN
                           IF latest.ver = stateVer[self]
                              THEN /\ \/ /\ store' = <<[ver |-> latest.ver + 1, msgId |-> latest.msgId, txId |-> NULL]>> \o store
                                         /\ pc' = [pc EXCEPT ![self] = "SendAndAck"]
                                      \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                         /\ store' = store
                              ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                   /\ store' = store
                      /\ UNCHANGED << inputQueue, outQueue, outbox, 
                                      outboxStagging, processed, msg, txId, 
                                      stateVer >>

SendAndAck(self) == /\ pc[self] = "SendAndAck"
                    /\ outQueue' = (outQueue \union {outbox[msg[self].id]})
                    /\ processed' = (processed \union {msg[self]})
                    /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                    /\ UNCHANGED << inputQueue, store, outbox, outboxStagging, 
                                    msg, txId, stateVer >>

HandlerThread(self) == MainLoop(self) \/ LockInMsg(self) \/ LoadState(self)
                          \/ Redo_OutboxCommit(self)
                          \/ Redo_StateCleanup(self) \/ Process(self)
                          \/ StageOutbox(self) \/ StateCommit(self)
                          \/ OutboxCommit(self) \/ StateCleanup(self)
                          \/ SendAndAck(self)

Next == (\E self \in Processes: HandlerThread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(HandlerThread(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-acf7cb8a0a7a1b5e07100b01a6a2338f

====
