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

(*--algorithm outbox
variables
    inputQueue = [id : MessageIds, dupId : DupIds],
    store = [history |-> <<>>, ver |-> 0, tx |-> NULL], 
    outbox = [r \in MessageIds |-> [state |-> NULL, out |-> NULL]],
    output = { },
    processed = { }

define 
    InputMessages == [id : MessageIds, dupId : DupIds]
    OutputMessages == [msgId : MessageIds, ver : VersionIds]
    OutboxEntries == [state : {NULL, COMMITTED}, out : OutputMessages \union {NULL}]
    TypeInvariant == 
        /\ inputQueue \in SUBSET InputMessages
        /\ output \in SUBSET OutputMessages
        /\ processed \in SUBSET InputMessages
        /\ store.ver \in VersionIds
        /\ store.tx \in (MessageIds \union {NULL})
        /\ Range(store.history) \in SUBSET [ver : VersionIds, msgId : MessageIds ]
        /\ Range(outbox) \in SUBSET OutboxEntries

    AtMostOneStateChange ==
        \A id \in MessageIds : Cardinality(WithId(Range(store.history),id)) <= 1
    
    AtMostOneOutputMsg ==
        \A id \in MessageIds : Cardinality(WithId(output, id)) <= 1

    ConsistentStateAndOutput ==
        LET InState(id)  == CHOOSE x \in WithId(Range(store.history), id) : TRUE
            InOutput(id) == CHOOSE x \in WithId(output, id) : TRUE
        IN \A m \in processed: InState(m.id).ver = InOutput(m.id).ver
    
    Safety == AtMostOneStateChange /\ AtMostOneOutputMsg /\ ConsistentStateAndOutput

    Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                      /\ IsEmpty(inputQueue))
end define;

macro Rollback() begin
    goto MainLoop;
end macro;

macro CommitOutbox(msgId) begin
    outbox[msgId].state := COMMITTED;
end macro;

macro CommitState(state) begin
    if store.ver + 1 = state.ver then
        either
            store := state;
        or
            Rollback();
        end either;
    else
        Rollback();
    end if;
end macro;

macro CleanupState(state) begin
    if store.ver = state.ver then
        either
            store.tx := NULL || store.ver := store.ver + 1;
        or
            Rollback();
        end either;
    else
        Rollback();
    end if;
end macro;

fair process HandlerThread \in Processes
variables
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
        if outbox[msg.id].state = NULL then
            
            state.history := <<[msgId |-> msg.id, ver |-> state.ver + 1]>> \o state.history ||
            state.tx := msg.id ||
            state.ver := state.ver + 1;

        StageOutbox:
            outbox[msg.id].out := [msgId |-> msg.id, ver |-> state.ver];

        StateCommit:
            CommitState(state);
            
        OutboxCommit:
            CommitOutbox(msg.id);

        StateCleanup:
            CleanupState(state);
        end if;

    SendAndAck:
        output := output \union {outbox[msg.id].out};
        processed := processed \union {msg};
            
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES inputQueue, store, outbox, output, processed, pc

(* define statement *)
InputMessages == [id : MessageIds, dupId : DupIds]
OutputMessages == [msgId : MessageIds, ver : VersionIds]
OutboxEntries == [state : {NULL, COMMITTED}, out : OutputMessages \union {NULL}]
TypeInvariant ==
    /\ inputQueue \in SUBSET InputMessages
    /\ output \in SUBSET OutputMessages
    /\ processed \in SUBSET InputMessages
    /\ store.ver \in VersionIds
    /\ store.tx \in (MessageIds \union {NULL})
    /\ Range(store.history) \in SUBSET [ver : VersionIds, msgId : MessageIds ]
    /\ Range(outbox) \in SUBSET OutboxEntries

AtMostOneStateChange ==
    \A id \in MessageIds : Cardinality(WithId(Range(store.history),id)) <= 1

AtMostOneOutputMsg ==
    \A id \in MessageIds : Cardinality(WithId(output, id)) <= 1

ConsistentStateAndOutput ==
    LET InState(id)  == CHOOSE x \in WithId(Range(store.history), id) : TRUE
        InOutput(id) == CHOOSE x \in WithId(output, id) : TRUE
    IN \A m \in processed: InState(m.id).ver = InOutput(m.id).ver

Safety == AtMostOneStateChange /\ AtMostOneOutputMsg /\ ConsistentStateAndOutput

Termination == <>(/\ \A self \in Processes: pc[self] = "LockInMsg"
                  /\ IsEmpty(inputQueue))

VARIABLES msg, state, nextState

vars == << inputQueue, store, outbox, output, processed, pc, msg, state, 
           nextState >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ inputQueue = [id : MessageIds, dupId : DupIds]
        /\ store = [history |-> <<>>, ver |-> 0, tx |-> NULL]
        /\ outbox = [r \in MessageIds |-> [state |-> NULL, out |-> NULL]]
        /\ output = { }
        /\ processed = { }
        (* Process HandlerThread *)
        /\ msg = [self \in Processes |-> defaultInitValue]
        /\ state = [self \in Processes |-> defaultInitValue]
        /\ nextState = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ pc' = [pc EXCEPT ![self] = "LockInMsg"]
                  /\ UNCHANGED << inputQueue, store, outbox, output, processed, 
                                  msg, state, nextState >>

LockInMsg(self) == /\ pc[self] = "LockInMsg"
                   /\ ~ IsEmpty(inputQueue)
                   /\ \E m \in inputQueue:
                        /\ inputQueue' = { i \in inputQueue : i /= m}
                        /\ msg' = [msg EXCEPT ![self] = m]
                   /\ state' = [state EXCEPT ![self] = store]
                   /\ IF (state'[self].tx /= NULL)
                         THEN /\ pc' = [pc EXCEPT ![self] = "Redo_OutboxCommit"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Process"]
                   /\ UNCHANGED << store, outbox, output, processed, nextState >>

Redo_OutboxCommit(self) == /\ pc[self] = "Redo_OutboxCommit"
                           /\ outbox' = [outbox EXCEPT ![(state[self].tx)].state = COMMITTED]
                           /\ pc' = [pc EXCEPT ![self] = "Redo_StateCommit"]
                           /\ UNCHANGED << inputQueue, store, output, 
                                           processed, msg, state, nextState >>

Redo_StateCommit(self) == /\ pc[self] = "Redo_StateCommit"
                          /\ IF store.ver = state[self].ver
                                THEN /\ \/ /\ store' = [store EXCEPT !.tx = NULL,
                                                                     !.ver = store.ver + 1]
                                           /\ pc' = [pc EXCEPT ![self] = "Process"]
                                        \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                           /\ store' = store
                                ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                     /\ store' = store
                          /\ UNCHANGED << inputQueue, outbox, output, 
                                          processed, msg, state, nextState >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF outbox[msg[self].id].state = NULL
                       THEN /\ state' = [state EXCEPT ![self].history = <<[msgId |-> msg[self].id, ver |-> state[self].ver + 1]>> \o state[self].history,
                                                      ![self].tx = msg[self].id,
                                                      ![self].ver = state[self].ver + 1]
                            /\ pc' = [pc EXCEPT ![self] = "StageOutbox"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "SendAndAck"]
                            /\ state' = state
                 /\ UNCHANGED << inputQueue, store, outbox, output, processed, 
                                 msg, nextState >>

StageOutbox(self) == /\ pc[self] = "StageOutbox"
                     /\ outbox' = [outbox EXCEPT ![msg[self].id].out = [msgId |-> msg[self].id, ver |-> state[self].ver]]
                     /\ pc' = [pc EXCEPT ![self] = "StateCommit"]
                     /\ UNCHANGED << inputQueue, store, output, processed, msg, 
                                     state, nextState >>

StateCommit(self) == /\ pc[self] = "StateCommit"
                     /\ IF store.ver + 1 = state[self].ver
                           THEN /\ \/ /\ store' = state[self]
                                      /\ pc' = [pc EXCEPT ![self] = "OutboxCommit"]
                                   \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                      /\ store' = store
                           ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                /\ store' = store
                     /\ UNCHANGED << inputQueue, outbox, output, processed, 
                                     msg, state, nextState >>

OutboxCommit(self) == /\ pc[self] = "OutboxCommit"
                      /\ outbox' = [outbox EXCEPT ![(msg[self].id)].state = COMMITTED]
                      /\ pc' = [pc EXCEPT ![self] = "StateCleanup"]
                      /\ UNCHANGED << inputQueue, store, output, processed, 
                                      msg, state, nextState >>

StateCleanup(self) == /\ pc[self] = "StateCleanup"
                      /\ IF store.ver = state[self].ver
                            THEN /\ \/ /\ store' = [store EXCEPT !.tx = NULL,
                                                                 !.ver = store.ver + 1]
                                       /\ pc' = [pc EXCEPT ![self] = "SendAndAck"]
                                    \/ /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ store' = store
                            ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                 /\ store' = store
                      /\ UNCHANGED << inputQueue, outbox, output, processed, 
                                      msg, state, nextState >>

SendAndAck(self) == /\ pc[self] = "SendAndAck"
                    /\ output' = (output \union {outbox[msg[self].id].out})
                    /\ processed' = (processed \union {msg[self]})
                    /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                    /\ UNCHANGED << inputQueue, store, outbox, msg, state, 
                                    nextState >>

HandlerThread(self) == MainLoop(self) \/ LockInMsg(self)
                          \/ Redo_OutboxCommit(self)
                          \/ Redo_StateCommit(self) \/ Process(self)
                          \/ StageOutbox(self) \/ StateCommit(self)
                          \/ OutboxCommit(self) \/ StateCleanup(self)
                          \/ SendAndAck(self)

Next == (\E self \in Processes: HandlerThread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(HandlerThread(self))

\* END TRANSLATION

====
