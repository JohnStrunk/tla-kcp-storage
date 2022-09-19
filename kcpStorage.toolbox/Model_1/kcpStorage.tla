----------------------------- MODULE kcpStorage -----------------------------
(***************************************************************************)
(* Goal: Modeling interaction of controllers/users to ensure data safety   *)
(* as data and workloads are created, deleted, used, and migrated across   *)
(* clusters                                                                *)
(***************************************************************************)

(***************************************************************************
Processes:

- Controllers

- Users


Constants:

- Clusters - Set of locations where things can be deployed.

- Namepaces - Set of kcp namespaces.  For now, skip this and only model
a single NS.  Extend the model once we have cross NS interaction

- PVCs - Set of PVCs.  Since they don't interact w/ each other, we'll
only model one

- SyncStates - "nil", "Empty", "Sync"


State:

- ns - record mapping Clusters to SyncStates.  This represents the
state/A:"" label on the namespace

- pvc - record mapping Clusters to SyncStates, representing the state/A
label on the PVC.
 ***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    CLUSTERS,   \* The set of clusters that workloads can be assigned to.
    NC, PVCC, U \* Model values

ASSUME
    Cardinality(CLUSTERS) > 0

SyncStates == {"nil", "Empty", "Sync"}

(* --fair algorithm kcpStorage
variables
    \* Namespaces start unassigned to any cluster
    ns = [c \in CLUSTERS |-> "nil"],
    pvc = [c \in CLUSTERS |-> "nil"]

\* Process representing the user's actions
\*process User = U
\*begin
\*    Start:
\*    skip;
\*end process;

\* The kcp-level Namespace controller
process NamespaceController = NC
variables
begin
    Start:
    \*assert(PrintT(<<ns, pvc>>));
    either \* Assign a NS to a cluster
        await \A c \in CLUSTERS: ns[c] = "nil"; \* Only assign if not on any cluster
        with c \in CLUSTERS do
            ns[c] := "Sync";
        end with;
    or \* Remove the NS from a cluster
        with c \in {c \in CLUSTERS: ns[c] = "Sync"} do
            ns[c] := "nil";
        end with;
    end either;
    goto Start;
end process;

\* kcp-level PVC controller
process PVCController = PVCC
begin
    Start:
    pvc := ns; \* Set the PVC's state to match the NS state
    goto Start;
end process;

\* The syncer process running on each workload cluster
process Syncer \in CLUSTERS
variables
    pvc_state = "nil" \* Starts not synced here
begin
    Start:
    \* Update our local state to match desired
    pvc_state := ns[self];
    goto Start;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c54d5efb" /\ chksum(tla) = "2e992517")
\* Label Start of process NamespaceController at line 67 col 5 changed to Start_
\* Label Start of process PVCController at line 84 col 5 changed to Start_P
VARIABLES ns, pvc, pc, pvc_state

vars == << ns, pvc, pc, pvc_state >>

ProcSet == {NC} \cup {PVCC} \cup (CLUSTERS)

Init == (* Global variables *)
        /\ ns = [c \in CLUSTERS |-> "nil"]
        /\ pvc = [c \in CLUSTERS |-> "nil"]
        (* Process Syncer *)
        /\ pvc_state = [self \in CLUSTERS |-> "nil"]
        /\ pc = [self \in ProcSet |-> CASE self = NC -> "Start_"
                                        [] self = PVCC -> "Start_P"
                                        [] self \in CLUSTERS -> "Start"]

Start_ == /\ pc[NC] = "Start_"
          /\ \/ /\ \A c \in CLUSTERS: ns[c] = "nil"
                /\ \E c \in CLUSTERS:
                     ns' = [ns EXCEPT ![c] = "Sync"]
             \/ /\ \E c \in {c \in CLUSTERS: ns[c] = "Sync"}:
                     ns' = [ns EXCEPT ![c] = "nil"]
          /\ pc' = [pc EXCEPT ![NC] = "Start_"]
          /\ UNCHANGED << pvc, pvc_state >>

NamespaceController == Start_

Start_P == /\ pc[PVCC] = "Start_P"
           /\ pvc' = ns
           /\ pc' = [pc EXCEPT ![PVCC] = "Start_P"]
           /\ UNCHANGED << ns, pvc_state >>

PVCController == Start_P

Start(self) == /\ pc[self] = "Start"
               /\ pvc_state' = [pvc_state EXCEPT ![self] = ns[self]]
               /\ pc' = [pc EXCEPT ![self] = "Start"]
               /\ UNCHANGED << ns, pvc >>

Syncer(self) == Start(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == NamespaceController \/ PVCController
           \/ (\E self \in CLUSTERS: Syncer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

-----------------------------------------------------------------------------

\* All variables are of the correct type
TypeOK ==
    \* ns has a mapping for exactly every cluster
    /\ DOMAIN ns = CLUSTERS
    \* All cluster sync states are valid values
    /\ \A c \in DOMAIN ns: ns[c] \in SyncStates

\* A Namespace is assigned to at most 1 cluster
Inv_NSAtMostOneCluster == Cardinality({\A c \in CLUSTERS: ns[c] = "Sync"}) \leq 1

\* A PVC is assigned to at most 1 cluster
Inv_PVCAtMostOneCluster == Cardinality({\A c \in CLUSTERS: pvc[c] = "Sync"}) \leq 1

\* At most one cluster thinks they can use the PVC
Inv_UsableByAtMostOne == Cardinality({c \in CLUSTERS: pvc_state[c] = "Sync"}) \leq 1

\* Statements that must be true in ALL states
Invariants ==
    /\ TypeOK
    /\ Inv_NSAtMostOneCluster
    /\ Inv_PVCAtMostOneCluster
    /\ Inv_UsableByAtMostOne
=============================================================================
\* Modification History
\* Last modified Fri Sep 16 16:07:04 EDT 2022 by jstrunk
\* Created Fri Sep 16 09:16:27 EDT 2022 by jstrunk
