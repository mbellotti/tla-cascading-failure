-------------------------- MODULE provisioning_naive --------------------------
EXTENDS TLC, Integers, Sequences

VMs == {"Server1","Server2","Server3"}
Incidents(set) == set \X set \X set \X set
Events == [target: VMs, size: 0..4]

(*--algorithm provisioning
variables
	incident \in Incidents(Events),
	Cluster = [v \in VMs |-> 4],
	curr = ""; \* helper: current event

define
	ServersHealthy == \A vm \in VMs: Cluster[vm] <= 9
end define;

macro trigger_event(event) begin
	Cluster[event.target] := Cluster[event.target] + event.size
end macro;


begin
	while incident /= <<>> do
		curr := Head(incident);
		incident := Tail(incident);
		trigger_event(curr)
	end while;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES incident, Cluster, curr, pc

(* define statement *)
ServersHealthy == \A vm \in VMs: Cluster[vm] <= 9


vars == << incident, Cluster, curr, pc >>

Init == (* Global variables *)
        /\ incident \in Incidents(Events)
        /\ Cluster = [v \in VMs |-> 4]
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF incident /= <<>>
               THEN /\ curr' = Head(incident)
                    /\ incident' = Tail(incident)
                    /\ Cluster' = [Cluster EXCEPT ![curr'.target] = Cluster[curr'.target] + curr'.size]
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << incident, Cluster, curr >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

==========================================================================
