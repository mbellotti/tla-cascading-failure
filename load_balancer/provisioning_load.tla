-------------------------- MODULE provisioning_load --------------------------
EXTENDS TLC, Integers, Sequences

VMs == {1,2,3}
Incidents(set) == set \X set \X set \X set
Events == [size: 1..4]

(*--algorithm provisioning
variables
	Cluster = [v \in VMs |-> 4],

define
	ServersHealthy == \E vm \in VMs: Cluster[vm] <= 9
end define;

macro trigger_event(event) begin
	Cluster[rrobin] := Cluster[rrobin] + event.size;
	if rrobin = 3 then
		rrobin := 1;
	else
		rrobin := rrobin + 1
	end if;
end macro;


process garbage_collection = "recover resources"
	variables
		Gcollection \in [1..3 -> 1..4];

	begin Collect:
		with i \in VMs do
			if Gcollection[i] >= Cluster[i] then
				Cluster[i] := 0;
			else
				Cluster[i] := Cluster[i] - Gcollection[i];
			end if;
		end with;
end process;


process incoming = "increasing resource usage"
	variables
		incident \in Incidents(Events),
		curr = "", \* helper: current event
		rrobin = 1;

	begin Increase:
		while incident /= <<>> do
			curr := Head(incident);
			incident := Tail(incident);
			trigger_event(curr);
		end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES Cluster, pc

(* define statement *)
ServersHealthy == \E vm \in VMs: Cluster[vm] <= 9

VARIABLES Gcollection, incident, curr, rrobin

vars == << Cluster, pc, Gcollection, incident, curr, rrobin >>

ProcSet == {"recover resources"} \cup {"increasing resource usage"}

Init == (* Global variables *)
        /\ Cluster = [v \in VMs |-> 4]
        (* Process garbage_collection *)
        /\ Gcollection \in [1..3 -> 1..4]
        (* Process incoming *)
        /\ incident \in Incidents(Events)
        /\ curr = ""
        /\ rrobin = 1
        /\ pc = [self \in ProcSet |-> CASE self = "recover resources" -> "Collect"
                                        [] self = "increasing resource usage" -> "Increase"]

Collect == /\ pc["recover resources"] = "Collect"
           /\ \E i \in VMs:
                IF Gcollection[i] >= Cluster[i]
                   THEN /\ Cluster' = [Cluster EXCEPT ![i] = 0]
                   ELSE /\ Cluster' = [Cluster EXCEPT ![i] = Cluster[i] - Gcollection[i]]
           /\ pc' = [pc EXCEPT !["recover resources"] = "Done"]
           /\ UNCHANGED << Gcollection, incident, curr, rrobin >>

garbage_collection == Collect

Increase == /\ pc["increasing resource usage"] = "Increase"
            /\ IF incident /= <<>>
                  THEN /\ curr' = Head(incident)
                       /\ incident' = Tail(incident)
                       /\ Cluster' = [Cluster EXCEPT ![rrobin] = Cluster[rrobin] + curr'.size]
                       /\ IF rrobin = 3
                             THEN /\ rrobin' = 1
                             ELSE /\ rrobin' = rrobin + 1
                       /\ pc' = [pc EXCEPT !["increasing resource usage"] = "Increase"]
                  ELSE /\ pc' = [pc EXCEPT !["increasing resource usage"] = "Done"]
                       /\ UNCHANGED << Cluster, incident, curr, rrobin >>
            /\ UNCHANGED Gcollection

incoming == Increase

Next == garbage_collection \/ incoming
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



==========================================================================
