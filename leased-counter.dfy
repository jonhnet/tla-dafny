include "Lift.j.dfy"
include "Induction.j.dfy"
include "DafnyPatches.s.dfy"

module Jon__leasedCounter_i {
import opened Temporal__Temporal_j
import opened Temporal__Lift_j
import opened Temporal__Induction_j
import opened DafnyPatches_s

datatype Node = Node(count:int, lease:bool, active:bool)

datatype System = System(n:seq<Node>)

predicate Init(s:System) {
    && (forall i :: 0<=i<|s.n| ==> (s.n[i] == Node(0, i==0, i==0)))
    && 0<|s.n|
}

datatype Step = IncrementStep(i: int) | GrantStep(i: int, j: int)

predicate AppActivity(s:System, s':System, i:int) {
    && 0 <= i < |s.n|
    && |s'.n| == |s.n|
    && (forall j :: 0<=j<|s'.n| && j!=i ==> s'.n[j]==s.n[j])
    && s'.n[i].count == s.n[i].count
    && s'.n[i].lease == s.n[i].lease
    && s'.n[i].active == true
}

predicate Waiting(s:System, i:int) {
    && 0 <= i < |s.n|
    && s.n[i].active
}

predicate Increment(s:System, s':System, i:int) {
    && 0 <= i < |s.n|
    && s.n[i].lease
    && |s'.n| == |s.n|
    && (forall j :: 0<=j<|s'.n| && j!=i ==> s'.n[j]==s.n[j])
    && s'.n[i].count == s.n[i].count + 1
    && s'.n[i].lease == s.n[i].lease
    && s'.n[i].active == false
}

predicate Grant(s:System, s':System, i:int, j:int) {
    && 0 <= i < |s.n|
    && 0 <= j < |s.n|
    && i != j
    && s.n[i].lease
    && |s'.n| == |s.n|
    && (forall k :: 0<=k<|s'.n| && k!=i && k!=j ==> s'.n[k]==s.n[k])
    && s'.n[i].lease == false
    && s'.n[j].lease == true

    && s'.n[j].count == s.n[i].count

    && s'.n[i].active == false
    && s'.n[j].active == true
}

predicate Next(s:System, s':System) {
    exists step :: NextStep(s, s', step)
}

predicate NextStep(s:System, s':System, step: Step) {
    match step
        case IncrementStep(i) => Increment(s, s', i)
        case GrantStep(i, j) => Grant(s, s', i, j)
}

////////////////////////////////////////
// A safety proof.
////////////////////////////////////////

predicate OneNodeHoldsLease(s: System, i: int)
{
    && 0<=i<|s.n|
    && s.n[i].lease
    && (forall j :: 0<=j<|s.n| && j!=i ==> !s.n[j].lease)
}

predicate ExactlyOneLease(s: System) 
{
    exists i :: OneNodeHoldsLease(s, i)
}

lemma lemmaExactlyOneLeaseInit(s: System)
    requires Init(s);
    ensures ExactlyOneLease(s);
{
    assert OneNodeHoldsLease(s, 0);
}


lemma lemmaExactlyOneLeaseNext(s: System, s': System, step: Step)
    requires NextStep(s, s', step);
    requires ExactlyOneLease(s);
    ensures ExactlyOneLease(s');
{
    var i :| OneNodeHoldsLease(s, i);
    match step
        case IncrementStep(i) => {
            assert OneNodeHoldsLease(s', i);
        }
        case GrantStep(i, j) => {
            assert OneNodeHoldsLease(s', j);
        }
}

////////////////////////////////////////
// A safety proof
////////////////////////////////////////

function Spec() : temporal {
    LiftSpec(Init, Next)
}

function{:opaque} LeaseHolders(s: System) : set<int>
{
    set i | 0<=i<|s.n| && s.n[i].lease
}

predicate Inv(s: System)
{
    |LeaseHolders(s)| == 1
}

function LeaseHolder(s: System) : (h:int)
    requires Inv(s)
    ensures LeaseHolders(s) == {h}
{
    var hs := LeaseHolders(s);
    var h :| h in hs;
    singletonExtensionality(h, hs);
    assert |hs| == 1;
    assert h in hs;
    assert hs == {h};
    h
}

lemma InferAlwaysInv()
    requires sat(Spec())
    ensures sat(always(Lift(Inv)))
{
    // Prove the base case in ordinary predicate logic.
    forall s | Init(s)
        ensures Inv(s)
    {
        reveal_LeaseHolders();
        assert LeaseHolders(s) == {0};
    }

    // Prove the base case in ordinary action (state-pair) logic.
    forall s, s' | Next(s, s') && Inv(s)
        ensures Inv(s')
    {
        var holder := LeaseHolder(s);
        var step :| NextStep(s, s', step);
        match step
            case IncrementStep(i) => {
                reveal_LeaseHolders();
                forall j | j!=i
                    ensures !(j in LeaseHolders(s'))
                {
                    if j in LeaseHolders(s') {
                        assert {i,j} <= LeaseHolders(s);
                    }
                }
                assert LeaseHolders(s') == {i};
                assert Inv(s');
            }
            case GrantStep(i, j) => {
                reveal_LeaseHolders();
                forall k | k!=j
                    ensures !(k in LeaseHolders(s'))
                {
                    if k in LeaseHolders(s') {
                        assert {i,k} <= LeaseHolders(s);
                    }
                }
                assert LeaseHolders(s') == {j};
                assert Inv(s');
            }
    }

    // Lift those proofs into the temporal logic expression.
    LiftInvariant(Init, Next, Inv);
}

////////////////////////////////////////
// A liveness property
////////////////////////////////////////

function WaitingAtClient(i: int) : StatePredicate<System>
{
    s => Waiting(s, i)
}

function IncrementAtClient(i: int) : Action<System>
{
    (s,s') => Increment(s, s', i)
}

lemma 

lemma LeaseAtRotation(i: int, j: int)
    requires sat(Spec())
    ensures sat(leadsto(LeaseAt(i), LeaseAt(j)));
{
}

lemma LeaseAtLeadsToIncrement(i: int)
    requires sat(Spec())
    ensures sat(leadsto(and(LeaseAt(i), WaitingAtClient(i)), IncrementAtClient(i)));
{
}

lemma InferIncrementIsFair(i: int)
    requires sat(Spec())
    ensures sat(implies(
        always(eventually(Lift(WaitingAtClient(i)))),
        always(eventually(LiftAction(IncrementAtClient(i))))
        ));
{
    if (sat(always(eventually(Lift(WaitingAtClient(i)))))) {
        assert sat(always(eventually(LiftAction(IncrementAtClient(i)))));
    }
}

// prove forall i always eventually Waiting(i) ==> always eventually Count(i)
// What is want I? I guess a ready action.

}
