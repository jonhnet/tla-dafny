include "Lift.i.dfy"
include "Induction.i.dfy"
include "DafnyPatches.s.dfy"
include "Liveness.i.dfy"

module Jon__leasedCounter_i {
import opened Temporal__Temporal_s
import opened Temporal__Lift_i
import opened Temporal__Induction_i
import opened Temporal__Liveness_i
import opened DafnyPatches_s

datatype Node = Node(count:int, lease:bool, waiting:bool)

datatype System = System(n:seq<Node>)

predicate Init(s:System) {
    && (forall i :: 0<=i<|s.n| ==> (s.n[i] == Node(0, i==0, i==0)))
    && 0<|s.n|
}

datatype Step = AppRequestStep(i: int) | IncrementStep(i: int) | GrantStep(i: int, j: int)

predicate AppRequest(s:System, s':System, i:int) {
    && 0 <= i < |s.n|
    && |s'.n| == |s.n|
    && !s.n[i].waiting
    && (forall j :: 0<=j<|s'.n| && j!=i ==> s'.n[j]==s.n[j])
    && s'.n[i].count == s.n[i].count
    && s'.n[i].lease == s.n[i].lease
    && s'.n[i].waiting == true
}

predicate Waiting(s:System, i:int) {
    && 0 <= i < |s.n|
    && s.n[i].waiting
}

predicate Increment(s:System, s':System, i:int) {
    && 0 <= i < |s.n|
    && s.n[i].lease
    && |s'.n| == |s.n|
    && s.n[i].waiting
    && (forall j :: 0<=j<|s'.n| && j!=i ==> s'.n[j]==s.n[j])
    && s'.n[i].count == s.n[i].count + 1
    && s'.n[i].lease == s.n[i].lease
    && s'.n[i].waiting == false
}

predicate Grant(s:System, s':System, i:int, j:int) {
    && 0 <= i < |s.n|
    && 0 <= j < |s.n|
    && i != j
    && s.n[i].lease
    && !s.n[i].waiting
    && |s'.n| == |s.n|
    && (forall k :: 0<=k<|s'.n| && k!=i && k!=j ==> s'.n[k]==s.n[k])
    && s'.n[i].lease == false
    && s'.n[j].lease == true

    && s'.n[j].count == s.n[i].count

    && s'.n[i].waiting == s.n[i].waiting    // ==false
    && s'.n[j].waiting == s.n[j].waiting
}

predicate Next(s:System, s':System) {
    exists step :: NextStep(s, s', step)
}

predicate NextStep(s:System, s':System, step: Step) {
    match step
        case AppRequestStep(i) => AppRequest(s, s', i)
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
        case AppRequestStep(j) => {
            assert OneNodeHoldsLease(s', i);
        }
        case IncrementStep(j) => {
            assert OneNodeHoldsLease(s', j);
        }
        case GrantStep(j, k) => {
            assert OneNodeHoldsLease(s', k);
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
            case AppRequestStep(k) => {
                reveal_LeaseHolders();
                var hs := LeaseHolders(s);
                var i :| i in hs;
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

function WaitingAt(i: int) : StatePredicate<System>
{
    s => Waiting(s, i)
}

function IncrementAt(i: int) : Action<System>
{
    (s,s') => Increment(s, s', i)
}

function LeaseAt(i: int) : StatePredicate<System>
{
    (s:System) => 0<=i<|s.n| && s.n[i].lease
}

lemma LeaseAtRotation(i: int, j: int)
    requires sat(Spec())
    ensures sat(leadsto(Lift(LeaseAt(i)), Lift(LeaseAt(j))));
{
    assume false;   // TODO
}

lemma LeaseEverywhere(i: int)
    requires sat(Spec())
    ensures sat(always(eventually(Lift(LeaseAt(i)))))
{
    assume false;   // TODO
}

lemma WaitingUntilIncrement(i: int)
    requires sat(Spec())
    ensures sat(always(until(Lift(WaitingAt(i)), LiftAction(IncrementAt(i)))));
{
    forall s, s' | Next(s, s') && WaitingAt(i)(s) && LeaseAt(i)(s)
        ensures IncrementAt(i)(s, s')
    {
        assert Next(s, s');
        var step :| NextStep(s, s', step);
        match step
            case AppRequestStep(j) => {
                assert AppRequest(s, s', j);
                assert false;
            }
            case IncrementStep(j) => {
                assert IncrementAt(i)(s, s');
            }
            case GrantStep(j, k) => {
                assert false;
            }
    }
    var WaitingImpliesIncrement :=
        (s, s') => WaitingAt(i)(s) ==> IncrementAt(i)(s, s');
    InferAlways(WaitingImpliesIncrement);
    assert sat(always(LiftAction(WaitingImpliesIncrement)));
    assert sat(always(until(Lift(WaitingAt(i)), LiftAction(IncrementAt(i)))));
}

lemma IncrementBeforeGrant(i: int)
    ensures sat(always(implies(and(Lift(WaitingAt(i)), Lift(WaitingAt(i))),
        LiftAction(IncrementAt(i)))));
{
    var action := (s, s') =>
        WaitingAt(i)(s) && WaitingAt(i)(s) ==> IncrementAt(i)(s, s');
    assert forall s, s' :: action(s, s');
    InferAlways(action);
    assert sat(always(LiftAction(action)));
    calc {
        sat(LiftAction(action));
        sat(implies(and(Lift(WaitingAt(i)), Lift(WaitingAt(i))),
            LiftAction(IncrementAt(i))));
    }
    assert sat(always(implies(and(Lift(WaitingAt(i)), Lift(WaitingAt(i))),
        LiftAction(IncrementAt(i)))));
}

lemma InferIncrementIsFair(i: int)
    requires sat(Spec())
    ensures sat(implies(
        always(eventually(Lift(WaitingAt(i)))),
        always(eventually(LiftAction(IncrementAt(i))))
        ));
{
    if (sat(always(eventually(Lift(WaitingAt(i)))))) {
        WaitingUntilIncrement(i);
        assert sat(
            always(until(Lift(WaitingAt(i)), LiftAction(IncrementAt(i)))));
        LeaseEverywhere(i);
        assert sat(
            always(eventually(Lift(LeaseAt(i)))));
        IncrementBeforeGrant(i);
        assert sat(always(implies(and(Lift(WaitingAt(i)), Lift(WaitingAt(i))),
            LiftAction(IncrementAt(i)))));
        InferFromUntil(Lift(WaitingAt(i)),
            Lift(WaitingAt(i)), LiftAction(IncrementAt(i)));
        assert sat(leadsto(Lift(WaitingAt(i)), LiftAction(IncrementAt(i))));
        InferInfinitelyOften(Lift(WaitingAt(i)), LiftAction(IncrementAt(i)));
        assert sat(
             always(eventually(LiftAction(IncrementAt(i)))));
    }
}


}
