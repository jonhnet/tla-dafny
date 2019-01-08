include "Lift.i.dfy"
include "Induction.i.dfy"
include "DafnyPatches.s.dfy"
include "Liveness.i.dfy"


module Jon__simplest_liveness_i {
import opened Temporal__Temporal_s
import opened Temporal__Lift_i
import opened Temporal__Induction_i
import opened Temporal__Liveness_i
import opened DafnyPatches_s

function systemSize() : nat // CONSTANT
    ensures 0 < systemSize()
    // axiom

datatype System = System(owner:int)

predicate Grant(s:System, s':System) {
    s'.owner == (s.owner + 1) % systemSize()
}

predicate Init(s:System) {
    s.owner == 0
}

predicate Next(s:System, s':System) {
    Grant(s, s')
}

function Spec() : temporal {
    LiftSpec(Init, Next)
}


predicate Owner(s:System, i:int) {
    s.owner == i
}

function OwnerAt(i:int) : StatePredicate<System> {
    (s:System) => Owner(s, i)
}

lemma FairnessAxioms()
    ensures forall i :: 0<=i<systemSize() ==> sat(WF(LiftAction(Grant)))
// AXIOM

lemma OwnOneHop(i: int)
    requires sat(Spec())
    requires 0 <= i < systemSize() - 1
    ensures sat(leadsto(Lift(OwnerAt(i)), Lift(OwnerAt(i+1))))
{
    var f := Lift(OwnerAt(i));
    var g := Lift(OwnerAt(i+1));
    InferUntil(Init, Next, OwnerAt(i), OwnerAt(i+1));
    assert sat(until(f, g));
    FairnessAxioms();
    assert sat(WF(f));  // Yeah, how do we get from OwnerAt(i) to LiftAction(Grant)?
    InferLeadsTo(f, g);
}

lemma OwnWrap()
    requires sat(Spec())
    ensures sat(leadsto(Lift(OwnerAt(systemSize() - 1)), Lift(OwnerAt(0))))
{
}

lemma OwnInduction(i: int, j: int)
    requires sat(Spec())
    requires 0 <= i < systemSize();
    requires 0 <= j < systemSize();
    ensures sat(leadsto(Lift(OwnerAt(i)), Lift(OwnerAt(j))))
    decreases systemSize() + j - i;
{
    if i==j {
    } else if (i < j) {
        OwnInduction(i, j-1);
        OwnOneHop(j-1);
        LeadsToInduction(Lift(OwnerAt(i)), Lift(OwnerAt(j-1)), Lift(OwnerAt(j)));
    } else {
        // i > j: need to wrap.
        OwnInduction(i, systemSize()-1);
        OwnWrap();
        OwnInduction(0, j);
        LeadsToInduction(Lift(OwnerAt(i)), Lift(OwnerAt(systemSize() - 1)), Lift(OwnerAt(0)));
        LeadsToInduction(Lift(OwnerAt(i)), Lift(OwnerAt(0)), Lift(OwnerAt(j)));
    }
}

lemma OwnForall(j: int)
    requires sat(Spec())
    requires 0 <= j < systemSize();
    //ensures forall i :: 0 <= i < systemSize() ==> sat(leadsto(Lift(OwnerAt(i)), Lift(OwnerAt(j))))
    ensures sat(Forall(i => 0<=i<systemSize(), i => leadsto(Lift(OwnerAt(i)), Lift(OwnerAt(j)))))
{
    forall i | 0 <= i < systemSize()
        ensures sat(leadsto(Lift(OwnerAt(i)), Lift(OwnerAt(j))))
    {
        OwnInduction(i, j);
    }
}

lemma AlwaysExistsOwner()
    requires sat(Spec())
    ensures sat(Exists(j => 0<=j<systemSize(), j => Lift(OwnerAt(j))))
{
}

lemma Liveness()
    requires sat(Spec())
    ensures forall j :: 0 <= j < systemSize() ==>
        sat(always(eventually(Lift(OwnerAt(j)))))
{
    forall j | 0 <= j < systemSize()
        ensures sat(always(eventually(Lift(OwnerAt(j)))))
    {
        AlwaysExistsOwner();
        AllRoadsLeadTo(
            i => 0 <= i < systemSize(), i => Lift(OwnerAt(i)),
            Lift(OwnerAt(j)));
    }
}

lemma AlwaysEventuallyEveryOwner(i: int)
    requires sat(Spec())
    requires 0 <= i < systemSize()
    ensures sat(always(eventually(Lift(OwnerAt(i)))))
{
    // Unpack forall from Liveness?
}

}
