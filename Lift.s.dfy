include "Temporal.j.dfy"

module Temporal__Lift_j {
    import opened Temporal__Temporal_j

    type StatePredicate<!S> = S -> bool
    type Action<!S> = (S,S) -> bool

    type Behavior<S> = int -> S

    function{:axiom} ambientBehavior<S>() : Behavior<S>

    function Lift<S>(p: StatePredicate<S>) : temporal
    {
        i => p(ambientBehavior()(i))
    }

    function{:opaque} LiftAction<S>(a: Action<S>) : temporal
    {
        var b := ambientBehavior();
        i => a(b(i), b(i+1))
    }

    function LiftSpec<S>(init:StatePredicate<S>, next:Action<S>) : temporal
    {
        and(Lift(init), always(LiftAction(next)))
    }

    lemma InferAlways<S>(action:Action<S>)
        requires forall s, s' :: action(s, s')
        ensures sat(always(LiftAction(action)))
    {
        reveal_LiftAction();
    }
}
