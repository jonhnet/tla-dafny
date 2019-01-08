include "Temporal.s.dfy"

module Temporal__Lift_i {
    import opened Temporal__Temporal_s

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

    lemma InferUntil<S>(init:StatePredicate<S>, next:Action<S>,
        f:StatePredicate<S>, g:StatePredicate<S>)
        requires forall s, s' :: next(s, s') && f(s) ==> (f(s) || g(s))
        requires sat(LiftSpec(init, next))
        ensures sat(until(Lift(f), Lift(g)))
    {
    }

}
