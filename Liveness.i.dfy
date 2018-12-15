include "Temporal.s.dfy"
include "Lift.i.dfy"

module Temporal__Liveness_i {
    import opened Temporal__Temporal_s
    import opened Temporal__Lift_i

    // f happens infinitely often.
    // once g happens, it is stable until h
    // f && g ==> h
    // thus g leadsto h
    //  (because g stays true until f happens, at which point f&&g==>h.)
    lemma InferFromUntil(f:temporal, g:temporal, h:temporal)
        requires sat(always(eventually(f)))
        requires sat(always(until(g, h)))
        requires sat(always(implies(and(f, g), h)))
        ensures sat(leadsto(g, h))
    {
    }

    lemma InferInfinitelyOften(f:temporal, g:temporal)
        requires sat(always(eventually(f)))
        requires sat(leadsto(f, g))
        ensures sat(always(eventually(g)))
    {
    }
}
