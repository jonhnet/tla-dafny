include "Temporal.s.dfy"
include "Lift.i.dfy"

module Temporal__Liveness_i {
    import opened Temporal__Temporal_s
    import opened Temporal__Lift_i

/*
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
        // I don't know if this proof rule is actually right. I should
        // probably read the inference rules in Specifying Systems...
    }

    lemma InferInfinitelyOften(f:temporal, g:temporal)
        requires sat(always(eventually(f)))
        requires sat(leadsto(f, g))
        ensures sat(always(eventually(g)))
    {
        // I don't know if this proof rule is actually right. I should
        // probably read the inference rules in Specifying Systems...
    }
*/

    lemma InferLeadsTo(f:temporal, g:temporal)
        requires sat(WF(f))
        requires sat(until(f, g))
        ensures sat(leadsto(f, g))
    {
        assert sat(always(implies(f, eventually(g))));
    }

    lemma LeadsToInduction(f:temporal, g:temporal, h:temporal)
        requires sat(leadsto(f, g));
        requires sat(leadsto(g, h));
        ensures sat(leadsto(f, h));
    {
        reveal_eventually();
        assert sat(always(implies(f, eventually(g))));

        forall j | 0 <= j
            ensures implies(f, eventually(h))(j)
        {
            // Unpack the implies
            if f(j) {
                // Chain the eventually witnesses together
                assert implies(f, eventually(g))(j);
                var k :| j <= k && g(k);
                assert implies(g, eventually(h))(k);
            }
        }
    }

    lemma AllRoadsLeadTo<T(!new)>(r: QuantifierConstraint<T>,
        f: QuantifiedTemporal<T>, g: temporal)
        requires sat(Exists(r, f))
        requires sat(Forall(r, t => leadsto(f(t), g)))
        ensures sat(always(eventually(g)))
    {
        reveal_eventually();
        reveal_Exists();

        forall j | 0 <= j
            ensures eventually(g)(j)
        {
            // Find the t that we need at time j to get f(t).
            var t :| r(t) && f(t)(j);
            // Then chain f(t) over to eventually-g.
            assert implies(f(t), eventually(g))(j);
        }
    }
}
