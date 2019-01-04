include "Temporal.s.dfy"
include "Lift.i.dfy"

module Temporal__Induction_i {
    import opened Temporal__Temporal_s
    import opened Temporal__Lift_i

    lemma InvariantByInduction_helper(init:temporal, next:temporal,
        inv:temporal, k:int)
        requires sat(init)
        requires sat(always(next))
        requires sat(implies(init, inv))
        requires sat(always(implies(and(next, inv), prime(inv))))
        requires 0 <= k
        ensures inv(k)
        //ensures forall j :: 0<=j<=k ==> 
    {
        if (0 < k) {
            InvariantByInduction_helper(init, next, inv, k-1);
            reveal_prime();
            assert implies(and(next, inv), prime(inv))(k-1);
        }
    }

    lemma InvariantByInduction(init:temporal, next:temporal, inv:temporal)
        requires sat(init)
        requires sat(always(next))
        requires sat(implies(init, inv))
        requires sat(always(implies(and(next, inv), prime(inv))))
        ensures sat(always(inv))
    {
        forall j | 0 <= j
            ensures inv(j)
        {
            InvariantByInduction_helper(init, next, inv, j);
        }
    }
    
    lemma LiftInvariant_helper<S>(init:StatePredicate<S>, next:Action<S>, inv:StatePredicate<S>, k:int)
        requires 0 <= k
        requires sat(LiftSpec(init, next));
        requires forall s :: init(s) ==> inv(s);
        requires forall s, s' :: inv(s) && next(s, s') ==> inv(s');
        ensures Lift(inv)(k);
    {
        if (0 < k) {
            LiftInvariant_helper(init, next, inv, k-1);
            assert LiftAction(next)(k-1);
            reveal_prime();
            reveal_LiftAction();
        }
    }

    lemma LiftInvariant<S>(init:StatePredicate<S>, next:Action<S>, inv:StatePredicate<S>)
        requires sat(LiftSpec(init, next));
        requires forall s :: init(s) ==> inv(s);
        requires forall s, s' :: inv(s) && next(s, s') ==> inv(s');
        ensures sat(always(Lift(inv)));
    {
        forall j | 0 <= j
            ensures Lift(inv)(j)
        {
            LiftInvariant_helper(init, next, inv, j);
        }
    }

    // TODO suprised we need this
    lemma alwaysPropagation(f:temporal, g:temporal)
        requires sat(always(f));
        requires sat(f) == sat(g);
        ensures sat(always(g));
    {
        forall j | 0 <= j
            ensures g(j)
        {
            assert f(j);
            // OH! this is the metalogical disaster! Since we can't see
            // the implicit quantifier over i, we can't actually conclude
            // that f and g are 
            assert g(j);
        }
    }
}
