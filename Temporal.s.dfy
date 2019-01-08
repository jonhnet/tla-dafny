include "DafnyPatches.s.dfy"

module Temporal__Temporal_s {
    import opened DafnyPatches_s

    type temporal = int -> bool

    predicate sat(x:temporal) {
        x(0)
    }
    
    function and(x:temporal, y:temporal) : temporal
    {
        i => x(i) && y(i)
    }
    
    function or(x:temporal, y:temporal) : temporal
    {
        i => x(i) || y(i)
    }

    function implies(x:temporal, y:temporal) : temporal
    {
        i => x(i) ==> y(i)
    }

    function equiv(x:temporal, y:temporal) : temporal
    {
        i => x(i) <==> y(i)
    }

    function not(x:temporal) : temporal
    {
        i => !x(i)
    }

    function{:opaque} prime(x:temporal) : temporal
    {
        i => x(i+1)
    }

    function always(x:temporal) : temporal
    {
        i => forall j :: i <= j ==> x(j)
    }

    function{:opaque} eventually(x:temporal) : temporal
    {
        i => exists j :: i <= j && x(j)
    }

    // this is the official TLA+ definition
    function tlaEventually(x:temporal) : temporal
    {
        not(always(not(x)))
    }

    lemma tlaIsEventually(x: temporal)
        ensures eventually(x) == tlaEventually(x)
    {
        reveal_eventually();
        forall i ensures eventually(x)(i) == tlaEventually(x)(i)
        {
            assert forall j :: !x(j) == not(x)(j);
        }
        functionExtensionality(eventually(x), tlaEventually(x));
    }

    // Liveness
    function leadsto(f:temporal, g:temporal) : temporal
    {
        always(implies(f, eventually(g)))
    }

    function enabled(f:temporal) : temporal
    {
        // Well, this will be tricky to write without concrete states!
        // We want to talk about a hypothetical next state, not necessarily
        // any state in the ambient behavior. Yuck.
//        i => exsits state' : f(state[i], state')
        f
    }

    // XXX This isn't really Lamport Weak Fairness yet
    // (Specifying Systems page 97), because it mentions f,
    // not <f>_v. I think the _v bit is about building modular specs,
    // or refine-able specs, so I think we can defer it for a little bit.
    function WF(f:temporal) : temporal
    {
        always(implies(always(enabled(f)), eventually(f)))
    }

    function until(f:temporal, g:temporal) : temporal
    {
        always(implies(f, or(prime(f), g)))
    }

    type QuantifierConstraint<!T> = T -> bool
    type QuantifiedTemporal<!T> = T -> temporal

    function Forall<T(!new)>(r:QuantifierConstraint<T>, f:QuantifiedTemporal<T>) : temporal
    {
        i => forall t :: r(t) ==> f(t)(i)
    }

    function {:opaque} Exists<T(!new)>(r:QuantifierConstraint<T>, f:QuantifiedTemporal<T>) : temporal
    {
        i => forall j :: i <= j ==> exists t :: r(t) && f(t)(j)
    }
} 
