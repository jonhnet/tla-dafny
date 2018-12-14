include "DafnyPatches.s.dfy"

module Temporal__Temporal_j {
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
} 
