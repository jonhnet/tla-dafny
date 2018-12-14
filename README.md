# tla-dafny
An embedding of TLA+ in Dafny.

# Background

The first embedding of TLA+ in Dafny appears in the
[IronFleet repository](https://github.com/Microsoft/Ironclad/tree/master/ironfleet/src). The proofs in that version float between the spec level
(state and action predicates), TLA+ expressions (temporal predicates),
and predicates over explicitly realized behaviors. The proofs often reason
by working backwards from one index in a behavior to a previous index where
another predicate was true.

My understanding of TLA+ from
[Specifying Systems](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf),
however, is that one should work as much as possible purely at the spec level,
including most of the way through safety proofs.
To finish off an invariant proof, or to build a liveness proof, one pops up
into temporal expressions such as always eventually ("infinitely often") and
leads to, stringing those together with temporal proof rules to complete
the proof. Importantly, while behaviors are implicit to the semantics of TLA+,
they're _never_ realized in practice.

# Design

The magic of TLA+ is that state, action, and temporal predicates interact
comfortably side-by-side, in a common syntax.
Every state predicate is a temporal predicate about "now", the first state
in a behavior.

To embed TLA+ into Dafny, we have to accept a compromise syntax. A tla-dafny
spec defines an explicit `State` datatype. Its state predicates take an
explicit `state` argument, and its action predicates take explicit `state`
and `state'` arguments. (These are analogous to explicit 'this' formals in
an object-oriented language.)

Temporal formulas are represented with a separate type `temporal`. Thus
one must explicitly "lift" state predicates and actions into corresponding
temporal formulas. The classic TLA+ `Spec` would be written as
```
    and(Lift(Init), always(Lift(Next)))
```
(Not really; I haven't included the explicit stutter subscript yet.)

Once in Temporal land, proofs are completed entirely with temporal formulas,
never mentioning behaviors explicily. (Behaviors do appear as the semantics
inside the library, but are not exported.)
