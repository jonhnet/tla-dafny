module DafnyPatches_s {

lemma setSizeRelation<T>(a:set<T>, b:set<T>)
    requires a <= b;
    ensures |a| <= |b|;
{
    assume false;
}

lemma singletonExtensionality<T>(t:T, s:set<T>)
    requires t in s
    requires |s| == 1
    ensures s == {t}
{
    var v := {t};
    forall u: T
        ensures (u in s) == (u in v);
    {
        if (u != t) {
            if (u in s) {
                setSizeRelation({t,u}, s);
            }
        }
    }
}

lemma functionExtensionality<T,U>(f:T->U, g:T->U)
    requires forall t :: f(t) == g(t)
    ensures f == g
{
    assume false;
}

lemma notExists<T>(P : T -> bool)
    ensures !(forall j :: !P(j)) == exists j :: P(j);
{
}

}
