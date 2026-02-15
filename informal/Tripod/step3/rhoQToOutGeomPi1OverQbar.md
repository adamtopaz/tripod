# Tripod.step3.rhoQToOutGeomPi1OverQbar

The outer Galois representation
`rho : Gal(Qbar/Q) ->* Out(pi_1(X_{Qbar}))`.

This is the outer action arising from the fundamental exact sequence
`1 -> pi_1(X_{Qbar}) -> pi_1(X_Q) -> Gal(Qbar/Q) -> 1` via the general
construction `ProfiniteGrp.GroupExtension.outerAction`: each element
`sigma in Gal(Qbar/Q)` lifts to an element of `pi_1(X_Q)`, and conjugation by
that lift gives a well-defined outer automorphism of the geometric fundamental
group.
