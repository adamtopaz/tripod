# Tripod.step4.rhoQToOutGeomPi1OverQbarInjective

The outer Galois representation
`rho : Gal(Qbar/Q) ->* Out(pi_1(X_{Qbar}))` is injective.

The proof uses Belyi's theorem: every algebraic curve defined over `Qbar`
admits a Belyi map to `P^1 \ {0,1,infinity}`, so the action of `Gal(Qbar/Q)`
on the etale fundamental group of the tripod determines the action on all
algebraic curves over `Qbar`. If `sigma` acts trivially on
`Out(pi_1(X_{Qbar}))`, then `sigma` acts trivially on the function fields of
all curves over `Qbar`, forcing `sigma = 1`.
