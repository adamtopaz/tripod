# Conventions for the Tripod Notes

These notes accompany the formal Lean development in `Tripod.lean`. On the informal side
we deliberately suppress some standard choices (geometric basepoints, compatible choices
under base change, and so on) in order to present statements in the style used in research
mathematics.

The price of this suppression is that many constructions are only canonical up to
conjugation. In practice this is handled by working with outer automorphisms.

## The Tripod

We write

`X_0 := P^1_{\mathbf Q} \setminus \{0,1,\infty\}`

for the thrice-punctured projective line over `\mathbf Q`, and for a field `k` we write

`X_k := X_0 \times_{\mathbf Q} k`.

## Geometric Basepoints and Conjugacy

A *geometric point* of a scheme `X` is a morphism `\bar x : \operatorname{Spec}(\Omega) \to X`
with `\Omega` separably closed. The etale fundamental group `\pi_1^{\mathrm{et}}(X, \bar x)`
is defined as the automorphism group of the corresponding fiber functor on the Galois
category of finite etale covers of `X`.

If `\bar x` and `\bar x'` are geometric points of a connected `X`, then there exists an
isomorphism `\pi_1^{\mathrm{et}}(X, \bar x) \cong \pi_1^{\mathrm{et}}(X, \bar x')`, but it is
not canonical: it is only well-defined up to inner automorphism of the target group.
Consequently, whenever basepoints are suppressed, any statement intended to be
basepoint-independent should be interpreted as living naturally in `\mathrm{Out}`.

Reference: SGA1, Expose V (fundamental group via fiber functors, basepoint change and
conjugacy).

## Outer Automorphisms and Basepoint-Free Statements

For a group `G`, write `\mathrm{Out}(G) := \mathrm{Aut}(G) / \mathrm{Inn}(G)`.
Passing to `\mathrm{Out}` exactly removes the ambiguity coming from basepoint change.

In particular, for a connected scheme `X` we regard `\mathrm{Out}(\pi_1^{\mathrm{et}}(X))` as
canonical even when `\pi_1^{\mathrm{et}}(X, \bar x)` depends on an (unspecified) `\bar x`.

## Outer Actions From Short Exact Sequences

Given a short exact sequence of groups

`1 \to N \to E \to Q \to 1`,

one obtains a canonical homomorphism `Q \to \mathrm{Out}(N)` as follows: for `q \in Q` choose
a lift `\tilde q \in E`, let `\tilde q` act on `N` by conjugation, and take its class in
`\mathrm{Out}(N)`. Different lifts differ by an element of `N`, hence give conjugate
automorphisms of `N`, i.e. the same class in `\mathrm{Out}(N)`.

This is the conceptual origin of the outer Galois representation attached to the
fundamental exact sequence of etale fundamental groups.

## Algebraically Closed Base Change

Let `k \to k'` be an extension of algebraically closed fields, and let `Y` be a connected
scheme of finite type over `k`. The projection `Y_{k'} \to Y` induces an isomorphism of
etale fundamental groups after choosing compatible geometric points:

`\pi_1^{\mathrm{et}}(Y_{k'}, \bar y') \cong \pi_1^{\mathrm{et}}(Y, \bar y)`.

As above, changing the geometric points conjugates the resulting isomorphism, so the
induced identification on outer automorphism groups is canonical.

Reference: SGA1, Expose X (invariance under algebraically closed base change).

## Fundamental Exact Sequence Over A Field

Let `K` be a field with separable closure `K^{\mathrm{sep}}` and let `Y/K` be geometrically
connected. After choosing a geometric point `\bar y` of `Y`, there is an exact sequence of
profinite groups

`1 \to \pi_1^{\mathrm{et}}(Y_{K^{\mathrm{sep}}}, \bar y)
   \to \pi_1^{\mathrm{et}}(Y, \bar y)
   \to \mathrm{Gal}(K^{\mathrm{sep}}/K) \to 1`.

Reference: SGA1, Expose IX, Theoreme 6.1.

## Covers, Quotients, and Dessins

Finite quotients of `\pi_1^{\mathrm{et}}(X, \bar x)` correspond to connected finite etale
Galois covers of `X`. Thus an automorphism of `\pi_1^{\mathrm{et}}(X, \bar x)` is determined
by its effect on all finite etale covers, and passing to `\mathrm{Out}` corresponds to the
basepoint-free notion of preserving these covers up to isomorphism.

For the tripod `X = P^1_{\bar{\mathbf Q}} \setminus \{0,1,\infty\}`, finite etale covers are
equivalent to dessins d'enfants. The classical theorem that
`\mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q)` acts faithfully on dessins is the arithmetic input
behind the injectivity statement in this project.
