# State of the Tripod Blueprint

## Mathematical target

Let

$$
G_{\mathbf Q} := \operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q),
\qquad
\widehat F_2 := \widehat{\langle x, y \rangle}
$$

where $\widehat F_2$ is the free profinite group on two generators.

The project goal is to prove:

$$
\exists\,\rho : G_{\mathbf Q} \to \operatorname{Out}(\widehat F_2)
\text{ such that } \rho \text{ is injective.}
$$

## Geometric framework

Set

$$
X := \mathbf P^1 \setminus \{0,1,\infty\}.
$$

The blueprint uses two geometric etale fundamental groups:

$$
\Pi_{\mathbf C} := \pi_1^{\mathrm{\acute et}}(X_{\mathbf C}),
\qquad
\Pi_{\overline{\mathbf Q}} := \pi_1^{\mathrm{\acute et}}(X_{\overline{\mathbf Q}}).
$$

Strictly speaking, these depend on a geometric base point; without fixing base points they are
defined only up to inner automorphism. This is compatible with the use of outer automorphism
groups throughout the project.

Planned comparison isomorphisms are:

$$
\widehat F_2 \cong \Pi_{\mathbf C},
\qquad
\Pi_{\mathbf C} \cong \Pi_{\overline{\mathbf Q}}.
$$

For any profinite-group isomorphism $e : G \cong H$, we now have a formalized transport

$$
\operatorname{Out}(G) \cong \operatorname{Out}(H)
$$

implemented as `ProfiniteGrp.outEquivOfIso` in `ToMathlib/ProfiniteGrp/Out.lean`.

## Construction of the Galois representation

The mathematical construction is organized as:

1. Define
   $$
   \rho_{\overline{\mathbf Q}} : G_{\mathbf Q} \to \operatorname{Out}(\Pi_{\overline{\mathbf Q}})
   $$
   from the exact sequence
   $$
   1 \to \Pi_{\overline{\mathbf Q}} \to \pi_1^{\mathrm{\acute et}}(X_{\mathbf Q}) \to G_{\mathbf Q} \to 1,
   $$
   where conjugation induces an outer action.
2. Transport along $\Pi_{\mathbf C} \cong \Pi_{\overline{\mathbf Q}}$ to get
   $$
   \rho_{\mathbf C} : G_{\mathbf Q} \to \operatorname{Out}(\Pi_{\mathbf C}).
   $$
3. Transport along $\widehat F_2 \cong \Pi_{\mathbf C}$ to get
   $$
   \rho : G_{\mathbf Q} \to \operatorname{Out}(\widehat F_2).
   $$

## Injectivity strategy

The injectivity proof is split into two mathematical statements:

1. (Arithmetic input) Prove injectivity of
   $$
   \rho_{\overline{\mathbf Q}} : G_{\mathbf Q} \to \operatorname{Out}(\Pi_{\overline{\mathbf Q}})
   $$
   using Belyi's theorem.
2. Transport injectivity through the two outer-automorphism isomorphisms to deduce
   $$
   \rho : G_{\mathbf Q} \to \operatorname{Out}(\widehat F_2)
   $$
   is injective.

## Current formalization status (Informalize)

From `lake exe informalize status --module Tripod`:

- Tracked declarations: **6**
- Declarations with markdown locations: **6**
- Declarations with empty locations: **0**
- Unique markdown locations: **6**

Tracked declarations correspond to the active placeholders in `Tripod.lean`.
Transport constructions and the final transport-injectivity proof are now plain Lean
code (not wrapped in Informalize-specific `formalized` syntax, which was removed in the
new Informalize release).

Main remaining mathematical gaps:

- Concrete models for $\Pi_{\mathbf C}$ and $\Pi_{\overline{\mathbf Q}}$.
- Isomorphisms $\widehat F_2 \cong \Pi_{\mathbf C}$ and $\Pi_{\mathbf C} \cong \Pi_{\overline{\mathbf Q}}$.
- Construction of $\rho_{\overline{\mathbf Q}}$ from the exact sequence.
- Belyi-based injectivity of $\rho_{\overline{\mathbf Q}}$.

## Dependency shape of the blueprint

`lake exe informalize deps --module Tripod` currently reports:

- Leaves: `geomPi1ThreePuncturedLineOverC`, `geomPi1ThreePuncturedLineOverQbar`.
- `geomPi1OverCIsoGeomPi1OverQbar` depends on both geometric placeholders.
- `freeProfiniteGroupOnTwoIsoGeomPi1OverC` depends on
  `geomPi1ThreePuncturedLineOverC`.
- `rhoQToOutGeomPi1OverQbar` depends on `geomPi1ThreePuncturedLineOverQbar`.
- `rhoQToOutGeomPi1OverQbar_injective` depends on
  `rhoQToOutGeomPi1OverQbar` and `geomPi1ThreePuncturedLineOverQbar`.

So the dependency shape still reflects the intended staged development, with transport
machinery formalized and arithmetic-geometric inputs isolated as explicit placeholders.

## Next steps

1. **Formalize the core arithmetic action over $\overline{\mathbf Q}$**
   - Refine `rhoQToOutGeomPi1OverQbar` into smaller artifacts: exact-sequence statement,
     induced outer action, and base-point-independence (up to inner automorphism).
2. **Refine the comparison isomorphisms into subgoals**
   - Split
     $$
     \widehat F_2 \cong \Pi_{\mathbf C}, \qquad \Pi_{\mathbf C} \cong \Pi_{\overline{\mathbf Q}}
     $$
     into intermediate lemmas with explicit dependencies in Informalize metadata.
3. **Develop the Belyi injectivity pipeline explicitly**
   - Introduce staged statements for faithfulness of the Galois action on finite etale covers
     (dessins perspective), then derive injectivity of
     $$
     \rho_{\overline{\mathbf Q}} : G_{\mathbf Q} \to \operatorname{Out}(\Pi_{\overline{\mathbf Q}}).
     $$
4. **Keep blueprint metadata synchronized while refining**
   - For each new placeholder declaration, add/update a matching id path in
     `informal/Tripod.md` and use `informal[Tripod....]` in Lean.
   - Re-run `informalize status`, `deps`, `decls`, and `locations` checks.
