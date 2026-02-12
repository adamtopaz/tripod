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

From the current `Tripod` blueprint metadata:

- Total entries: **9**
- Informal entries: **6**
- Formalized entries: **3**
- Progress: **33%**

Already formalized in `Tripod.lean`:

- Transport $\rho_{\overline{\mathbf Q}} \mapsto \rho_{\mathbf C}$.
- Transport $\rho_{\mathbf C} \mapsto \rho$.
- Deduction of injectivity of $\rho$ from injectivity of $\rho_{\overline{\mathbf Q}}$.

Still informal (main mathematical gaps):

- Concrete models for $\Pi_{\mathbf C}$ and $\Pi_{\overline{\mathbf Q}}$.
- Isomorphisms $\widehat F_2 \cong \Pi_{\mathbf C}$ and $\Pi_{\mathbf C} \cong \Pi_{\overline{\mathbf Q}}$.
- Construction of $\rho_{\overline{\mathbf Q}}$ from the exact sequence.
- Belyi-based injectivity of $\rho_{\overline{\mathbf Q}}$.

## Dependency shape of the blueprint

The dependency graph matches the intended mathematics:

- $\rho_{\mathbf C}$ depends on $\rho_{\overline{\mathbf Q}}$ and the comparison
  $\Pi_{\mathbf C} \cong \Pi_{\overline{\mathbf Q}}$.
- $\rho$ depends on $\rho_{\mathbf C}$ and
  $\widehat F_2 \cong \Pi_{\mathbf C}$.
- Injectivity of $\rho$ depends on injectivity of $\rho_{\overline{\mathbf Q}}$.

So the project is currently in a consistent staged state: transport machinery is formalized,
while the deepest arithmetic-geometric inputs remain explicitly isolated as informal goals.

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
   - For each new declaration, add `{DeclName}` dependencies and matching `docs/` markers,
     and re-run `informalize status`, `deps`, `lint`, and `blueprint` checks.
