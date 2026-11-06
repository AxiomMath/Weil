module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Weil.Attr

/-!
# Locally of finite type morphisms via affine opens

A morphism of schemes `f : X ⟶ Y` is locally of finite type (in the terminology of
Freitag–Kiehl, *finitely generated*) if and only if for every affine open `V ⊆ Y` and every
affine open `U ⊆ f⁻¹(V)`, the ring `Γ(U, 𝒪_X)` is a finitely generated `Γ(V, 𝒪_Y)`-algebra
via the restriction map `f.appLE V U`.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_iff_forall_affineOpens_finiteType`: the
  characterization above.

## Implementation notes

The notion of a finitely generated morphism (every point of `Y` has an affine neighbourhood
whose preimage is covered by affine opens with finitely generated section algebras) is
Mathlib's `AlgebraicGeometry.LocallyOfFiniteType`, which is defined affine-locally by
`RingHom.FiniteType`. The equivalence is then an instance of
`AlgebraicGeometry.HasRingHomProperty.iff_appLE`, whose proof in Mathlib goes through the
same gluing of finite generation over a basic open cover (`RingHom.finiteType_ofLocalizationSpan`).

## References

* [FK88] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes is locally of finite type if and only if, for every affine open
`V` of the target and every affine open `U` of the source contained in `f⁻¹(V)`, the ring
map `Γ(Y, V) ⟶ Γ(X, U)` induced by `f` is of finite type. -/
@[weil "lem_fk102_finitely_generated_affine_iff"]
theorem locallyOfFiniteType_iff_forall_affineOpens_finiteType :
    LocallyOfFiniteType f ↔
      ∀ (V : Y.affineOpens) (U : X.affineOpens) (e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens)),
        (f.appLE V U e).hom.FiniteType :=
  HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)

end AlgebraicGeometry
