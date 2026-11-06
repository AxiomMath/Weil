module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization

/-!
# The normalization of a locally Noetherian scheme

Let `X` be a locally Noetherian scheme. Every quasi-compact open `U ⊆ X` is a Noetherian
topological space, so it has only finitely many irreducible components. This is exactly the
finiteness hypothesis under which the normalization `ν : X^ν → X` of Stacks, Tag 035N, is formed:
the relative normalization of `X` in the canonical morphism `∐_η Spec κ(η) → X`, the coproduct
running over the generic points `η` of the irreducible components of `X`.

For a reduced Noetherian scheme with irreducible components `X₁, …, X_r`, this is the
normalization of Freitag–Kiehl, `X₁^ν ⊔ ⋯ ⊔ X_r^ν → X`, each `X_j^ν` being obtained by gluing the
spectra of the integral closures of `Γ(V, 𝒪_{X_j})` in the function field `κ(η_j)` of `X_j`.

## Main definitions

* `AlgebraicGeometry.Scheme.noetherianNormalizationScheme`: the normalization `X^ν` of a
  locally Noetherian scheme `X`.
* `AlgebraicGeometry.Scheme.noetherianNormalization`: the normalization morphism `ν : X^ν ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.noetherianNormalization_eq`: the normalization agrees with
  `AlgebraicGeometry.Scheme.normalization` for any proof of its finiteness hypothesis.
* `AlgebraicGeometry.normalizationOverField_eq_noetherianNormalization`: for a scheme
  locally of finite type over a field it is `AlgebraicGeometry.normalizationOverField`.
* The normalization morphism is integral, and the normalization of an integral scheme is
  integral.

## Implementation notes

The normalization is not built component by component: it is the relative normalization of `X`
in the disjoint union of the spectra of the residue fields at its generic points. Since relative
normalization takes coproducts in the source to coproducts, the summand over the generic point
`η_j` is the normalization of `X` in `Spec κ(η_j)`, which is the normalization of the reduced
irreducible component `X_j` in its function field; this is the description by integral closures
over affine opens (Stacks, Tag 035Q). The finiteness hypothesis of
`AlgebraicGeometry.Scheme.normalization` is supplied by
`AlgebraicGeometry.finite_irreducibleComponents_of_isCompact`. The definitions are
abbreviations, definitionally equal to
`AlgebraicGeometry.Scheme.normalizationOfIsLocallyNoetherian`, so the API of
`AlgebraicGeometry.Scheme.normalization` and of Mathlib's relative normalization
`AlgebraicGeometry.Scheme.Hom.normalization` applies directly.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [R. Hartshorne, *Algebraic Geometry*, II Ex. 3.8][hartshorne1977]
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][freitagkiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- The normalization `X^ν` of a locally Noetherian scheme `X` (Stacks, Tag 035N). -/
noncomputable abbrev noetherianNormalizationScheme (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Scheme.{u} :=
  X.normalizationScheme (finite_irreducibleComponents_of_isCompact X)

/-- The normalization morphism `ν : X^ν ⟶ X` of a locally Noetherian scheme `X`
(Stacks, Tag 035N). For a reduced Noetherian scheme with irreducible components `X₁, …, X_r` it is
the morphism `X₁^ν ⊔ ⋯ ⊔ X_r^ν → X` given on `X_j^ν` by the normalization of the integral scheme
`X_j` followed by the closed immersion `X_j → X`. -/
@[weil "def_fk105_normalization"]
noncomputable abbrev noetherianNormalization (X : Scheme.{u}) [IsLocallyNoetherian X] :
    X.noetherianNormalizationScheme ⟶ X :=
  X.normalization (finite_irreducibleComponents_of_isCompact X)

/-- The normalization of a locally Noetherian scheme is `AlgebraicGeometry.Scheme.normalization`,
for any proof of the finiteness of irreducible components of its quasi-compact opens. -/
theorem noetherianNormalization_eq (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    X.noetherianNormalization = X.normalization hX :=
  rfl

/-- The normalization morphism of a locally Noetherian scheme is integral. -/
instance isIntegralHom_noetherianNormalization (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsIntegralHom X.noetherianNormalization := by
  unfold noetherianNormalization normalization
  infer_instance

/-- The normalization of an integral locally Noetherian scheme is integral. -/
instance isIntegral_noetherianNormalizationScheme (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsIntegral X] : IsIntegral X.noetherianNormalizationScheme :=
  isIntegral_normalizationScheme X _

end Scheme

/-- For a scheme locally of finite type over a field, the normalization of the underlying locally
Noetherian scheme is `AlgebraicGeometry.normalizationOverField`. -/
theorem normalizationOverField_eq_noetherianNormalization
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    normalizationOverField k p = X.noetherianNormalization :=
  rfl

end AlgebraicGeometry
