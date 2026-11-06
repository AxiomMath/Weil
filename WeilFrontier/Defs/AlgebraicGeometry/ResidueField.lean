module

public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# The underlying point of a point with values in a field

Let `X` be a scheme and `K` a field. A morphism `a : Spec K ⟶ X` (a `K`-valued point of `X`)
has an underlying point `|a| ∈ X`, the image of the unique point of `Spec K`. By
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, `a` is the same as the point `|a|` together with
an embedding `κ(|a|) ⟶ K` of its residue field, and `|a|` is the first component of this pair.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.underlyingPoint`: the underlying point `|a|` of a morphism
  `a : Spec K ⟶ X` from the spectrum of a field.

## Main results

* `AlgebraicGeometry.Scheme.Hom.underlyingPoint_eq_apply`: `|a|` is the image under `a` of any
  point of `Spec K`.
* `AlgebraicGeometry.Scheme.Hom.underlyingPoint_comp`: `|a ≫ f| = f |a|`.
* `AlgebraicGeometry.Scheme.Hom.underlyingPoint_map_comp`: `|Spec φ ≫ a| = |a|` for a field
  homomorphism `φ`; in particular `|a ∘ Spec ρ| = |a|` for an automorphism `ρ` of `K`.
* `AlgebraicGeometry.Scheme.Hom.underlyingPoint_SpecToEquivOfField_symm`: the point with values
  in `K` given by `x ∈ X` and an embedding `κ(x) ⟶ K` has underlying point `x`.
* `AlgebraicGeometry.GeometricPoint.point_eq_underlyingPoint`: for a geometric point this is
  `AlgebraicGeometry.GeometricPoint.point`.

## Implementation notes

In the source, `a` ranges over the `k`-valued points of a scheme `X₀` over a field `κ`, that is
over `κ`-morphisms `Spec k ⟶ X₀`, with `k` an algebraic closure of `κ`. The underlying point
does not depend on the structure over `κ` nor on `k` being algebraically closed, so it is
defined for every morphism from the spectrum of a field.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {K L : Type u} [Field K] [Field L] {X Y : Scheme.{u}}

/-- **The underlying point of a point with values in a field.** For a field `K` and a morphism
`a : Spec K ⟶ X`, the point `|a| ∈ X` is the image of the unique point of `Spec K`; it is the
first component of `AlgebraicGeometry.Scheme.SpecToEquivOfField K X a`. -/
@[weil "def_fk204_underlying_closed_point"]
def underlyingPoint (a : Spec (.of K) ⟶ X) : X :=
  (X.SpecToEquivOfField K a).1

lemma underlyingPoint_eq_SpecToEquivOfField (a : Spec (.of K) ⟶ X) :
    a.underlyingPoint = (X.SpecToEquivOfField K a).1 :=
  rfl

lemma underlyingPoint_eq_closedPoint (a : Spec (.of K) ⟶ X) :
    a.underlyingPoint = a (closedPoint K) :=
  rfl

/-- `|a|` is the image under `a` of any point of `Spec K`. -/
lemma underlyingPoint_eq_apply (a : Spec (.of K) ⟶ X) (t : Spec (.of K)) :
    a.underlyingPoint = a t := by
  rw [underlyingPoint_eq_closedPoint]
  congr 1
  exact Subsingleton.elim _ _

/-- The point `|a|` is the only point in the range of `a`. -/
lemma range_eq_singleton_underlyingPoint (a : Spec (.of K) ⟶ X) :
    Set.range a = {a.underlyingPoint} := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact (a.underlyingPoint_eq_apply t).symm
  · rintro rfl
    exact ⟨closedPoint K, rfl⟩

@[simp]
lemma underlyingPoint_comp (a : Spec (.of K) ⟶ X) (f : X ⟶ Y) :
    (a ≫ f).underlyingPoint = f a.underlyingPoint :=
  rfl

/-- Precomposing with the morphism of spectra induced by a field homomorphism does not change
the underlying point. -/
@[simp]
lemma underlyingPoint_map_comp (φ : CommRingCat.of K ⟶ CommRingCat.of L)
    (a : Spec (.of K) ⟶ X) :
    (Spec.map φ ≫ a).underlyingPoint = a.underlyingPoint := by
  rw [underlyingPoint_comp, underlyingPoint_eq_closedPoint, underlyingPoint_eq_apply a]

/-- The point with values in `K` given by `x ∈ X` and an embedding `κ(x) ⟶ K` lies over `x`. -/
@[simp]
lemma underlyingPoint_SpecToEquivOfField_symm (x : X) (φ : X.residueField x ⟶ .of K) :
    ((X.SpecToEquivOfField K).symm ⟨x, φ⟩).underlyingPoint = x :=
  congrArg Sigma.fst ((X.SpecToEquivOfField K).apply_symm_apply ⟨x, φ⟩)

@[simp]
lemma underlyingPoint_map_comp_fromSpecResidueField (x : X) (φ : X.residueField x ⟶ .of K) :
    (Spec.map φ ≫ X.fromSpecResidueField x).underlyingPoint = x :=
  underlyingPoint_SpecToEquivOfField_symm x φ

@[simp]
lemma underlyingPoint_fromSpecResidueField (x : X) :
    (X.fromSpecResidueField x).underlyingPoint = x :=
  Scheme.fromSpecResidueField_apply x _

/-- A point with values in `K` factors through the spectrum of the residue field of its
underlying point. -/
lemma exists_eq_map_comp_fromSpecResidueField (a : Spec (.of K) ⟶ X) :
    ∃ φ : X.residueField a.underlyingPoint ⟶ .of K,
      Spec.map φ ≫ X.fromSpecResidueField a.underlyingPoint = a :=
  ⟨(X.SpecToEquivOfField K a).2, (X.SpecToEquivOfField K).symm_apply_apply a⟩

/-- Every point of `X` whose residue field embeds into `K` is the underlying point of a point
with values in `K`. -/
lemma exists_underlyingPoint_eq (x : X) (φ : X.residueField x ⟶ .of K) :
    ∃ a : Spec (.of K) ⟶ X, a.underlyingPoint = x :=
  ⟨_, underlyingPoint_SpecToEquivOfField_symm x φ⟩

end Scheme.Hom

namespace GeometricPoint

variable {S : Scheme.{u}}

/-- The underlying point of a geometric point is the underlying point of its morphism. -/
lemma point_eq_underlyingPoint (s : GeometricPoint S) : s.point = s.hom.underlyingPoint :=
  rfl

end GeometricPoint

end AlgebraicGeometry
