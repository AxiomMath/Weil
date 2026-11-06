module

public import Weil.Defs.AlgebraicGeometry.ResidueField
public import Weil.Attr

/-!
# The residue field of a point with values in a field, as a subfield

Let `X` be a scheme and `K` a field. By `AlgebraicGeometry.Scheme.SpecToEquivOfField`, a
morphism `a : Spec K ⟶ X` is the same as its underlying point `|a| ∈ X` together with a field
embedding `κ(|a|) ⟶ K`. The image of this embedding is a subfield `κ(a) ⊆ K`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.residueFieldEmbedding`: the embedding `κ(|a|) ⟶ K` induced by
  `a : Spec K ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.residueFieldRange`: the subfield `κ(a) ⊆ K`, the image of
  `AlgebraicGeometry.Scheme.Hom.residueFieldEmbedding`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.map_comp_fromSpecResidueField_residueFieldEmbedding`:
  `a` is recovered from its embedding as `Spec κ(|a|) ⟶ X` composed with `Spec` of it.
* `AlgebraicGeometry.Scheme.Hom.residueFieldRange_SpecToEquivOfField_symm`: the point given by
  `x ∈ X` and `φ : κ(x) ⟶ K` has `κ(a)` the image of `φ`.
* `AlgebraicGeometry.Scheme.Hom.residueFieldRange_map_comp`: for a field homomorphism
  `φ : K → L`, `κ(a ∘ Spec φ) = φ(κ(a))`; in particular `κ(a ∘ Spec σ) = σ(κ(a))` for an
  automorphism `σ` of `K`.
* `AlgebraicGeometry.Scheme.Hom.residueFieldRange_comp_le`: `κ(f ∘ a) ⊆ κ(a)` for a morphism
  of schemes `f : X ⟶ Y`.

## Implementation notes

In the source, `a` ranges over the `k`-valued points of a scheme `X₀` over a finite field `κ`,
with `k` an algebraic closure of `κ`. The subfield `κ(a)` depends neither on the structure
over `κ` nor on `k` being algebraically closed, so it is defined for every morphism from the
spectrum of a field. It is a `Subfield` of `K`; when `X` lies over a field, the
`IntermediateField` it gives is recovered from the structure morphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {K L : Type u} [Field K] [Field L] {X Y : Scheme.{u}}

/-- The field embedding `κ(|a|) ⟶ K` induced by a point `a : Spec K ⟶ X` with values in a
field: the second component of `AlgebraicGeometry.Scheme.SpecToEquivOfField K X a`. -/
def residueFieldEmbedding (a : Spec (.of K) ⟶ X) :
    X.residueField a.underlyingPoint ⟶ .of K :=
  (X.SpecToEquivOfField K a).2

lemma residueFieldEmbedding_eq_SpecToEquivOfField (a : Spec (.of K) ⟶ X) :
    a.residueFieldEmbedding = (X.SpecToEquivOfField K a).2 :=
  rfl

/-- A point with values in `K` is `Spec` of its residue field embedding followed by the
canonical morphism `Spec κ(|a|) ⟶ X`. -/
@[simp]
lemma map_comp_fromSpecResidueField_residueFieldEmbedding (a : Spec (.of K) ⟶ X) :
    Spec.map a.residueFieldEmbedding ≫ X.fromSpecResidueField a.underlyingPoint = a :=
  (X.SpecToEquivOfField K).symm_apply_apply a

/-- **The residue field of a point with values in a field.** For a field `K` and a morphism
`a : Spec K ⟶ X`, the subfield `κ(a) ⊆ K` is the image of the field embedding
`κ(|a|) ⟶ K` induced by `a`. -/
@[weil "def_fk204_residue_field_of_geometric_point"]
def residueFieldRange (a : Spec (.of K) ⟶ X) : Subfield K :=
  a.residueFieldEmbedding.hom.fieldRange

lemma residueFieldRange_eq_fieldRange (a : Spec (.of K) ⟶ X) :
    a.residueFieldRange = a.residueFieldEmbedding.hom.fieldRange :=
  rfl

lemma mem_residueFieldRange {a : Spec (.of K) ⟶ X} {t : K} :
    t ∈ a.residueFieldRange ↔ ∃ s, a.residueFieldEmbedding s = t :=
  RingHom.mem_fieldRange

lemma residueFieldEmbedding_mem_residueFieldRange (a : Spec (.of K) ⟶ X)
    (s : X.residueField a.underlyingPoint) :
    a.residueFieldEmbedding s ∈ a.residueFieldRange :=
  RingHom.mem_fieldRange_self _ _

/-- The image subfield of the second component of a pair in `Σ x, κ(x) ⟶ K` only depends on
the pair. -/
private lemma fieldRange_snd_eq {s t : Σ x : X, X.residueField x ⟶ .of K} (h : s = t) :
    s.2.hom.fieldRange = t.2.hom.fieldRange := by
  subst h; rfl

/-- The point with values in `K` given by `x ∈ X` and `φ : κ(x) ⟶ K` has residue field the
image of `φ`. -/
@[simp]
lemma residueFieldRange_SpecToEquivOfField_symm (x : X) (φ : X.residueField x ⟶ .of K) :
    ((X.SpecToEquivOfField K).symm ⟨x, φ⟩).residueFieldRange = φ.hom.fieldRange := by
  have h := fieldRange_snd_eq ((X.SpecToEquivOfField K).apply_symm_apply ⟨x, φ⟩)
  exact h

@[simp]
lemma residueFieldRange_map_comp_fromSpecResidueField (x : X)
    (φ : X.residueField x ⟶ .of K) :
    (Spec.map φ ≫ X.fromSpecResidueField x).residueFieldRange = φ.hom.fieldRange :=
  residueFieldRange_SpecToEquivOfField_symm x φ

/-- Precomposing with `Spec φ` for a field homomorphism `φ : K → L` maps the residue field
by `φ`. -/
lemma residueFieldRange_map_comp (φ : CommRingCat.of K ⟶ CommRingCat.of L)
    (a : Spec (.of K) ⟶ X) :
    (Spec.map φ ≫ a).residueFieldRange = a.residueFieldRange.map φ.hom := by
  conv_lhs => rw [← a.map_comp_fromSpecResidueField_residueFieldEmbedding, ← Category.assoc,
    ← Spec.map_comp, residueFieldRange_map_comp_fromSpecResidueField]
  ext t
  simp only [RingHom.mem_fieldRange, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, Subfield.mem_map, residueFieldRange, exists_exists_eq_and]

/-- Postcomposing with a morphism of schemes shrinks the residue field. -/
lemma residueFieldRange_comp_le (a : Spec (.of K) ⟶ X) (f : X ⟶ Y) :
    (a ≫ f).residueFieldRange ≤ a.residueFieldRange := by
  conv_lhs => rw [← a.map_comp_fromSpecResidueField_residueFieldEmbedding, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, residueFieldRange_map_comp_fromSpecResidueField]
  rintro t ⟨s, rfl⟩
  exact ⟨_, rfl⟩

end Scheme.Hom

end AlgebraicGeometry
