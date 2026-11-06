module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Weil.Attr

/-!
# The composite of a morphism with its cone inclusion is null-homotopic

For a morphism of cochain complexes `φ : F ⟶ G` in a preadditive category, the composite
`φ ≫ inr φ : F ⟶ mappingCone φ` of `φ` with the inclusion `inr φ : G ⟶ mappingCone φ` is
homotopic to zero. A null-homotopy is given in degree `n` by the inclusion
`F^n ⟶ (mappingCone φ)^{n-1} = F^n ⊞ G^{n-1}`, `x ↦ (x, 0)`, i.e. by the cochain
`mappingCone.inl φ`. Consequently the classes satisfy `[φ] ≫ [inr φ] = 0` in the homotopy
category `K(C)`.

## Main results

* `CochainComplex.mappingCone.homotopyCompInrZero`: the homotopy `φ ≫ inr φ ∼ 0`, with
  components the cochain `inl φ`.
* `CochainComplex.mappingCone.quotient_map_comp_map_inr_eq_zero`:
  `[φ] ≫ [inr φ] = 0` in `HomotopyCategory C (ComplexShape.up ℤ)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex.mappingCone

variable {C : Type*} [Category C] [Preadditive C] {F G : CochainComplex C ℤ} (φ : F ⟶ G)
  [HomologicalComplex.HasHomotopyCofiber φ]

/-- The null-homotopy of `φ ≫ inr φ`: in degree `n` it is `(inl φ).v n (n - 1)`,
`x ↦ (x, 0) : F^n ⟶ F^n ⊞ G^{n-1}`. -/
@[weil "lem_fka2_cone_inclusion_composite_null"]
noncomputable def homotopyCompInrZero : Homotopy (φ ≫ inr φ) 0 :=
  (HomComplex.Cochain.equivHomotopy _ _).symm ⟨inl φ, by simp [δ_inl]⟩

/-- The components of `homotopyCompInrZero φ` are those of the cochain `inl φ`. -/
lemma homotopyCompInrZero_hom (p q : ℤ) (hpq : p + -1 = q) :
    (homotopyCompInrZero φ).hom p q = (inl φ).v p q hpq := by
  simp [homotopyCompInrZero, HomComplex.Cochain.equivHomotopy, hpq]

/-- `[φ] ≫ [inr φ] = 0` in the homotopy category `K(C)`. -/
@[weil "lem_fka2_cone_inclusion_composite_null"]
lemma quotient_map_comp_map_inr_eq_zero :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (inr φ) = 0 := by
  rw [← Functor.map_comp, HomotopyCategory.eq_of_homotopy _ _ (homotopyCompInrZero φ),
    Functor.map_zero]

end CochainComplex.mappingCone
