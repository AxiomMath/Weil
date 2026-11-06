module

public import Weil.Attr
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Complexes with cohomology bounded below lie in `D⁺`

Let `C` be an abelian category and `K` a cochain complex in `C` indexed by `ℤ`. If the
cohomology `Hⁱ(K)` vanishes for all `i < m`, then the image of `K` in the derived category
`D(C)` lies in the bounded below derived category `D⁺(C)`, the full subcategory
`DerivedCategory.Plus C` of objects `X` with `X.IsGE n` for some `n` in the canonical
t-structure. More precisely, the truncation map `K ⟶ τ_{≥ m} K` is a quasi-isomorphism, so `K`
is isomorphic in `D(C)` to the bounded below complex `τ_{≥ m} K`.

## Main results

* `DerivedCategory.plus_Q_obj_of_isZero_homology`: if `Hⁱ(K) = 0` for all `i < m`, then
  `Q.obj K` satisfies the property `TStructure.t.plus` defining `DerivedCategory.Plus C`.
* `DerivedCategory.exists_isStrictlyGE_iso_Q_obj_of_isZero_homology`: under the same
  hypothesis, `Q.obj K` is isomorphic to `Q.obj L` for a complex `L` with `Lⁱ = 0` for `i < m`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A cochain complex whose cohomology vanishes in all degrees `< m` is bounded below in the
derived category: its image under `Q` lies in `D⁺(C)`. -/
@[weil "lem_fka2_cohomology_bounded_below_in_dplus"]
theorem plus_Q_obj_of_isZero_homology (K : CochainComplex C ℤ) (m : ℤ)
    (hK : ∀ i < m, IsZero (K.homology i)) :
    TStructure.t.plus (Q.obj K) := by
  have : K.IsGE m := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK i hi
  exact ⟨m, inferInstance⟩

/-- A cochain complex whose cohomology vanishes in all degrees `< m` is isomorphic in the derived
category to a complex concentrated in degrees `≥ m`, namely its truncation `τ_{≥ m} K`. -/
theorem exists_isStrictlyGE_iso_Q_obj_of_isZero_homology (K : CochainComplex C ℤ) (m : ℤ)
    (hK : ∀ i < m, IsZero (K.homology i)) :
    ∃ (L : CochainComplex C ℤ) (_ : L.IsStrictlyGE m), Nonempty (Q.obj K ≅ Q.obj L) := by
  have : K.IsGE m := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK i hi
  exact ⟨K.truncGE m, inferInstance, ⟨asIso (Q.map (K.πTruncGE m))⟩⟩

end DerivedCategory
