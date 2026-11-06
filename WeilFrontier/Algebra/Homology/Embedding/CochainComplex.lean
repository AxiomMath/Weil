module

public import Weil.Attr
public import WeilFrontier.Defs.Algebra.Homology.Embedding.CochainComplex

/-!
# Cohomology of the cokernel of the canonical truncation

Let `K` be a cochain complex in an abelian category and `m : ℤ`. The complex
`K.truncLECokernel m = ⋯ → 0 → Kᵐ / Ker dᵐ → K^{m+1} → ⋯` has vanishing cohomology in all
degrees `ν < m + 1`: below `m` its terms are zero, and in degree `m` the differential induced by
`dᵐ` on `Kᵐ / Ker dᵐ` is injective.

## Main results

* `CochainComplex.exactAt_truncLECokernel`: `K.truncLECokernel m` is exact in degrees `ν < m + 1`.
* `CochainComplex.isZero_homology_truncLECokernel`: `Hᵛ(K.truncLECokernel m) = 0` for `ν < m + 1`.
* The instance `(K.truncLECokernel m).IsGE (m + 1)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], App. A, §2
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ) (m : ℤ)

/-- `K.truncLECokernel m` is exact in every degree `ν < m + 1`. -/
lemma exactAt_truncLECokernel (ν : ℤ) (hν : ν < m + 1) : (K.truncLECokernel m).ExactAt ν := by
  obtain hν | rfl : ν < m ∨ ν = m := by lia
  · exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_truncLECokernel_X m ν hν)
  · rw [HomologicalComplex.exactAt_iff' _ (ν - 1) ν (ν + 1) (by simp) (by simp)]
    have := K.mono_truncLECokernel_d ν
    exact (ShortComplex.exact_iff_mono _
      (IsZero.eq_of_src (K.isZero_truncLECokernel_X ν (ν - 1) (by lia)) _ _)).2 this

instance isGE_truncLECokernel : (K.truncLECokernel m).IsGE (m + 1) := by
  rw [isGE_iff]
  intro ν hν
  exact K.exactAt_truncLECokernel m ν hν

/-- The cohomology of `K.truncLECokernel m` vanishes in every degree `ν < m + 1`. -/
@[weil "lem_fka2_truncation_cokernel_cohomology"]
lemma isZero_homology_truncLECokernel (ν : ℤ) (hν : ν < m + 1) :
    IsZero ((K.truncLECokernel m).homology ν) :=
  (K.exactAt_truncLECokernel m ν hν).isZero_homology

end CochainComplex
