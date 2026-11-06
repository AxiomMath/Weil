module

public import Weil.Attr
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise

/-!
# The cokernel of the canonical truncation `τ_{≤ m} K ⟶ K`

Let `K` be a cochain complex in an abelian category and `m : ℤ`. The complex
`K.truncLECokernel m` is the cokernel of the monomorphism `K.ιTruncLE m : K.truncLE m ⟶ K`.
Since `(K.truncLE m)ⁿ = Kⁿ` for `n < m`, `(K.truncLE m)ᵐ = Ker dᵐ` and `(K.truncLE m)ⁿ = 0` for
`n > m`, this complex is
`⋯ → 0 → Kᵐ / Ker dᵐ → K^{m+1} → K^{m+2} → ⋯`,
with differential induced by `dᵐ` in degree `m` and equal to `dⁿ` in degrees `n > m`.
Freitag and Kiehl describe the same complex as the cokernel of `Hᵐ(K)[-m] ⟶ τ_{≥ m} K`.

## Main definitions

* `CochainComplex.truncLECokernel K m`: the complex `Kᵐ / Ker dᵐ → K^{m+1} → ⋯`.
* `CochainComplex.toTruncLECokernel K m : K ⟶ K.truncLECokernel m`: the canonical epimorphism.

## Main results

* `CochainComplex.isZero_truncLECokernel_X`: the complex vanishes in degrees `n < m`.
* `CochainComplex.isIso_toTruncLECokernel_f`: in degrees `n > m` the canonical map is an
  isomorphism `Kⁿ ≅ (K.truncLECokernel m)ⁿ`.
* `CochainComplex.shortExact_iCycles_toTruncLECokernel_f`: in degree `m` the sequence
  `0 → Ker dᵐ → Kᵐ → (K.truncLECokernel m)ᵐ → 0` is short exact, i.e. the degree `m` term is
  `Kᵐ / Ker dᵐ`.
* `CochainComplex.mono_truncLECokernel_d`: the differential in degree `m` is a monomorphism.
* `CochainComplex.shortExact_eval_shortComplexTruncLE`: in each degree `n`, the sequence
  `0 → (τ_{≤ m} K)ⁿ → Kⁿ → (K.truncLECokernel m)ⁿ → 0` is short exact.
* `CochainComplex.iCycles_toTruncLECokernel_f`: `Ker dᵐ ⟶ Kᵐ ⟶ (K.truncLECokernel m)ᵐ` is zero.

Mathlib's `K.shortComplexTruncLEX₃ToTruncGE m (m + 1) : K.truncLECokernel m ⟶ K.truncGE (m + 1)`
is a quasi-isomorphism (an instance), so `K.truncLECokernel m` has the same cohomology as
`τ_{≥ m + 1} K`.

## Implementation notes

Rather than building the complex degree by degree, it is defined as the cokernel of
`K.ιTruncLE m`, which is the third object of Mathlib's `K.shortComplexTruncLE m`. Its terms are
then identified with the expected ones up to the canonical maps from `K`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], App. A, §2
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ) (m : ℤ)

/-- The cokernel of the canonical truncation `K.ιTruncLE m : τ_{≤ m} K ⟶ K`: the complex
`⋯ → 0 → Kᵐ / Ker dᵐ → K^{m+1} → K^{m+2} → ⋯`. -/
@[weil "def_fka2_truncation_cokernel_complex"]
noncomputable abbrev truncLECokernel : CochainComplex C ℤ :=
  (K.shortComplexTruncLE m).X₃

/-- The canonical epimorphism `K ⟶ K.truncLECokernel m`. -/
noncomputable abbrev toTruncLECokernel : K ⟶ K.truncLECokernel m :=
  (K.shortComplexTruncLE m).g

/-- In each degree, `0 → (τ_{≤ m} K)ⁿ → Kⁿ → (K.truncLECokernel m)ⁿ → 0` is short exact. -/
lemma shortExact_eval_shortComplexTruncLE (n : ℤ) :
    ((K.shortComplexTruncLE m).map (HomologicalComplex.eval C _ n)).ShortExact :=
  (K.shortComplexTruncLE_shortExact m).map_of_exact _

/-- `K.truncLECokernel m` vanishes in degrees `n < m`. -/
lemma isZero_truncLECokernel_X (n : ℤ) (hn : n < m) : IsZero ((K.truncLECokernel m).X n) := by
  have hS := K.shortExact_eval_shortComplexTruncLE m n
  have : IsIso ((K.ιTruncLE m).f n) := K.isIso_ιTruncLE_f_of_lt m n hn
  have hg : (K.toTruncLECokernel m).f n = 0 := by
    rw [← cancel_epi ((K.ιTruncLE m).f n), comp_zero, ← HomologicalComplex.comp_f]
    exact HomologicalComplex.congr_hom (K.shortComplexTruncLE m).zero n
  have : Epi ((K.toTruncLECokernel m).f n) := hS.epi_g
  exact IsZero.of_epi_eq_zero _ hg

/-- In degrees `n > m`, `K.toTruncLECokernel m` is an isomorphism `Kⁿ ≅ (K.truncLECokernel m)ⁿ`. -/
lemma isIso_toTruncLECokernel_f (n : ℤ) (hn : m < n) :
    IsIso ((K.toTruncLECokernel m).f n) := by
  have hS := K.shortExact_eval_shortComplexTruncLE m n
  have hz : IsZero ((K.truncLE m).X n) := (K.truncLE m).isZero_of_isStrictlyLE m n hn
  have : Mono ((K.toTruncLECokernel m).f n) :=
    hS.exact.mono_g (hz.eq_of_src _ _)
  have : Epi ((K.toTruncLECokernel m).f n) := hS.epi_g
  exact isIso_of_mono_of_epi _

/-- The differential of `K.truncLECokernel m` in degree `m` is a monomorphism. -/
lemma mono_truncLECokernel_d : Mono ((K.truncLECokernel m).d m (m + 1)) := by
  have hex : (K.truncLECokernel m).ExactAt ((embeddingUpIntLE m).f 0) :=
    (K.shortComplexTruncLE_X₃_isSupportedOutside (embeddingUpIntLE m)).exactAt 0
  have h0 : (embeddingUpIntLE m).f 0 = m := by change m - ((0 : ℕ) : ℤ) = m; simp
  rw [h0, HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp)] at hex
  exact hex.mono_g (IsZero.eq_of_src (K.isZero_truncLECokernel_X m (m - 1) (by lia)) _ _)

@[reassoc (attr := simp)]
lemma iCycles_toTruncLECokernel_f : K.iCycles m ≫ (K.toTruncLECokernel m).f m = 0 := by
  have := K.mono_truncLECokernel_d m
  rw [← cancel_mono ((K.truncLECokernel m).d m (m + 1)), Category.assoc,
    HomologicalComplex.Hom.comm, HomologicalComplex.iCycles_d_assoc, zero_comp, zero_comp]

/-- In degree `m`, the sequence `0 → Ker dᵐ → Kᵐ → (K.truncLECokernel m)ᵐ → 0` is short exact:
the degree `m` term of `K.truncLECokernel m` is `Kᵐ / Ker dᵐ`. -/
lemma shortExact_iCycles_toTruncLECokernel_f :
    (ShortComplex.mk _ _ (K.iCycles_toTruncLECokernel_f m)).ShortExact := by
  have hS := K.shortExact_eval_shortComplexTruncLE m m
  have := K.mono_truncLECokernel_d m
  have := K.isIso_toTruncLECokernel_f m (m + 1) (by lia)
  have : Epi ((K.toTruncLECokernel m).f m) := hS.epi_g
  refine { exact := ?_ }
  let S' : ShortComplex C := ShortComplex.mk (K.iCycles m) (K.d m (m + 1)) (by simp)
  have hS' : S'.Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel m (m + 1) (by simp))
  let φ : ShortComplex.mk _ _ (K.iCycles_toTruncLECokernel_f m) ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (K.truncLECokernel m).d m (m + 1) ≫ inv ((K.toTruncLECokernel m).f (m + 1))
      comm₁₂ := by simp [S']
      comm₂₃ := by
        dsimp [S']
        rw [Category.id_comp, ← Category.assoc, HomologicalComplex.Hom.comm,
          Category.assoc, IsIso.hom_inv_id, Category.comp_id] }
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS'

end CochainComplex
