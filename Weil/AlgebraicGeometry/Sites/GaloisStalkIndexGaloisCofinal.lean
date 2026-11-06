module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.GaloisStalk
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Galois elements are cofinal in the index of the Galois stalk

Let `K` be a field and `Ω` a normal extension of `K` (in the source, a separable closure `K̄`).
For any two elements `L, L'` of the poset `Λ_K` of finite separable intermediate fields of
`Ω / K`, there is an element `L''` of `Λ_K`, Galois over `K`, containing both: the normal
closure in `Ω` of the compositum `L L'`. It is finite over `K` since `L L'` is, and separable
since each conjugate of `L L'` in `Ω` is separable over `K`.

## Main results

- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.exists_isGalois_le`: for `L, L' ∈ Λ_K` there
  is `L'' ∈ Λ_K`, Galois over `K`, with `L ≤ L''` and `L' ≤ L''`.

## Implementation notes

The source takes `Ω = K̄`, a separable closure, which is normal over `K`; the statement here holds
for every normal extension `Ω` of `K`. The proof takes the normal closure of the compositum
instead of the splitting field of the minimal polynomial of a primitive element; the two agree.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

public section

universe u

open IntermediateField

namespace AlgebraicGeometry

namespace EtaleCategory

namespace GaloisStalkIndex

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The normal closure in `Ω` of a separable intermediate field of `Ω / K` is separable
over `K`. -/
private lemma isSeparable_normalClosure (M : IntermediateField K Ω) [Algebra.IsSeparable K M] :
    Algebra.IsSeparable K (normalClosure K M Ω) := by
  rw [← le_separableClosure_iff]
  refine normalClosure_le_iff.2 fun i ↦ ?_
  have : Algebra.IsSeparable K i.fieldRange :=
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i)
  exact le_separableClosure K Ω _

/-- **Galois elements are cofinal in `Λ_K`.** For `L, L' ∈ Λ_K`, with `Ω / K` normal, there is
`L'' ∈ Λ_K`, Galois over `K`, containing `L` and `L'`. -/
@[weil "lem_fk101_galois_stalk_index_galois_cofinal"]
theorem exists_isGalois_le [Normal K Ω] (L L' : GaloisStalkIndex K Ω) :
    ∃ L'' : GaloisStalkIndex K Ω, IsGalois K L''.field ∧ L ≤ L'' ∧ L' ≤ L'' := by
  let M : IntermediateField K Ω := (sup L L').field
  have hsep : Algebra.IsSeparable K (normalClosure K M Ω) := isSeparable_normalClosure M
  let L'' : GaloisStalkIndex K Ω := ofIsSeparable (normalClosure K M Ω)
  have hM : sup L L' ≤ L'' := le_iff.mpr (le_normalClosure M)
  have : Normal K L''.field := inferInstanceAs (Normal K (normalClosure K M Ω))
  exact ⟨L'', IsGalois.mk, (le_sup_left L L').trans hM, (le_sup_right L L').trans hM⟩

end GaloisStalkIndex

end EtaleCategory

end AlgebraicGeometry
