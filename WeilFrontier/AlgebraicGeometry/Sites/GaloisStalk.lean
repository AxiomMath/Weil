module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.GaloisStalk

/-!
# Every finite subextension of a separable closure lies in `Λ_K`

Let `K` be a field and `Ω` a separable algebraic extension of `K` (in the source, a separable
closure `K̄`). Every intermediate field `K ⊆ L ⊆ Ω` with `[L : K] < ∞` belongs to the index set
`Λ_K` of the Galois stalk: `L` is separable over `K`, since every element of `Ω` is, so `L` is a
finite separable field extension of `K`, hence étale over `K`.

## Main results

- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.mem_of_finiteDimensional`: a finite
  intermediate field of a separable extension `Ω / K` is finite and étale over `K`.
- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.ofFiniteDimensional`: the corresponding
  element of `Λ_K`.

## Implementation notes

The source takes `Ω = K̄` a separable closure; the statement holds for any separable extension
`Ω / K` (`Algebra.IsSeparable K Ω`), which every separable closure is (`IsSepClosure`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

namespace EtaleCategory

namespace GaloisStalkIndex

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω]

/-- Every intermediate field `K ⊆ L ⊆ Ω` of finite degree over `K`, with `Ω / K` separable,
belongs to `Λ_K`: it is finite and étale over `K`. -/
@[weil "lem_fk101_galois_stalk_index_all_finite_subfields"]
theorem mem_of_finiteDimensional (L : IntermediateField K Ω) [FiniteDimensional K L] :
    FiniteDimensional K L ∧ Algebra.Etale K L :=
  (mem_iff L).mpr ⟨inferInstance, Algebra.isSeparable_tower_bot_of_isSeparable K L Ω⟩

/-- The element of `Λ_K` given by an intermediate field of finite degree of a separable
extension `Ω / K`. -/
def ofFiniteDimensional (L : IntermediateField K Ω) [FiniteDimensional K L] :
    GaloisStalkIndex K Ω :=
  ⟨L, mem_of_finiteDimensional L⟩

@[simp]
lemma field_ofFiniteDimensional (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (ofFiniteDimensional L).field = L := rfl

end GaloisStalkIndex

end EtaleCategory

end AlgebraicGeometry
