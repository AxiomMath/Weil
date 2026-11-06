module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtaleCoveringFk101

/-!
# Composites of étale coverings

Let `A` be a commutative ring. If `(gᵢ : B → Bᵢ)ᵢ` is an étale covering of an object `B` of the
étale category `Et(A)` and, for each `i`, `(cᵢₖ : Bᵢ → Cᵢₖ)ₖ` is an étale covering of `Bᵢ`, then
the family of composites `(cᵢₖ ∘ gᵢ : B → Cᵢₖ)ᵢ,ₖ` is an étale covering of `B`: it is finite, and
a prime of `B` is the preimage of a prime `q` of some `Bᵢ`, which is itself the preimage of a
prime of some `Cᵢₖ`.

## Main results

- `AlgebraicGeometry.EtaleCategory.IsCovering.comp`: the composite of étale coverings is an
  étale covering.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

public section

universe u w w'

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

lemma ringHom_comp {B C D : EtaleCategory A} (g : B ⟶ C) (c : C ⟶ D) :
    ringHom (g ≫ c) = ringHom g ≫ ringHom c :=
  rfl

/-- If `(gᵢ : B ⟶ Bᵢ)ᵢ` is an étale covering of `B` and each `(cᵢₖ : Bᵢ ⟶ Cᵢₖ)ₖ` is an étale
covering of `Bᵢ`, then the composites `gᵢ ≫ cᵢₖ`, indexed by the pairs `⟨i, k⟩`, form an étale
covering of `B`. -/
@[weil "lem_fk101_covering_composite"]
theorem IsCovering.comp {B : EtaleCategory A} {ι : Type w} {Bi : ι → EtaleCategory A}
    {g : ∀ i, B ⟶ Bi i} (hg : IsCovering g) {K : ι → Type w'}
    {C : ∀ i, K i → EtaleCategory A} {c : ∀ i k, Bi i ⟶ C i k}
    (hc : ∀ i, IsCovering (c i)) :
    IsCovering (fun ik : Σ i, K i ↦ g ik.1 ≫ c ik.1 ik.2) where
  finite := by
    have := hg.finite
    have := fun i ↦ (hc i).finite
    infer_instance
  exists_comap_eq p := by
    obtain ⟨i, q, rfl⟩ := hg.exists_comap_eq p
    obtain ⟨k, Q, rfl⟩ := (hc i).exists_comap_eq q
    exact ⟨⟨i, k⟩, Q, rfl⟩

end EtaleCategory

end AlgebraicGeometry
