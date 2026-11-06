module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringMorphism

/-!
# Pulling back an étale covering along a morphism of the étale category

Let `A` be a commutative ring, `f : B ⟶ B'` a morphism of the étale category `Et(A)` and
`𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` an étale covering of `B`. The family of pushouts
`B' ⟶ Bᵢ ⊗_B B'` is an étale covering of `B'`, and the canonical maps `Bᵢ ⟶ Bᵢ ⊗_B B'`,
together with the identity of the index set, form a morphism of coverings over `f`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.Covering.pullback f 𝔅`: the covering `(B' ⟶ Bᵢ ⊗_B B')ᵢ`
  of `B'`.
- `AlgebraicGeometry.EtaleCategory.Covering.toPullback f 𝔅`: the morphism of coverings
  `𝔅 ⟶ Covering.pullback f 𝔅` over `f`.

## Main results

- `AlgebraicGeometry.EtaleCategory.Covering.exists_homOver`: for every morphism `f : B ⟶ B'`
  and covering `𝔅` of `B` there are a covering `𝔅'` of `B'` and a morphism `𝔅 ⟶ 𝔅'` over `f`.

## Implementation notes

Since `Et(A)` is the opposite of `Scheme.AffineEtale (Spec A)`, the object `Bᵢ ⊗_B B'` is
taken as the fibre product of `Spec Bᵢ ⟶ Spec B` and `Spec B' ⟶ Spec B` in
`Scheme.AffineEtale (Spec A)`, which is `Spec (Bᵢ ⊗_B B')`. The covering property then follows
from the stability of covering sieves of `Scheme.AffineEtale.topology (Spec A)` under pullback,
through `AlgebraicGeometry.EtaleCategory.isCovering_iff_mem_topology`, in place of the
pointwise argument with primes of the tensor product.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace EtaleCategory

namespace Covering

variable {A : CommRingCat.{u}} {B B' : EtaleCategory A}

/-- The pullback `(B' ⟶ Bᵢ ⊗_B B')ᵢ` of a covering `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` of `B` along a
morphism `f : B ⟶ B'` of `Et(A)`, a covering of `B'` with the same index set. -/
def pullback (f : B ⟶ B') (𝔅 : Covering.{w} B) : Covering.{w} B' where
  ι := 𝔅.ι
  obj i := op (Limits.pullback (𝔅.map i).unop f.unop)
  map i := (Limits.pullback.snd (𝔅.map i).unop f.unop).op
  isCovering := by
    rw [isCovering_iff_mem_topology]
    refine ⟨𝔅.isCovering.finite, ?_⟩
    have h : (Sieve.generate (Presieve.ofArrows (fun i ↦ (𝔅.obj i).unop)
        (fun i ↦ (𝔅.map i).unop))).pullback f.unop ∈
          Scheme.AffineEtale.topology (Spec A) B'.unop :=
      (Scheme.AffineEtale.topology (Spec A)).pullback_stable f.unop 𝔅.sieve_mem
    rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback] at h
    exact h

@[simp]
lemma pullback_ι (f : B ⟶ B') (𝔅 : Covering.{w} B) : (pullback f 𝔅).ι = 𝔅.ι := rfl

lemma pullback_map (f : B ⟶ B') (𝔅 : Covering.{w} B) (i : 𝔅.ι) :
    (pullback f 𝔅).map i = (Limits.pullback.snd (𝔅.map i).unop f.unop).op := rfl

/-- The morphism `(id, (Bᵢ ⟶ Bᵢ ⊗_B B')ᵢ)` from a covering `𝔅` of `B` to its pullback along
`f : B ⟶ B'`, over `f`. -/
def toPullback (f : B ⟶ B') (𝔅 : Covering.{w} B) : HomOver f 𝔅 (pullback f 𝔅) where
  σ i := i
  h i := (Limits.pullback.fst (𝔅.map i).unop f.unop).op
  comm i := Quiver.Hom.unop_inj (Limits.pullback.condition (f := (𝔅.map i).unop) (g := f.unop))

@[simp]
lemma toPullback_σ (f : B ⟶ B') (𝔅 : Covering.{w} B) (i : 𝔅.ι) :
    (toPullback f 𝔅).σ i = i := rfl

lemma toPullback_h (f : B ⟶ B') (𝔅 : Covering.{w} B) (i : 𝔅.ι) :
    (toPullback f 𝔅).h i = (Limits.pullback.fst (𝔅.map i).unop f.unop).op := rfl

/-- For a morphism `f : B ⟶ B'` of `Et(A)` and a covering `𝔅` of `B`, there are a covering
`𝔅'` of `B'` and a morphism of coverings `𝔅 ⟶ 𝔅'` over `f`. -/
@[weil "lem_fk101_covering_pullback"]
theorem exists_homOver (f : B ⟶ B') (𝔅 : Covering.{w} B) :
    ∃ 𝔅' : Covering.{w} B', Nonempty (HomOver f 𝔅 𝔅') :=
  ⟨pullback f 𝔅, ⟨toPullback f 𝔅⟩⟩

end Covering

end EtaleCategory

end AlgebraicGeometry
