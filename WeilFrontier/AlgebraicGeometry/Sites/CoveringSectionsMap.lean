module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringSectionsMap

/-!
# Morphisms of coverings induce the same map on sections

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)`, `f : B ⟶ B'` a
morphism of `Et(A)` and `(σ, h), (τ, k) : 𝔅 ⟶ 𝔅'` two morphisms over `f` between coverings
`𝔅 = (gᵢ)_{i ∈ I}` of `B` and `𝔅' = (g'ⱼ)_{j ∈ J}` of `B'`. Then `(σ, h)_* = (τ, k)_*` as maps
`F(𝔅) → F(𝔅')`. Indeed, for `j ∈ J` the morphisms `hⱼ : B_{σ j} ⟶ B'ⱼ` and
`kⱼ : B_{τ j} ⟶ B'ⱼ` satisfy `hⱼ ∘ g_{σ j} = g'ⱼ ∘ f = kⱼ ∘ g_{τ j}`, so the compatibility of a
section `(sᵢ)ᵢ ∈ F(𝔅)` gives `F(hⱼ)(s_{σ j}) = F(kⱼ)(s_{τ j})`.

## Main results

- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsMap_eq`: two morphisms of coverings
  over the same `f` induce the same map on the sections of a presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsAddMonoidHom_eq`: the same for a
  presheaf of abelian groups.

## Implementation notes

The statement is proved for morphisms over an arbitrary `f : B ⟶ B'`; the case of morphisms
in the category of coverings of a fixed object is `f = 𝟙 B`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

namespace Covering

namespace HomOver

variable {A : CommRingCat.{u}} {B B' : EtaleCategory A} {f : B ⟶ B'}
  {𝔅 : Covering.{w} B} {𝔅' : Covering.{w} B'}

/-- Two morphisms `(σ, h), (τ, k) : 𝔅 ⟶ 𝔅'` of coverings over the same `f : B ⟶ B'` induce the
same map `F(𝔅) → F(𝔅')` on the sections of a presheaf of sets `F`. -/
@[weil "lem_fk101_covering_morphisms_induce_same_map"]
theorem sectionsMap_eq (F : EtaleCategory A ⥤ Type v) (φ ψ : HomOver f 𝔅 𝔅') :
    φ.sectionsMap F = ψ.sectionsMap F := by
  funext s
  refine Subtype.ext <| funext fun j ↦ ?_
  simp only [sectionsMap_apply]
  exact map_eq_map_of_mem_coveringSections F 𝔅.map s.2 _ _ (by rw [φ.comm, ψ.comm])

/-- Two morphisms `(σ, h), (τ, k) : 𝔅 ⟶ 𝔅'` of coverings over the same `f : B ⟶ B'` induce the
same homomorphism `F(𝔅) → F(𝔅')` on the sections of a presheaf of abelian groups `F`. -/
@[weil "lem_fk101_covering_morphisms_induce_same_map"]
theorem sectionsAddMonoidHom_eq (F : EtaleCategory A ⥤ AddCommGrpCat.{v})
    (φ ψ : HomOver f 𝔅 𝔅') :
    φ.sectionsAddMonoidHom F = ψ.sectionsAddMonoidHom F := by
  ext s : 1
  refine Subtype.ext <| funext fun j ↦ ?_
  exact map_eq_map_of_mem_coveringSections (F ⋙ forget AddCommGrpCat) 𝔅.map s.2 _ _
    (by rw [φ.comm, ψ.comm])

end HomOver

end Covering

end EtaleCategory

end AlgebraicGeometry
