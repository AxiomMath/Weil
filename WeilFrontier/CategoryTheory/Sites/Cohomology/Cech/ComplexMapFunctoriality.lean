module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapFunctoriality

/-!
# The cochain map of a refinement is a functorial chain map

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, let `U` be an
object of `Et(S)` and let `F` be a presheaf of abelian groups on `Et(S)`. A refinement
`φ : 𝔘 ⟶ 𝔙` of families of morphisms with target `U` induces maps
`φ^* : Č^p(𝔙, F) → Č^p(𝔘, F)`. These commute with the Čech differentials,
`d^p ∘ φ^* = φ^* ∘ d^p`, and the assignment `φ ↦ φ^*` is contravariantly functorial:
`(φ ∘ ψ)^* = ψ^* ∘ φ^*` and `id^* = id`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_comm`: `φ^*` commutes
  with the Čech differentials.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_comp`: the cochain map
  of a composite refinement is the composite of the cochain maps, in the opposite order.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_id`: the identity
  refinement induces the identity of the Čech complex.

## Implementation notes

Since `φ^*` is a morphism of cochain complexes, the commutation with the differentials is
`HomologicalComplex.Hom.comm`. Functoriality is `Stacks.CechSite.cechComplexMap_comp` and
`Stacks.CechSite.cechComplexMap_id`, for refinements viewed as morphisms of families over the
identity of `U`. The three families may be indexed in different universes, and the
coefficients may lie in any preadditive category with products.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' w'' v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SmallNoetherianSeparatedEtale B S hS}
  {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} U} {H : PreZeroHypercover.{w''} U}
  {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- **`φ^*` commutes with the Čech differentials**: `d ∘ φ^* = φ^* ∘ d` in every degree. -/
@[weil "lem_fk102_refinement_cochain_map_commutes", reassoc]
lemma refinementCochainMap_comm [HasProducts.{w} A] [HasProducts.{w'} A] (φ : E.Hom G)
    (F : EtalePresheaf B S hS A) (p q : ℕ) :
    (refinementCochainMap φ F).f p ≫ (cechComplex E F).d p q =
      (cechComplex G F).d p q ≫ (refinementCochainMap φ F).f q :=
  (refinementCochainMap φ F).comm p q

/-- **Functoriality of `φ^*` in the refinement**: `(φ ∘ ψ)^* = ψ^* ∘ φ^*`, where `φ ∘ ψ` is
the refinement `φ` followed by `ψ`. -/
@[weil "lem_fk102_refinement_cochain_map_commutes", reassoc]
lemma refinementCochainMap_comp [HasProducts.{w} A] [HasProducts.{w'} A]
    [HasProducts.{w''} A] (φ : E.Hom G) (ψ : G.Hom H) (F : EtalePresheaf B S hS A) :
    refinementCochainMap (φ.comp ψ) F = refinementCochainMap ψ F ≫ refinementCochainMap φ F :=
  (Stacks.CechSite.cechComplexMap_comp E G H
    ((PreZeroHypercover.homOverIdEquivHom E G).symm φ)
    ((PreZeroHypercover.homOverIdEquivHom G H).symm ψ) (Category.comp_id (𝟙 U)) F).symm

/-- **The identity refinement induces the identity**: `id^* = id`. -/
@[weil "lem_fk102_refinement_cochain_map_commutes", simp]
lemma refinementCochainMap_id [HasProducts.{w} A] (F : EtalePresheaf B S hS A) :
    refinementCochainMap (PreZeroHypercover.Hom.id E) F = 𝟙 (cechComplex E F) :=
  Stacks.CechSite.cechComplexMap_id E F

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
