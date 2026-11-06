module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement

/-!
# The cochain map induced by a refinement

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, let `U` be an
object of `Et(S)` and let `𝔘 = (Uᵢ → U)_{i ∈ I}` and `𝔙 = (V_j → U)_{j ∈ J}` be families of
morphisms of `Et(S)` with target `U`. A refinement map `φ = (σ, (φᵢ)) : 𝔘 → 𝔙` consists of a
map `σ : I → J` and `U`-morphisms `φᵢ : Uᵢ → V_{σ(i)}`. For a presheaf `F` of abelian groups
on `Et(S)` it induces, in each degree `p`, the map
`φ^* : Č^p(𝔙, F) → Č^p(𝔘, F)`,
`(φ^* s)_{ν₀ … ν_p} = (φ_{ν₀} × ⋯ × φ_{ν_p})^* (s_{σ(ν₀) … σ(ν_p)})`,
restriction along the morphism of iterated fibre products
`φ_{ν₀} ×_U ⋯ ×_U φ_{ν_p} : U_ν → V_{σ(ν₀) … σ(ν_p)}`. These maps commute with the Čech
differentials, so they form a morphism of cochain complexes `Č^•(𝔙, F) ⟶ Č^•(𝔘, F)`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap`: the morphism of
  Čech complexes `φ^* : Č^•(𝔙, F) ⟶ Č^•(𝔘, F)` induced by a refinement `φ : 𝔘 ⟶ 𝔙`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementProductMap_π`: the morphism
  `U_ν ⟶ V_{σ ∘ ν}` of iterated fibre products is the product of the `φ_{ν_a}`: its
  composite with the `a`-th projection is the `a`-th projection followed by `φ_{ν_a}`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_f_π`: the degree-`p`
  component of `φ^*` at a tuple `ν` is the component of `s` at `σ ∘ ν` restricted along
  `U_ν ⟶ V_{σ ∘ ν}`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_f_apply`: the same
  formula, elementwise, for presheaves of abelian groups.

## Implementation notes

A refinement map is Mathlib's `CategoryTheory.PreZeroHypercover.Hom`, and the morphism of
complexes is `Stacks.CechSite.cechComplexMap`, applied to the refinement viewed as a morphism of
families over the identity of `U` (`CategoryTheory.PreZeroHypercover.homOverIdEquivHom`). As for
the Čech complex itself, neither finiteness of the index sets nor joint surjectivity is needed,
the two families may be indexed in different universes, and the coefficients may lie in any
preadditive category with products.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w w' v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SmallNoetherianSeparatedEtale B S hS}
  {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} U}

/-- The morphism of iterated fibre products `U_{ν₀} ×_U ⋯ ×_U U_{ν_p} ⟶
V_{σ(ν₀)} ×_U ⋯ ×_U V_{σ(ν_p)}` induced by a refinement `φ = (σ, (φᵢ))`. -/
noncomputable abbrev refinementProductMap (φ : E.Hom G) (p : ℕ) (ν : Fin (p + 1) → E.I₀) :
    (∏ᶜ (fun a ↦ Over.mk (E.f (ν a)))).left ⟶ (∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (ν a))))).left :=
  Stacks.CechSite.cechProductMap E G ((PreZeroHypercover.homOverIdEquivHom E G).symm φ) p ν

/-- The morphism `U_ν ⟶ V_{σ ∘ ν}` is `φ_{ν₀} ×_U ⋯ ×_U φ_{ν_p}`: followed by the `a`-th
projection it is the `a`-th projection followed by `φ_{ν_a}`. -/
@[reassoc]
lemma refinementProductMap_π (φ : E.Hom G) (p : ℕ) (ν : Fin (p + 1) → E.I₀) (a : Fin (p + 1)) :
    refinementProductMap φ p ν ≫ (Pi.π (fun b ↦ Over.mk (G.f (φ.s₀ (ν b)))) a).left =
      (Pi.π (fun b ↦ Over.mk (E.f (ν b))) a).left ≫ φ.h₀ (ν a) := by
  exact (Over.comp_left _ _ _ _ _).symm.trans (by erw [Pi.lift_π]; rfl)

/-- **The cochain map of a refinement.** A refinement `φ = (σ, (φᵢ)) : 𝔘 ⟶ 𝔙` of families of
morphisms of `Et(S)` with target `U` induces, for every presheaf `F` on `Et(S)` (with values in
abelian groups or, more generally, in a preadditive category with products), the morphism of
Čech complexes `φ^* : Č^•(𝔙, F) ⟶ Č^•(𝔘, F)`, given in degree `p` by
`(φ^* s)_ν = (φ_{ν₀} × ⋯ × φ_{ν_p})^* (s_{σ ∘ ν})`. -/
@[weil "def_fk102_refinement_cochain_map"]
noncomputable abbrev refinementCochainMap {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A] (φ : E.Hom G) (F : EtalePresheaf B S hS A) :
    cechComplex G F ⟶ cechComplex E F :=
  Stacks.CechSite.cechComplexMap E G ((PreZeroHypercover.homOverIdEquivHom E G).symm φ) F

/-- The degree-`p` component of `φ^*` at a tuple `ν` is the component at `σ ∘ ν` followed by
restriction along `U_ν ⟶ V_{σ ∘ ν}`. -/
@[weil "def_fk102_refinement_cochain_map", reassoc]
lemma refinementCochainMap_f_π {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A] (φ : E.Hom G) (F : EtalePresheaf B S hS A)
    (p : ℕ) (ν : Fin (p + 1) → E.I₀) :
    (refinementCochainMap φ F).f p ≫
        Pi.π (fun i : Fin (p + 1) → E.I₀ ↦ F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) ν =
      Pi.π (fun j : Fin (p + 1) → G.I₀ ↦ F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left)))
          (φ.s₀ ∘ ν) ≫
        F.map (refinementProductMap φ p ν).op :=
  Stacks.CechSite.cechComplexMap_f_Pi_π E G _ F p ν

/-- **The refinement formula, elementwise.** For a presheaf of abelian groups `F` and a
`p`-cochain `s` of `𝔙`, `(φ^* s)_{ν₀ … ν_p} = (φ_{ν₀} × ⋯ × φ_{ν_p})^* (s_{σ(ν₀) … σ(ν_p)})`. -/
lemma refinementCochainMap_f_apply [HasProducts.{w} AddCommGrpCat.{a}]
    [HasProducts.{w'} AddCommGrpCat.{a}] (φ : E.Hom G) (F : EtalePresheaf B S hS AddCommGrpCat.{a})
    (p : ℕ) (s : (cechComplex G F).X p) (ν : Fin (p + 1) → E.I₀) :
    Pi.π (Stacks.CechSite.cochainFactor E F p) ν ((refinementCochainMap φ F).f p s) =
      F.map (refinementProductMap φ p ν).op
        (Pi.π (Stacks.CechSite.cochainFactor G F p) (φ.s₀ ∘ ν) s) := by
  exact (ConcreteCategory.comp_apply _ _ s).symm.trans
    ((ConcreteCategory.congr_hom (refinementCochainMap_f_π φ F p ν) s).trans
      (ConcreteCategory.comp_apply _ _ s))

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
