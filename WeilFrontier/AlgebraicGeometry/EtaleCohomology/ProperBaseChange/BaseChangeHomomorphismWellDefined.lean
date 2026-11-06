module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import Weil.Attr

/-!
# The base change morphism of complexes is compatible with maps of resolutions

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. For a complex `I` of abelian sheaves on the small étale site
of `X` and a morphism of complexes `q : g'^* I ⟶ J`, the base change morphism of complexes is
`γ_q = f'_*(q) ∘ β_I : g^* f_* I ⟶ f'_* J`
(`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`). Given two such data `(I₁, q₁)`,
`(I₂, q₂)`, a morphism of complexes `ũ : I₁ ⟶ I₂` and a morphism `v : J₁ ⟶ J₂` with
`v ∘ q₁ ≃ q₂ ∘ g'^*(ũ)` (homotopic), we show
$$
f'_*(v) ∘ γ_{q₁} \simeq γ_{q₂} ∘ g^* f_*(ũ).
$$
The proof applies the additive functor `f'_*` degreewise to the given homotopy, precomposes with
`β_{I₁}`, and uses the naturality of the base change map `β` in the sheaf. As a consequence the
two composites induce the same maps on cohomology sheaves.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChangeHomotopy` — the homotopy
  `γ_{q₁} ≫ f'_*(v) ≃ g^* f_*(ũ) ≫ γ_{q₂}`, built from a homotopy `q₁ ≫ v ≃ g'^*(ũ) ≫ q₂`.
* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange_comp_homologyMap` — the two composites
  agree on cohomology in every degree.

The independence of the induced morphism in the derived category from the choice of resolutions
is `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_app_eq`.

## Implementation notes

The statement holds for arbitrary complexes `I₁, I₂, J₁, J₂` (of any complex shape) and arbitrary
morphisms `q₁, q₂`: neither the resolutions `ι_k : F_k ⟶ I_k` nor the compatibility
`ũ ∘ ι₁ ≃ ι₂ ∘ u` enter the proof, so they are not hypotheses. Sheaves are abelian sheaves on
Mathlib's small étale site `X.smallEtaleTopology`, the setting of
`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change morphism of complexes is compatible with maps of resolutions, up to
homotopy.** For morphisms of complexes `q₁ : g'^* I₁ ⟶ J₁`, `q₂ : g'^* I₂ ⟶ J₂`, `ũ : I₁ ⟶ I₂`
and `v : J₁ ⟶ J₂`, a homotopy `q₁ ≫ v ≃ g'^*(ũ) ≫ q₂` gives a homotopy
`γ_{q₁} ≫ f'_*(v) ≃ g^* f_*(ũ) ≫ γ_{q₂}` between morphisms `g^* f_* I₁ ⟶ f'_* J₂`. -/
@[weil "lem_fk106_base_change_homomorphism_well_defined"]
def etaleAbelianResolutionBaseChangeHomotopy {ι : Type*} {c : ComplexShape ι}
    {I₁ I₂ : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    {J₁ J₂ : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q₁ : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I₁ ⟶ J₁)
    (q₂ : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I₂ ⟶ J₂)
    (ũ : I₁ ⟶ I₂) (w : J₁ ⟶ J₂)
    (H : Homotopy (q₁ ≫ w) (((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).map ũ ≫
      q₂)) :
    Homotopy (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I₁ q₁ ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex c).map w)
      (((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
          c).map ũ ≫ etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I₂ q₂) := by
  refine (Homotopy.ofEq ?_).trans
    (((((etaleAbelianDirectImage.{u, v} f').mapHomotopy H).compLeft
      ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h) c).app
        I₁))).trans (Homotopy.ofEq ?_))
  · simp only [etaleAbelianResolutionBaseChange, Functor.map_comp, Category.assoc]
  · refine HomologicalComplex.hom_ext _ _ fun n => ?_
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, etaleAbelianResolutionBaseChange_f]
    rw [Functor.map_comp, (etaleAbelianBaseChange.{u, v} f g g' f' h).naturality_assoc]
    rfl

/-- The two composites `γ_{q₁} ≫ f'_*(v)` and `g^* f_*(ũ) ≫ γ_{q₂}` of
`etaleAbelianResolutionBaseChangeHomotopy` induce the same map on cohomology in every degree. -/
theorem etaleAbelianResolutionBaseChange_comp_homologyMap {ι : Type*} {c : ComplexShape ι}
    {I₁ I₂ : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    {J₁ J₂ : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q₁ : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I₁ ⟶ J₁)
    (q₂ : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I₂ ⟶ J₂)
    (ũ : I₁ ⟶ I₂) (w : J₁ ⟶ J₂)
    (H : Homotopy (q₁ ≫ w) (((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).map ũ ≫
      q₂)) (i : ι) :
    HomologicalComplex.homologyMap (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I₁ q₁ ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex c).map w) i =
      HomologicalComplex.homologyMap
        (((etaleAbelianDirectImage.{u, v} f ⋙
          etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex c).map ũ ≫
          etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I₂ q₂) i :=
  (etaleAbelianResolutionBaseChangeHomotopy.{u, v} f g g' f' h q₁ q₂ ũ w H).homologyMap_eq i

end Stacks.EtaleCohomology

end
