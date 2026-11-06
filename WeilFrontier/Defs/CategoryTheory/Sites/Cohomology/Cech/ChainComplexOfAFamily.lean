module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Attr

/-!
# The Čech chain complex of free module sheaves on a covering

Let `C` be a category, `X` an object of `C` and `E = (Uᵢ ⟶ X)_{i ∈ I}` a family of morphisms
with target `X` whose finite nonempty fibre products `U_ν = U_{ν₀} ×_X ⋯ ×_X U_{ν_p}` exist.
For a functor `G : C ⥤ A` to a preadditive category with coproducts, the *Čech chain complex*
`K_•(E, G)` has degree-`p` term `⨁_{ν ∈ I^{p+1}} G(U_ν)` and differential
`d = ∑_j (-1)^j G(∂_j)` on the summand of `ν`, where `∂_j : U_ν ⟶ U_{ν₀ … ν̂_j … ν_p}` is the
projection omitting the `j`-th factor. The maps `G(U_ν ⟶ X)` for `ν ∈ I` assemble into an
augmentation `K₀(E, G) ⟶ G(X)` with `d₁` followed by it zero. This is the covariant
counterpart of the Čech cochain complex `Stacks.CechSite.cechComplex` of a presheaf.

Let `Λ` be a ring, `X` a scheme and `U` an object of the small étale site of `X`. For an étale
covering `𝔛 = (U_ν ⟶ U)` and `G` the functor `V ↦ (Ṽ)^Λ` sending an étale `X`-scheme to the
free sheaf of `Λ`-modules on the sheaf it represents, `K_•(𝔛, Λ) ⟶ (Ũ)^Λ` is the augmented
complex of sheaves of `Λ`-modules of Freitag–Kiehl, I.4.

## Main definitions

* `CategoryTheory.PreZeroHypercover.cechChainComplexFunctor`, and
  `CategoryTheory.PreZeroHypercover.cechChainComplex`: the Čech chain complex `K_•(E, G)`.
* `CategoryTheory.PreZeroHypercover.cechChainComplexAugmentation`: the augmentation
  `K₀(E, G) ⟶ G(X)`.
* `CategoryTheory.PreZeroHypercover.augmentedCechChainComplex`: the augmented complex
  `⋯ ⟶ K₁ ⟶ K₀ ⟶ G(X)`, with `G(X)` in degree `0`.
* `AlgebraicGeometry.SmallEtale.freeRepresentedSheaf`: `V ↦ (Ṽ)^Λ`, the free sheaf of
  `Λ`-modules on the represented sheaf.
* `AlgebraicGeometry.SmallEtale.cechFreeComplex`, and
  `AlgebraicGeometry.SmallEtale.cechFreeComplexAugmentation`: the complex `K_•(𝔛, Λ)` and its
  augmentation to `(Ũ)^Λ`.

## Main results

* `CategoryTheory.PreZeroHypercover.cechChainComplex_X`: `K_p = ⨁_{ν ∈ I^{p+1}} G(U_ν)`.
* `CategoryTheory.PreZeroHypercover.ι_cechChainComplex_d`: the alternating-sum formula for the
  differential on a summand.
* `CategoryTheory.PreZeroHypercover.ι_cechChainComplexAugmentation` and
  `CategoryTheory.PreZeroHypercover.cechChainComplex_d_comp_augmentation`: the augmentation on a
  summand, and `d₁` followed by the augmentation is zero.
* `AlgebraicGeometry.SmallEtale.cechFreeComplex_X`,
  `AlgebraicGeometry.SmallEtale.ι_cechFreeComplex_d`,
  `AlgebraicGeometry.SmallEtale.ι_cechFreeComplexAugmentation`: the same for `K_•(𝔛, Λ)`.

## Implementation notes

The complex is the alternating face map complex of the simplicial object obtained by
evaluating `G`, extended to formal coproducts by coproducts
(`CategoryTheory.Limits.FormalCoproduct.eval`), on the Čech simplicial formal coproduct
`Stacks.CechSite.cechSimplicialObject`, the object on which `Stacks.CechSite.cechComplex`
evaluates presheaves. The two complexes are therefore built from the same iterated fibre
products and face maps, which is what identifies `Hom(K_•(E, G), F)` with a Čech complex.

Neither finiteness of the index set nor joint surjectivity of the family is needed to define
the complex, so neither is imposed. On the small étale site, every `U_ν` is an étale
`X`-scheme and `(Ũ_ν)^Λ` is Mathlib's `CategoryTheory.Sheaf.composeAndSheafify` of the free
module functor applied to the represented sheaf `Ũ_ν`
(`AlgebraicGeometry.SmallEtale.representedSheaf`, the étale topology being subcanonical).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl1988]
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace CategoryTheory.PreZeroHypercover

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasCoproducts.{w} A]

/-- The summand `G(U_ν)` of the degree-`p` term of the Čech chain complex indexed by
`ν : Fin (p + 1) → I`, where `U_ν = U_{ν₀} ×_X ⋯ ×_X U_{ν_p}`. -/
noncomputable abbrev cechChainFactor (G : C ⥤ A) (p : ℕ) (ν : Fin (p + 1) → E.I₀) : A :=
  G.obj (∏ᶜ (fun a ↦ Over.mk (E.f (ν a))) : Over X).left

/-- The Čech chain complex construction, as a functor of the covariant functor `G : C ⥤ A`. -/
noncomputable def cechChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  (Functor.whiskeringLeft (Over X) C A).obj (Over.forget X) ⋙
    FormalCoproduct.eval.{w} (Over X) A ⋙
      (Functor.whiskeringLeft _ _ A).obj (Stacks.CechSite.cechSimplicialObject E) ⋙
        AlgebraicTopology.alternatingFaceMapComplex A

/-- **The Čech chain complex `K_•(E, G)`** of a functor `G : C ⥤ A` along a family
`E = (Uᵢ ⟶ X)`: the chain complex with degree-`p` term `⨁_{ν ∈ I^{p+1}} G(U_ν)` and the
alternating sum of the face maps as differential. -/
noncomputable abbrev cechChainComplex (G : C ⥤ A) : ChainComplex A ℕ :=
  (cechChainComplexFunctor E).obj G

/-- The degree-`p` term of the Čech chain complex is the coproduct, over all `(p+1)`-tuples
`ν` of indices, of `G(U_{ν₀} ×_X ⋯ ×_X U_{ν_p})`. -/
lemma cechChainComplex_X (G : C ⥤ A) (p : ℕ) :
    (cechChainComplex E G).X p = ∐ cechChainFactor E G p :=
  rfl

/-- **The Čech differential.** On the summand of a tuple `ν = (ν₀, …, ν_{p+1})`, the
differential `K_{p+1} ⟶ K_p` is `∑_j (-1)^j G(∂_j)`, where `∂_j` is the projection omitting
the `j`-th factor, followed by the inclusion of the summand of `(ν₀, …, ν̂_j, …, ν_{p+1})`. -/
lemma ι_cechChainComplex_d (G : C ⥤ A) (p : ℕ) (ν : Fin (p + 2) → E.I₀) :
    Sigma.ι (cechChainFactor E G (p + 1)) ν ≫ (cechChainComplex E G).d (p + 1) p =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (G.map (Stacks.CechSite.faceProjection E ν j).left ≫
          Sigma.ι (cechChainFactor E G p) (fun b ↦ ν (j.succAbove b))) := by
  change _ ≫ (AlgebraicTopology.AlternatingFaceMapComplex.obj
    (Stacks.CechSite.cechSimplicialObject E ⋙
      (FormalCoproduct.eval.{w} (Over X) A).obj (Over.forget X ⋙ G))).d (p + 1) p = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  refine (Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  refine (Preadditive.comp_zsmul _ _ _).trans ?_
  congr 1
  exact Sigma.ι_desc _ _

/-- **The augmentation** `K₀(E, G) ⟶ G(X)`, induced on the summand of `ν ∈ I` by the
structure morphism `U_ν ⟶ X`. -/
noncomputable def cechChainComplexAugmentation (G : C ⥤ A) :
    (cechChainComplex E G).X 0 ⟶ G.obj X :=
  Sigma.desc fun ν : Fin 1 → E.I₀ ↦ G.map (∏ᶜ (fun a ↦ Over.mk (E.f (ν a))) : Over X).hom

@[reassoc (attr := simp)]
lemma ι_cechChainComplexAugmentation (G : C ⥤ A) (ν : Fin 1 → E.I₀) :
    Sigma.ι (cechChainFactor E G 0) ν ≫ cechChainComplexAugmentation E G =
      G.map (∏ᶜ (fun a ↦ Over.mk (E.f (ν a))) : Over X).hom :=
  Sigma.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The differential `K₁ ⟶ K₀` followed by the augmentation is zero. -/
@[reassoc (attr := simp)]
lemma cechChainComplex_d_comp_augmentation (G : C ⥤ A) :
    (cechChainComplex E G).d 1 0 ≫ cechChainComplexAugmentation E G = 0 := by
  refine Sigma.hom_ext (f := cechChainFactor E G 1) _ _ fun ν ↦ ?_
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ comp_zero.symm)
  rw [ι_cechChainComplex_d E G 0 ν]
  refine (Preadditive.sum_comp _ _ _).trans ?_
  rw [Fin.sum_univ_two]
  simp only [Preadditive.zsmul_comp, Category.assoc, ι_cechChainComplexAugmentation,
    ← G.map_comp, Over.w]
  simp

/-- **The augmented Čech chain complex** `⋯ ⟶ K₁(E, G) ⟶ K₀(E, G) ⟶ G(X)`, with `G(X)` in
degree `0` and `K_p(E, G)` in degree `p + 1`. -/
noncomputable abbrev augmentedCechChainComplex (G : C ⥤ A) : ChainComplex A ℕ :=
  (cechChainComplex E G).augment (cechChainComplexAugmentation E G)
    (cechChainComplex_d_comp_augmentation E G)

/-- The augmentation as a morphism of chain complexes from `K_•(E, G)` to `G(X)` in degree
`0`. -/
noncomputable def cechChainComplexToSingle₀ [HasZeroObject A] (G : C ⥤ A) :
    cechChainComplex E G ⟶ (ChainComplex.single₀ A).obj (G.obj X) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨cechChainComplexAugmentation E G, cechChainComplex_d_comp_augmentation E G⟩

end CategoryTheory.PreZeroHypercover

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} (Λ : Type u) [Ring Λ]

/-- Sheaves of `Λ`-modules on the small étale site have all coproducts indexed by types of
size at most `u`, sheafification being available. -/
noncomputable instance hasCoproducts_sheaf_moduleCat [UnivLE.{w, u}] :
    HasCoproducts.{w} (Sheaf (topology B X hX) (ModuleCat.{u} Λ)) :=
  fun _ ↦ Sheaf.instHasColimitsOfShape

variable (B X hX) in
/-- The free sheaf of `Λ`-modules `(Ṽ)^Λ` on the sheaf `Ṽ` represented by an étale
`X`-scheme `V`, as a functor of `V`: the sheafification of `W ↦ Λ^(Hom_X(W, V))`. -/
noncomputable abbrev freeRepresentedSheaf :
    SmallEtale B X hX ⥤ Sheaf (topology B X hX) (ModuleCat.{u} Λ) :=
  smallEtaleYoneda B X hX ⋙ Sheaf.composeAndSheafify (topology B X hX) (ModuleCat.free Λ)

/-- The free sheaf of `Λ`-modules on an étale `X`-scheme `V` is the free sheaf of
`Λ`-modules on the represented sheaf `Ṽ`. -/
lemma freeRepresentedSheaf_obj (V : SmallEtale B X hX) :
    (freeRepresentedSheaf B X hX Λ).obj V =
      (Sheaf.composeAndSheafify (topology B X hX) (ModuleCat.free Λ)).obj (representedSheaf V) :=
  rfl

variable {Λ} {U : SmallEtale B X hX} (𝔛 : PreZeroHypercover.{w} U) [UnivLE.{w, u}]

/-- **The Čech complex `K_•(𝔛, Λ)` of free sheaves.** For a family `𝔛 = (U_ν ⟶ U)` of étale
`X`-schemes over `U` (an étale covering in the source), the chain complex of sheaves of
`Λ`-modules on the small étale site of `X` with `K_p = ⨁_{ν ∈ I^{p+1}} (Ũ_ν)^Λ`, where
`U_ν = U_{ν₀} ×_U ⋯ ×_U U_{ν_p}`, and differential `∑_j (-1)^j (∂̃_j)^Λ` on the summand of `ν`. -/
@[weil "def_fk104_cech_free_complex"]
noncomputable abbrev cechFreeComplex :
    ChainComplex (Sheaf (topology B X hX) (ModuleCat.{u} Λ)) ℕ :=
  𝔛.cechChainComplex (freeRepresentedSheaf B X hX Λ)

/-- **The augmentation** `K₀(𝔛, Λ) ⟶ (Ũ)^Λ`, induced by the morphisms `U_ν ⟶ U`. -/
@[weil "def_fk104_cech_free_complex"]
noncomputable abbrev cechFreeComplexAugmentation :
    (cechFreeComplex 𝔛).X 0 ⟶ (freeRepresentedSheaf B X hX Λ).obj U :=
  𝔛.cechChainComplexAugmentation (freeRepresentedSheaf B X hX Λ)

/-- The degree-`p` term of `K_•(𝔛, Λ)` is `⨁_{ν ∈ I^{p+1}} (Ũ_ν)^Λ`. -/
@[weil "def_fk104_cech_free_complex"]
lemma cechFreeComplex_X (p : ℕ) :
    (cechFreeComplex (Λ := Λ) 𝔛).X p =
      ∐ fun ν : Fin (p + 1) → 𝔛.I₀ ↦ (freeRepresentedSheaf B X hX Λ).obj
        (∏ᶜ (fun a ↦ Over.mk (𝔛.f (ν a))) : Over U).left :=
  rfl

/-- The differential of `K_•(𝔛, Λ)` on the summand of `ν = (ν₀, …, ν_{p+1})` is
`∑_j (-1)^j (∂̃_j)^Λ`, where `∂_j` omits the `j`-th factor. -/
@[weil "def_fk104_cech_free_complex"]
lemma ι_cechFreeComplex_d (p : ℕ) (ν : Fin (p + 2) → 𝔛.I₀) :
    Sigma.ι (𝔛.cechChainFactor (freeRepresentedSheaf B X hX Λ) (p + 1)) ν ≫
        (cechFreeComplex 𝔛).d (p + 1) p =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        ((freeRepresentedSheaf B X hX Λ).map (Stacks.CechSite.faceProjection 𝔛 ν j).left ≫
          Sigma.ι (𝔛.cechChainFactor (freeRepresentedSheaf B X hX Λ) p)
            (fun b ↦ ν (j.succAbove b))) :=
  𝔛.ι_cechChainComplex_d _ p ν

/-- The augmentation on the summand of `ν ∈ I` is `(Ũ_ν ⟶ Ũ)^Λ`. -/
@[weil "def_fk104_cech_free_complex"]
lemma ι_cechFreeComplexAugmentation (ν : Fin 1 → 𝔛.I₀) :
    Sigma.ι (𝔛.cechChainFactor (freeRepresentedSheaf B X hX Λ) 0) ν ≫
        cechFreeComplexAugmentation 𝔛 =
      (freeRepresentedSheaf B X hX Λ).map (∏ᶜ (fun a ↦ Over.mk (𝔛.f (ν a))) : Over U).hom :=
  𝔛.ι_cechChainComplexAugmentation _ ν

end AlgebraicGeometry.SmallEtale

end
