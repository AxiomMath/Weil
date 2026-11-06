module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import Weil.Attr
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImageLambda
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.Homology.Ext.MapExactFunctorComp

/-!
# The inverse-image map on `Ext` groups is computed by any comparison of resolutions

Let `h : Z' ⟶ Z` be a morphism of schemes, `Λ` a ring and `A, B` sheaves of `Λ`-modules on the
small étale site of `Z`. Choose an injective resolution `B → I^•` of `B` and an injective
resolution `h^* B → J^•` of `h^* B`. Since `h^*` is exact, `h^* I^•` is a resolution of `h^* B`,
so there is a chain map `c : h^* I^• ⟶ J^•` compatible with the augmentations, and any two are
homotopic. The composite
`Hom(A, I^•) ⟶ Hom(h^* A, h^* I^•) ⟶ Hom(h^* A, J^•)`, `f ↦ c ∘ h^* f`,
induces on cohomology a map `Ext^p(A, B) ⟶ Ext^p(h^* A, h^* B)` (an *inverse-image map*). This
file shows that every such map is the inverse-image map
`Stacks.EtaleCohomology.etaleModuleExtInverseImage`; in particular there is exactly one
inverse-image map, independently of the comparison `c`.

The identification of `Ext^p(A, B)` with the `p`-th cohomology of `Hom(A, I^•)` is Mathlib's
`CategoryTheory.InjectiveResolution.extMk`: a cocycle `f : A ⟶ I^p` (that is, `f ≫ d = 0`)
represents the class `I.extMk f`, and every class is of this form
(`CategoryTheory.InjectiveResolution.extMk_surjective`).

## Main results

* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_extMk`: for any comparison `c` of
  `h^* I^•` with `J^•` over `h^* B`, the inverse-image map sends the class of a cocycle `f` of
  `Hom(A, I^•)` to the class of the cocycle `h^* f ≫ c` of `Hom(h^* A, J^•)`.
* `Stacks.EtaleCohomology.existsUnique_etaleModuleExtInverseImage`: there is exactly one map
  `Ext^p(A, B) → Ext^p(h^* A, h^* B)` induced on cocycles by some comparison of resolutions over
  `h^* B`, and it is `etaleModuleExtInverseImage`.

## Implementation notes

The resolutions `I` and `J` are arbitrary injective resolutions rather than chosen ones, and the
schemes are arbitrary rather than noetherian and separated; the statement contains the source's
case. The cocycle computation is the general fact
`Stacks.Cohomology.ModuleComparison.mapExactFunctor_extMk` for an exact functor of abelian
categories, and the existence of a comparison is
`Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.18][FK88]
-/

/- The identification Ext^p = H^p(Hom(A, I^•)) used is Mathlib's `InjectiveResolution.extMk`
(cocycle presentation of Ext), not this library's `Ext.addEquivHomologyOfInjectiveResolution`.
Stated on Mathlib's small étale site, as `etaleModuleExtInverseImage` is. -/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe w u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {Λ : Type r} [Ring Λ] {Z' Z : Scheme.{u}} {h : Z' ⟶ Z}
  [HasExt.{w} (EtaleModules.{u, r} Λ Z)] [HasExt.{w} (EtaleModules.{u, r} Λ Z')]

/-- **The inverse-image map on `Ext` on cocycles.** Let `I` be an injective resolution of `B`,
`J` one of `h^* B`, and `c : h^* I^• ⟶ J^•` a chain map compatible with the augmentations. Then
the inverse-image map `h^* : Ext^p(A, B) → Ext^p(h^* A, h^* B)` sends the class of a cocycle
`f : A ⟶ I^p` to the class of the cocycle `h^* f ≫ c^p`. -/
@[weil "lem_fk104_inverse_image_map_on_extgroups_exists_unique"]
theorem etaleModuleExtInverseImage_extMk {A B : EtaleModules.{u, r} Λ Z}
    (I : InjectiveResolution B) (J : InjectiveResolution ((etaleModuleInverseImage Λ h).obj B))
    (c : ((etaleModuleInverseImage Λ h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex ⟶ J.cocomplex)
    (hc : (etaleModuleInverseImage Λ h).map (I.ι.f 0) ≫ c.f 0 = J.ι.f 0)
    {p : ℕ} (f : A ⟶ I.cocomplex.X p) (hf : f ≫ I.cocomplex.d p (p + 1) = 0) :
    etaleModuleExtInverseImage Λ h A B p (I.extMk f (p + 1) rfl hf) =
      J.extMk ((etaleModuleInverseImage Λ h).map f ≫ c.f p) (p + 1) rfl
        (Stacks.Cohomology.ModuleComparison.extMk_map_comp_eq_zero _ I J c f rfl hf) :=
  Stacks.Cohomology.ModuleComparison.mapExactFunctor_extMk _ I J c hc f rfl hf

/-- **There is exactly one inverse-image map on `Ext`.** For injective resolutions `I` of `B` and
`J` of `h^* B`, there is exactly one map `φ : Ext^p(A, B) → Ext^p(h^* A, h^* B)` such that, for
some chain map `c : h^* I^• ⟶ J^•` compatible with the augmentations, `φ` sends the class of
every cocycle `f : A ⟶ I^p` to the class of `h^* f ≫ c^p`; it is `etaleModuleExtInverseImage`. -/
@[weil "lem_fk104_inverse_image_map_on_extgroups_exists_unique"]
theorem existsUnique_etaleModuleExtInverseImage {A B : EtaleModules.{u, r} Λ Z}
    (I : InjectiveResolution B) (J : InjectiveResolution ((etaleModuleInverseImage Λ h).obj B))
    (p : ℕ) :
    ∃! φ : Ext.{w} A B p →
        Ext.{w} ((etaleModuleInverseImage Λ h).obj A) ((etaleModuleInverseImage Λ h).obj B) p,
      ∃ (c : ((etaleModuleInverseImage Λ h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex ⟶ J.cocomplex)
        (_ : (etaleModuleInverseImage Λ h).map (I.ι.f 0) ≫ c.f 0 = J.ι.f 0),
        ∀ (f : A ⟶ I.cocomplex.X p) (hf : f ≫ I.cocomplex.d p (p + 1) = 0),
          φ (I.extMk f (p + 1) rfl hf) =
            J.extMk ((etaleModuleInverseImage Λ h).map f ≫ c.f p) (p + 1) rfl
              (Stacks.Cohomology.ModuleComparison.extMk_map_comp_eq_zero _ I J c f rfl hf) := by
  obtain ⟨c, hc⟩ := Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison
    (etaleModuleInverseImage Λ h) I J
  refine ⟨etaleModuleExtInverseImage Λ h A B p, ⟨c, hc, fun f hf =>
    etaleModuleExtInverseImage_extMk I J c hc f hf⟩, ?_⟩
  rintro φ ⟨c', hc', hφ⟩
  funext α
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (p + 1) rfl
  rw [hφ f hf, etaleModuleExtInverseImage_extMk I J c' hc' f hf]

end Stacks.EtaleCohomology

end

/-! ### The inverse image of sheaves of `Λ`-modules is additive and exact -/

/-!
# The inverse image of sheaves of `Λ`-modules is additive and exact

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B` and `Λ` a ring. The inverse
image `f^* : Sh(S_ét, Λ) ⥤ Sh(T_ét, Λ)` of sheaves of `Λ`-modules
(`AlgebraicGeometry.smallEtaleModuleSheafInverseImage`) is an additive functor, and it is exact:
it preserves finite limits and finite colimits. Consequently it sends an exact sequence
`G' ⟶ G ⟶ G''` of sheaves of `Λ`-modules to an exact sequence.

Additivity and right exactness hold because `f^*` is left adjoint to the direct image, which is
additive. Left exactness holds because `f^*` is the sheafification of the left Kan extension along
the opposite of base change: sheafification is left exact, and the colimits computing the Kan
extension are indexed by filtered categories (base change is representably flat), and filtered
colimits of `Λ`-modules are left exact.

## Main results

* `AlgebraicGeometry.smallEtaleModuleSheafInverseImage_additive_exact` — `f^*` on sheaves of
  `Λ`-modules is additive and exact.
* `CategoryTheory.ShortComplex.Exact.map_smallEtaleModuleSheafInverseImage` — `f^*` sends an
  exact sequence of sheaves of `Λ`-modules to an exact sequence.

## Implementation notes

The source deduces exactness from exactness of the inverse image of abelian sheaves, through the
identification of the underlying abelian sheaf of `f^* G` with `f^*` of the underlying abelian
sheaf of `G` (`AlgebraicGeometry.smallEtaleModuleSheafInverseImageForgetIso`). Here the
Kan-extension argument is carried out directly with coefficients in `ModuleCat.{w} Λ`, for any
universe `w` with `UnivLE.{u + 1, w}`, which avoids restricting the coefficient universe to the
one in which the abelian statement is available.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u r

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (Λ : Type r) [Ring Λ]
  [UnivLE.{u + 1, w}]

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat preservesFilteredColimits_forget_moduleCat
  hasLimitsOfShape_walkingMulticospan_moduleCat

/-- The left Kan extension along the opposite of small étale base change is left exact, for
coefficients in `ModuleCat.{w} Λ` with `UnivLE.{u + 1, w}`: the comma categories computing it
pointwise are filtered, and the forgetful functor from `Λ`-modules to sets preserves filtered
colimits of that size. -/
theorem preservesFiniteLimits_lan_op_smallEtaleBaseChange_moduleCat_of_univLE :
    PreservesFiniteLimits ((smallEtaleBaseChange B f).op.lan :
      ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ _) := by
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun X => ?_
  have : IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op X) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange B f) (Opposite.unop X))
  have : PreservesColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, u, u + 1} Λ
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{w}) :=
    have := preservesFilteredColimits_forget_addCommGrpCat.{u, w}
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  exact inferInstanceAs (PreservesColimitsOfShape
    (CostructuredArrow (smallEtaleBaseChange B f).op X)
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙ forget AddCommGrpCat.{w}))

attribute [local instance] preservesFiniteLimits_lan_op_smallEtaleBaseChange_moduleCat_of_univLE

/-- The inverse image of sheaves of `Λ`-modules preserves finite limits. -/
instance smallEtaleModuleSheafInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleModuleSheafInverseImage.{w} B f Λ) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- The inverse image of sheaves of `Λ`-modules preserves finite colimits, being a left
adjoint. -/
instance smallEtaleModuleSheafInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleModuleSheafInverseImage.{w} B f Λ) :=
  have := (smallEtaleModuleSheafInverseImageAdjunction.{w} B f Λ).isLeftAdjoint
  inferInstance

/-- The inverse image of sheaves of `Λ`-modules is additive, being left adjoint to the direct
image, which is additive. -/
instance smallEtaleModuleSheafInverseImage_additive :
    (smallEtaleModuleSheafInverseImage.{w} B f Λ).Additive :=
  have : ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).Additive := { map_add := rfl }
  (smallEtaleModuleSheafInverseImageAdjunction.{w} B f Λ).left_adjoint_additive

/-- **The inverse image of sheaves of `Λ`-modules is additive and exact.** For a morphism
`f : T ⟶ S` of schemes of a big étale site, the inverse image `f^*` from sheaves of `Λ`-modules on
the small étale site of `S` to those on the small étale site of `T` is an additive functor
preserving finite limits and finite colimits. -/
@[weil "lem_fka2_inverse_image_lambda_exact"]
theorem smallEtaleModuleSheafInverseImage_additive_exact :
    (smallEtaleModuleSheafInverseImage.{w} B f Λ).Additive ∧
      exactFunctor _ _ (smallEtaleModuleSheafInverseImage.{w} B f Λ) :=
  ⟨inferInstance, (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

/-- **The inverse image of sheaves of `Λ`-modules preserves exact sequences.** If
`G' ⟶ G ⟶ G''` is an exact sequence of sheaves of `Λ`-modules on the small étale site of `S`,
then `f^* G' ⟶ f^* G ⟶ f^* G''` is exact. -/
@[weil "lem_fka2_inverse_image_lambda_exact"]
theorem _root_.CategoryTheory.ShortComplex.Exact.map_smallEtaleModuleSheafInverseImage
    {X : ShortComplex (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} Λ))}
    (hX : X.Exact) :
    (X.map (smallEtaleModuleSheafInverseImage.{w} B f Λ)).Exact :=
  hX.map _

end AlgebraicGeometry

end

/-! ### Naturality of the inverse-image map on `Ext` groups -/

/-!
# Naturality of the inverse-image map on `Ext` groups

Let `h : Z' ⟶ Z` be a morphism of schemes and `Λ` a ring, and let
`h^* : Ext^p_Λ(Z; A, B) → Ext^p_Λ(Z'; h^* A, h^* B)` be the inverse-image map on `Ext` groups of
sheaves of `Λ`-modules on the small étale sites
(`Stacks.EtaleCohomology.etaleModuleExtInverseImage`). This file proves that it is natural:

* in both variables: for `u : A' ⟶ A` and `v : B ⟶ B'`, writing `Ext^p(u, v)` for the map
  `α ↦ u^* v_* α` (Yoneda composition with the degree-zero classes of `u` and `v`),
  `h^* ∘ Ext^p(u, v) = Ext^p(h^* u, h^* v) ∘ h^*`;
* in the morphism: for a further morphism `g : Z'' ⟶ Z'`, the composite `g^* ∘ h^*` is
  `(h ∘ g)^*` under the identification `g^* h^* ≅ (h ∘ g)^*` of inverse images
  (`Stacks.EtaleCohomology.etaleModuleInverseImageComp`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageComp`: the isomorphism
  `g^* ∘ h^* ≅ (g ≫ h)^*` of inverse-image functors of sheaves of `Λ`-modules, the conjugate of
  the identification `h_* ∘ g_* ≅ (g ≫ h)_*` of direct images.

## Main results

* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_naturality`: naturality in both variables.
* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_comp_morphism`: `(g ≫ h)^*` is `g^* ∘ h^*`
  conjugated by the components of `etaleModuleInverseImageComp`.
* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_comp_morphism_of_iso`: the same for any
  isomorphism `g^* ∘ h^* ≅ (g ≫ h)^*`.

## Implementation notes

The source proves both statements by comparing chain maps between injective resolutions. Here the
inverse-image map is the action of the exact functor `h^*` on `Ext` in the derived category, so
naturality in the variables is its compatibility with the Yoneda product, and compatibility with
composites is the corresponding statement for a composite of exact functors and for isomorphic
exact functors. The latter holds for every isomorphism of functors, not only the canonical one.
Sheaves are on Mathlib's small étale site `Z.smallEtaleTopology`, as for
`etaleModuleExtInverseImage`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FK88]
-/

/- Part (b) is stated with `etaleModuleInverseImageComp`, built on Mathlib's small étale site in the
same way as `AlgebraicGeometry.smallEtaleInverseImageComp` is
built on StacksFrontier's `SmallEtale`: the conjugate of the direct-image composition iso. The
`SmallEtale` iso is on a different site and is not used. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe w u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ]

/-- **The inverse image along a composite** of sheaves of `Λ`-modules on small étale sites: for
`g : Z'' ⟶ Z'` and `h : Z' ⟶ Z`, the isomorphism `g^* ∘ h^* ≅ (g ≫ h)^*`, the unique one
compatible with the adjunctions `f^* ⊣ f_*` and the identification `h_* ∘ g_* ≅ (g ≫ h)_*` of
direct images. -/
def etaleModuleInverseImageComp {Z'' Z' Z : Scheme.{u}} (g : Z'' ⟶ Z') (h : Z' ⟶ Z) :
    etaleModuleInverseImage Λ h ⋙ etaleModuleInverseImage Λ g ≅
      etaleModuleInverseImage Λ (g ≫ h) :=
  Adjunction.leftAdjointCompIso (etaleModuleInverseImageAdj Λ h) (etaleModuleInverseImageAdj Λ g)
    (etaleModuleInverseImageAdj Λ (g ≫ h))
    (smallEtalePushforwardComp' g h (g ≫ h) rfl (ModuleCat.{max (u + 1) r} Λ))

variable {Λ}

/-- **Naturality of the inverse-image map on `Ext` in both variables.** For `u : A' ⟶ A` and
`v : B ⟶ B'`, `h^* (u^* v_* α) = (h^* u)^* (h^* v)_* (h^* α)`, i.e.
`h^* ∘ Ext^p(u, v) = Ext^p(h^* u, h^* v) ∘ h^*`. -/
@[weil "lem_fk104_inverse_image_map_on_extgroups_natural"]
theorem etaleModuleExtInverseImage_naturality {Z' Z : Scheme.{u}} (h : Z' ⟶ Z)
    [HasExt.{w} (EtaleModules.{u, r} Λ Z)] [HasExt.{w} (EtaleModules.{u, r} Λ Z')]
    {A' A B B' : EtaleModules.{u, r} Λ Z} {p : ℕ} (u : A' ⟶ A) (v : B ⟶ B')
    (α : Ext.{w} A B p) :
    etaleModuleExtInverseImage Λ h A' B' p
        ((Ext.mk₀ u).comp (α.comp (Ext.mk₀ v) (add_zero p)) (zero_add p)) =
      (Ext.mk₀ ((etaleModuleInverseImage Λ h).map u)).comp
        ((etaleModuleExtInverseImage Λ h A B p α).comp
          (Ext.mk₀ ((etaleModuleInverseImage Λ h).map v)) (add_zero p)) (zero_add p) := by
  simp only [etaleModuleExtInverseImage_comp, etaleModuleExtInverseImage_mk₀]

/-- **The inverse-image map on `Ext` along a composite, for any identification.** For
`g : Z'' ⟶ Z'`, `h : Z' ⟶ Z` and any isomorphism `e : g^* ∘ h^* ≅ (g ≫ h)^*`, the map
`(g ≫ h)^*` on `Ext^p(A, B)` is `g^* ∘ h^*` followed by conjugation with the components of `e`. -/
theorem etaleModuleExtInverseImage_comp_morphism_of_iso {Z'' Z' Z : Scheme.{u}} (g : Z'' ⟶ Z')
    (h : Z' ⟶ Z) [HasExt.{w} (EtaleModules.{u, r} Λ Z)] [HasExt.{w} (EtaleModules.{u, r} Λ Z')]
    [HasExt.{w} (EtaleModules.{u, r} Λ Z'')]
    (e : etaleModuleInverseImage Λ h ⋙ etaleModuleInverseImage Λ g ≅
      etaleModuleInverseImage Λ (g ≫ h))
    {A B : EtaleModules.{u, r} Λ Z} {p : ℕ} (α : Ext.{w} A B p) :
    etaleModuleExtInverseImage Λ (g ≫ h) A B p α =
      (Ext.mk₀ (e.inv.app A)).comp
        ((etaleModuleExtInverseImage Λ g _ _ p (etaleModuleExtInverseImage Λ h A B p α)).comp
          (Ext.mk₀ (e.hom.app B)) (add_zero p)) (zero_add p) := by
  have : PreservesFiniteLimits (etaleModuleInverseImage Λ h ⋙ etaleModuleInverseImage Λ g) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (etaleModuleInverseImage Λ h ⋙ etaleModuleInverseImage Λ g) :=
    comp_preservesFiniteColimits _ _
  rw [etaleModuleExtInverseImage_apply, etaleModuleExtInverseImage_apply,
    etaleModuleExtInverseImage_apply,
    Stacks.Homology.ext_mapExactFunctor_of_iso _ _ e A p B α,
    Stacks.Homology.ext_mapExactFunctor_comp_functor _ _ A p B α]

/-- **The inverse-image map on `Ext` along a composite.** For `g : Z'' ⟶ Z'` and `h : Z' ⟶ Z`,
the map `(g ≫ h)^*` on `Ext^p(A, B)` is `g^* ∘ h^*` under the identification
`g^* h^* ≅ (g ≫ h)^*` of `etaleModuleInverseImageComp`. -/
@[weil "lem_fk104_inverse_image_map_on_extgroups_natural"]
theorem etaleModuleExtInverseImage_comp_morphism {Z'' Z' Z : Scheme.{u}} (g : Z'' ⟶ Z')
    (h : Z' ⟶ Z) [HasExt.{w} (EtaleModules.{u, r} Λ Z)] [HasExt.{w} (EtaleModules.{u, r} Λ Z')]
    [HasExt.{w} (EtaleModules.{u, r} Λ Z'')]
    {A B : EtaleModules.{u, r} Λ Z} {p : ℕ} (α : Ext.{w} A B p) :
    etaleModuleExtInverseImage Λ (g ≫ h) A B p α =
      (Ext.mk₀ ((etaleModuleInverseImageComp Λ g h).inv.app A)).comp
        ((etaleModuleExtInverseImage Λ g _ _ p (etaleModuleExtInverseImage Λ h A B p α)).comp
          (Ext.mk₀ ((etaleModuleInverseImageComp Λ g h).hom.app B)) (add_zero p)) (zero_add p) :=
  etaleModuleExtInverseImage_comp_morphism_of_iso g h _ α

end Stacks.EtaleCohomology
