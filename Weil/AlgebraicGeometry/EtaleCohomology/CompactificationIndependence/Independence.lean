module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDerived
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CompactSupportCohomologyDerived
public import Weil.Defs.AlgebraicGeometry.Flatness.Flattening.CompactificationDominates
public import Weil.Attr

/-!
# Independence of `Rf_!` from the compactification

Let `f : X ⟶ S` be a separated morphism of finite type to a quasi-compact quasi-separated
scheme, and let `c₁ = (X̄₁, j₁, f̄₁)`, `c₂ = (X̄₂, j₂, f̄₂)` be compactifications of `f`. The
derived direct images with proper support `R f̄₁_* ∘ j₁!` and `R f̄₂_* ∘ j₂!`, on bounded below
complexes of étale sheaves of `Λ`-modules with torsion cohomology sheaves, are canonically
isomorphic: a domination `φ : c₃ ⟶ c` of compactifications induces an isomorphism
`θ_φ : R f̄_* ∘ j_! ≅ R f̄₃_* ∘ j₃!`, natural in the complex, and the isomorphism
`ρ₂₁ = θ_{φ₂}⁻¹ ∘ θ_{φ₁}` does not depend on the compactification `c₃` nor on the dominations
`φ₁ : c₃ ⟶ c₁`, `φ₂ : c₃ ⟶ c₂`.

This file states the result on the small étale sites `AlgebraicGeometry.SmallEtale` of a big
étale site, for the functor `AlgebraicGeometry.SmallEtale.derivedLowerShriek`. It is obtained
from the corresponding statement on Mathlib's small étale sites,
`Stacks.EtaleCohomology.derivedLowerShriek_independent_of_compactification_univ`, by transport
along the equivalences of sheaf categories.

## Main definitions

* `AlgebraicGeometry.SmallEtale.torsionPlusLift`: the equivalence of bounded below derived
  categories, restricted to the complexes with torsion cohomology sheaves.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekHomIso`: the isomorphism
  `θ_φ : Rf_!^c ≅ Rf_!^{c'}` on `D⁺_tors` attached to a domination `φ : c' ⟶ c`.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekCompactificationIso`: the canonical isomorphism
  `ρ₂₁ : Rf_!^{c₁} ≅ Rf_!^{c₂}` on `D⁺_tors`.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedLowerShriekHomIso_comp`: `θ_{φ ∘ φ'} = θ_{φ'} ∘ θ_φ`.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekCompactificationIso_eq`: for every
  compactification `c₃` and every pair of dominations `φ₁ : c₃ ⟶ c₁`, `φ₂ : c₃ ⟶ c₂`,
  `ρ₂₁ = θ_{φ₂}⁻¹ ∘ θ_{φ₁}`.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekCompactificationIso_trans`: `ρ₃₂ ∘ ρ₂₁ = ρ₃₁`.

## Implementation notes

The source works with noetherian schemes and a compactifiable morphism; here the base is
quasi-compact and quasi-separated and the morphism separated of finite type, under which
compactifications exist by Nagata's theorem. The source's sheaves are abelian sheaves; here they
are sheaves of `Λ`-modules for an arbitrary ring `Λ`, the source's case being `Λ = ℤ`. The
source builds `θ_φ` and proves the cocycle law on injective resolutions; here `θ_φ` is the
isomorphism of `Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv`, built from the derived
comparison map of the Stacks project (Tag 0F7G), transported to the small étale sites of `B`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.6][FreitagKiehl]
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} (Λ : Type r) [Ring Λ]

/-- The equivalence of bounded below derived categories between the small étale site of `X` in
`B` and Mathlib's small étale site of `X`, restricted to the complexes with torsion cohomology
sheaves: the torsion condition on the left is defined through this equivalence. -/
def torsionPlusLift (X : B.Scheme) :
    (isTorsionPlus B X.obj X.property Λ).FullSubcategory ⥤
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).FullSubcategory :=
  ObjectProperty.lift _ ((isTorsionPlus B X.obj X.property Λ).ι ⋙
    (moduleDerivedPlusEquiv B X.obj X.property Λ).functor) fun K => K.property

variable {X S : B.Scheme} {f : X.obj ⟶ S.obj}

/-- Transport of a natural isomorphism between functors on `D⁺_tors` of Mathlib's small étale
sites, of the shape `ι ⋙ F ≅ ι ⋙ G`, to the corresponding functors `ι ⋙ E_X ⋙ F ⋙ E_S⁻¹` on the
small étale sites of `B`. -/
def transportTorsionIso
    {F G : DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X.obj) ⥤
      DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ S.obj)}
    (α : (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ F ≅
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ G) :
    (isTorsionPlus B X.obj X.property Λ).ι ⋙
        ((moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙ F ⋙
          (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus) ≅
      (isTorsionPlus B X.obj X.property Λ).ι ⋙
        ((moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙ G ⋙
          (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus) :=
  Functor.isoWhiskerLeft (torsionPlusLift Λ X)
    (Functor.isoWhiskerRight α (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus)

@[simp]
lemma transportTorsionIso_hom_app
    {F G : DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X.obj) ⥤
      DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ S.obj)}
    (α : (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ F ≅
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ G)
    (K : (isTorsionPlus B X.obj X.property Λ).FullSubcategory) :
    (transportTorsionIso Λ α).hom.app K =
      (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus.map
        (α.hom.app ((torsionPlusLift Λ X).obj K)) :=
  rfl

lemma transportTorsionIso_trans
    {F G H : DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X.obj) ⥤
      DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ S.obj)}
    (α : (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ F ≅
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ G)
    (β : (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ G ≅
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ H) :
    transportTorsionIso Λ (α ≪≫ β) = transportTorsionIso Λ α ≪≫ transportTorsionIso Λ β := by
  rw [transportTorsionIso, Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans]
  rfl

lemma transportTorsionIso_symm
    {F G : DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X.obj) ⥤
      DerivedCategory.Plus (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ S.obj)}
    (α : (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ F ≅
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙ G) :
    transportTorsionIso Λ α.symm = (transportTorsionIso Λ α).symm := by
  exact Iso.ext rfl

/-- **The isomorphism `θ_φ : Rf_!^c ≅ Rf_!^{c'}` attached to a domination `φ : c' ⟶ c`** of
compactifications of `f`, on bounded below complexes of étale sheaves of `Λ`-modules with torsion
cohomology sheaves: `R f̄_* (j_! K) ≅ R f̄_* (R φ_* (j'_! K)) ≅ R f̄'_* (j'_! K)`. -/
def derivedLowerShriekHomIso {c' c : f.Compactification} (φ : c' ⟶ c) :
    (isTorsionPlus B X.obj X.property Λ).ι ⋙ derivedLowerShriek Λ f c ≅
      (isTorsionPlus B X.obj X.property Λ).ι ⋙ derivedLowerShriek Λ f c' :=
  transportTorsionIso Λ (Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv Λ φ)

/-- The isomorphisms `θ` of dominations compose: `θ_{φ' ≫ φ} = θ_φ ≪≫ θ_{φ'}`. -/
theorem derivedLowerShriekHomIso_comp {c'' c' c : f.Compactification} (φ' : c'' ⟶ c')
    (φ : c' ⟶ c) :
    derivedLowerShriekHomIso Λ (φ' ≫ φ) =
      derivedLowerShriekHomIso Λ φ ≪≫ derivedLowerShriekHomIso Λ φ' := by
  exact (congrArg (transportTorsionIso Λ)
    (Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv_comp Λ φ' φ)).trans
      (transportTorsionIso_trans Λ _ _)

variable (f) [CompactSpace S.obj] [QuasiSeparatedSpace S.obj] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]

/-- **The canonical isomorphism `ρ₂₁ : Rf_!^{c₁} ≅ Rf_!^{c₂}`** between the derived direct
images with proper support computed through two compactifications `c₁`, `c₂` of `f`, on bounded
below complexes of étale sheaves of `Λ`-modules with torsion cohomology sheaves. It is natural in
the complex, and equals `θ_{φ₂}⁻¹ ∘ θ_{φ₁}` for every compactification `c₃` dominating both
(`derivedLowerShriekCompactificationIso_eq`). -/
@[weil "lem_fk108_compactification_independence"]
def derivedLowerShriekCompactificationIso (c₁ c₂ : f.Compactification) :
    (isTorsionPlus B X.obj X.property Λ).ι ⋙ derivedLowerShriek Λ f c₁ ≅
      (isTorsionPlus B X.obj X.property Λ).ι ⋙ derivedLowerShriek Λ f c₂ :=
  transportTorsionIso Λ (Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv f c₁ c₂ Λ)

/-- The isomorphisms `ρ` compose: `ρ₂₁ ≪≫ ρ₃₂ = ρ₃₁`. -/
theorem derivedLowerShriekCompactificationIso_trans (c₁ c₂ c₃ : f.Compactification) :
    derivedLowerShriekCompactificationIso Λ f c₁ c₂ ≪≫
        derivedLowerShriekCompactificationIso Λ f c₂ c₃ =
      derivedLowerShriekCompactificationIso Λ f c₁ c₃ := by
  exact (transportTorsionIso_trans Λ _ _).symm.trans (congrArg (transportTorsionIso Λ)
    (Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv_trans f Λ c₁ c₂ c₃))

/-- Along a domination `φ : c' ⟶ c`, the isomorphism `ρ : Rf_!^c ≅ Rf_!^{c'}` is `θ_φ`. -/
theorem derivedLowerShriekCompactificationIso_of_hom {c' c : f.Compactification} (φ : c' ⟶ c) :
    derivedLowerShriekCompactificationIso Λ f c c' = derivedLowerShriekHomIso Λ φ := by
  exact congrArg (transportTorsionIso Λ)
    (Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv_of_hom f Λ φ)

/-- `ρ₁₂ = ρ₂₁⁻¹`. -/
theorem derivedLowerShriekCompactificationIso_symm (c₁ c₂ : f.Compactification) :
    (derivedLowerShriekCompactificationIso Λ f c₁ c₂).symm =
      derivedLowerShriekCompactificationIso Λ f c₂ c₁ := by
  have hrefl : ∀ c : f.Compactification,
      derivedLowerShriekCompactificationIso Λ f c c = Iso.refl _ := by
    intro c
    have h := congrArg (fun e => e.hom) (derivedLowerShriekCompactificationIso_trans Λ f c c c)
    refine Iso.ext (NatTrans.ext (funext fun K => ?_))
    have hK := congrArg (fun α => α.app K) h
    simp only [Iso.trans_hom, NatTrans.comp_app] at hK
    exact (cancel_epi ((derivedLowerShriekCompactificationIso Λ f c c).hom.app K)).mp
      (hK.trans (Category.comp_id _).symm)
  calc (derivedLowerShriekCompactificationIso Λ f c₁ c₂).symm
      = (derivedLowerShriekCompactificationIso Λ f c₁ c₂).symm ≪≫
          (derivedLowerShriekCompactificationIso Λ f c₁ c₂ ≪≫
            derivedLowerShriekCompactificationIso Λ f c₂ c₁) := by
        rw [derivedLowerShriekCompactificationIso_trans, hrefl, Iso.trans_refl]
    _ = derivedLowerShriekCompactificationIso Λ f c₂ c₁ := Iso.symm_self_id_assoc _ _

/-- **Independence of `Rf_!` from the compactification** (Freitag–Kiehl I.8.6). Let `c₁`, `c₂`
be compactifications of a separated morphism of finite type `f : X ⟶ S` to a quasi-compact
quasi-separated scheme. The canonical isomorphism `ρ₂₁ : Rf_!^{c₁} ≅ Rf_!^{c₂}` on bounded below
complexes with torsion cohomology sheaves, natural in the complex, is `θ_{φ₂}⁻¹ ∘ θ_{φ₁}` for
*every* compactification `c₃` of `f` and *every* pair of dominations `φ₁ : c₃ ⟶ c₁`,
`φ₂ : c₃ ⟶ c₂`. -/
@[weil "lem_fk108_compactification_independence"]
theorem derivedLowerShriekCompactificationIso_eq {c₁ c₂ c₃ : f.Compactification}
    (φ₁ : c₃ ⟶ c₁) (φ₂ : c₃ ⟶ c₂) :
    derivedLowerShriekCompactificationIso Λ f c₁ c₂ =
      derivedLowerShriekHomIso Λ φ₁ ≪≫ (derivedLowerShriekHomIso Λ φ₂).symm := by
  rw [← derivedLowerShriekCompactificationIso_of_hom Λ f φ₁,
    ← derivedLowerShriekCompactificationIso_of_hom Λ f φ₂,
    derivedLowerShriekCompactificationIso_symm, derivedLowerShriekCompactificationIso_trans]

end AlgebraicGeometry.SmallEtale
