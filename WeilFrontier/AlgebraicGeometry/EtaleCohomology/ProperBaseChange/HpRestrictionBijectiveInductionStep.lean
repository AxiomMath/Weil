module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstructibleEmbedsInGoodSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.RestrictionBijectiveBelow
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import Weil.Attr

/-!
# Restriction to the closed fibre is bijective in every degree

Let `A` be a strictly henselian local ring, `f : X ⟶ Spec A` a proper morphism, `X₀` the closed
fibre and `i : X₀ ⟶ X` its inclusion. For every sheaf `F` of `ℤ/nℤ`-modules on the small étale
site of `X` (`n ≥ 1`), the restriction map `i^* : Hᵖ(X, F) ⟶ Hᵖ(X₀, i^* F)` is bijective in every
degree `p`. In particular the induction hypothesis `B_p` of the proof of the proper base change
theorem by Freitag and Kiehl holds for every `p`.

## Main results

* `AlgebraicGeometry.bijective_smallEtaleCohomologyRestrictionMap_closedFibre_of_nsmul`: the
  restriction map to the closed fibre is bijective in every degree on sheaves killed by `n ≥ 1`.
* `AlgebraicGeometry.cohomologyRestrictionBijectiveBelow_closedFibre`: the proposition `B_p`
  holds for the inclusion of the closed fibre, for every `p`.
* `CategoryTheory.injective_mapExtAddHom_of_equivalence_square`: injectivity of the map induced
  on `Ext` by an exact functor transfers along a square of equivalences.

## Implementation notes

Freitag and Kiehl prove bijectivity in degree `p` from the induction hypothesis `B_p`, assuming
`A` noetherian, `f` projective, `n` invertible in `A` and `dim X₀ ≤ 1`. Here the statement is the
stronger one given by the proper base change theorem
(`AlgebraicGeometry.bijective_etaleCohomologyRestrictionMap_closedFibre_of_nsmul`, on the small
étale sites `X.smallEtaleTopology`), transported to the small étale sites
`AlgebraicGeometry.SmallEtale` of a big étale site along the equivalences
`AlgebraicGeometry.SmallEtale.sheafEquiv`: no induction hypothesis, `A` strictly henselian, `f`
proper and no bound on `dim X₀`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1][FreitagKiehl]
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

/- FK's hypotheses (B_p, p ≥ 1, A noetherian, f projective, n invertible, dim X_s ≤ 1) are dropped:
the statement is proved in every degree from proper base change (stronger than FK's
statement). -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory

section Transport

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  [Abelian C₂] {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁] {D₂ : Type u₄}
  [Category.{v₄} D₂] [Abelian D₂]
  [HasExt.{w} C₁] [HasExt.{w} C₂] [HasExt.{w'} D₁] [HasExt.{w'} D₂]

/-- Injectivity of the map induced on `Ext` by an exact functor is unchanged when the two
objects are replaced by isomorphic ones. -/
theorem injective_mapExtAddHom_of_iso (F : C₁ ⥤ D₁) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X X' Y Y' : C₁} (a : X ≅ X') (b : Y ≅ Y') (n : ℕ)
    (h : Function.Injective (F.mapExtAddHom X' Y' n : Ext.{w} X' Y' n →+ Ext.{w'} _ _ n)) :
    Function.Injective (F.mapExtAddHom X Y n : Ext.{w} X Y n →+ Ext.{w'} _ _ n) := by
  intro x y hxy
  simp only [Functor.mapExtAddHom_apply] at hxy
  have h₁ : Stacks.Homology.extConj a.inv b.hom x = Stacks.Homology.extConj a.inv b.hom y := by
    apply h
    simp only [Functor.mapExtAddHom_apply, Stacks.Homology.extConj_mapExactFunctor, hxy]
  have h₂ := congrArg (Stacks.Homology.extConj a.hom b.inv) h₁
  simpa only [Stacks.Homology.extConj_extConj, a.hom_inv_id, b.hom_inv_id,
    Stacks.Homology.extConj_id] using h₂

/-- **Injectivity on `Ext` transfers along a square of equivalences.** For exact functors
`F₁ : C₁ ⥤ C₂` and `F₂ : D₁ ⥤ D₂`, exact equivalences `e₁ : C₁ ≌ D₁`, `e₂ : C₂ ≌ D₂` and an
isomorphism `e₁ ⋙ F₂ ≅ F₁ ⋙ e₂`, if `F₂` induces an injection
`Extⁿ(e₁ X, e₁ Y) ⟶ Extⁿ(F₂ e₁ X, F₂ e₁ Y)`, then `F₁` induces an injection
`Extⁿ(X, Y) ⟶ Extⁿ(F₁ X, F₁ Y)`. -/
theorem injective_mapExtAddHom_of_equivalence_square
    [EnoughInjectives C₁] [EnoughInjectives C₂] [EnoughInjectives D₁] [EnoughInjectives D₂]
    (F₁ : C₁ ⥤ C₂) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    (F₂ : D₁ ⥤ D₂) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (e₁ : C₁ ≌ D₁) [e₁.functor.Additive] [PreservesFiniteLimits e₁.functor]
    [PreservesFiniteColimits e₁.functor] [e₁.inverse.Additive] [PreservesFiniteLimits e₁.inverse]
    [PreservesFiniteColimits e₁.inverse]
    (e₂ : C₂ ≌ D₂) [e₂.functor.Additive] [PreservesFiniteLimits e₂.functor]
    [PreservesFiniteColimits e₂.functor] [e₂.inverse.Additive] [PreservesFiniteLimits e₂.inverse]
    [PreservesFiniteColimits e₂.inverse]
    (α : e₁.functor ⋙ F₂ ≅ F₁ ⋙ e₂.functor) (X Y : C₁) (n : ℕ)
    (h : Function.Injective (F₂.mapExtAddHom (e₁.functor.obj X) (e₁.functor.obj Y) n :
      Ext.{w'} _ _ n →+ Ext.{w'} _ _ n)) :
    Function.Injective (F₁.mapExtAddHom X Y n : Ext.{w} X Y n →+ Ext.{w} _ _ n) := by
  have : PreservesFiniteLimits (e₁.functor ⋙ F₂) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (e₁.functor ⋙ F₂) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (F₁ ⋙ e₂.functor) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (F₁ ⋙ e₂.functor) := comp_preservesFiniteColimits _ _
  have key : ∀ x : Ext.{w} X Y n,
      ((x.mapExactFunctor e₁.functor : Ext.{w'} _ _ n).mapExactFunctor F₂ :
        Ext.{w'} _ _ n) = Stacks.Homology.extConj (α.hom.app X) (α.inv.app Y)
          ((x.mapExactFunctor F₁ : Ext.{w} _ _ n).mapExactFunctor e₂.functor :
            Ext.{w'} _ _ n) := by
    intro x
    rw [← Stacks.Homology.ext_mapExactFunctor_comp_functor,
      ← Stacks.Homology.ext_mapExactFunctor_comp_functor,
      Stacks.Homology.ext_mapExactFunctor_of_iso' (F₁ ⋙ e₂.functor) (e₁.functor ⋙ F₂) α.symm x]
    rfl
  intro x y hxy
  simp only [Functor.mapExtAddHom_apply] at hxy
  apply Stacks.Homology.injective_mapExactFunctor_of_equivalence.{w, w'} e₁
  apply h
  simp only [Functor.mapExtAddHom_apply, key, hxy]

end Transport

end CategoryTheory

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme Stacks.Cohomology.ZModSheaf Stacks.EtaleCohomology

section MathlibSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

/-- Abelian sheaves on a small étale site, at the coefficients `AddCommGrpCat.{u + 1}`, form a
Grothendieck abelian category; this pins the coefficient universe. -/
private local instance (priority := 2000) isGrothendieckAbelian_sheaf_smallEtale_succ_closedFibre'
    (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, 0} Z

variable (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]

/-- On Mathlib's small étale sites, the exact inverse image along the inclusion of the closed
fibre induces an injection on `Extᵠ` out of the constant sheaf `ℤ` into every sheaf killed by
`n ≥ 1`. -/
private theorem injective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_of_nsmul
    {n : ℕ} (hn : 0 < n) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) (q : ℕ) :
    Function.Injective ((etaleAbelianInverseImage.{u, 0}
        (closedFibreInclusion A f)).mapExtAddHom
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q :
        Ext.{u + 1} _ _ q →+ Ext.{u + 1} _ _ q) := by
  intro x y hxy
  apply (bijective_etaleCohomologyRestrictionMap_closedFibre_of_nsmul A f hn F hF q).1
  rw [etaleCohomologyRestrictionMap_apply, etaleCohomologyRestrictionMap_apply]
  simp only [Functor.mapExtAddHom_apply] at hxy
  rw [hxy]

end MathlibSite

section SmallEtale

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A]
  (X : B.Scheme) (f : X.obj ⟶ Spec (.of A)) [IsProper f]
  (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f))
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
    AddCommGrpCat.{u + 1})]

/-- Restriction to the closed fibre is injective on sheaves killed by `n ≥ 1`, on the small
étale sites of a big étale site. -/
private theorem injective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul {n : ℕ}
    (hn : 0 < n) (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) (q : ℕ) :
    Function.Injective (smallEtaleCohomologyRestrictionMap.{w} B
      (B.closedFibreInclusion A X f hX₀) F q) := by
  let i := B.closedFibreInclusion A X f hX₀
  have : PreservesFiniteLimits (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) :=
    smallEtaleInverseImage_preservesFiniteLimits B i
  have : PreservesFiniteColimits (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) :=
    smallEtaleInverseImage_preservesFiniteColimits B i
  have : (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  let c := (smallEtaleInverseImageConstantSheafIso B i AddCommGrpCat.{u + 1}
    (AddCommGrpCat.of (ULift ℤ)))
  suffices hs : Function.Injective ((smallEtaleInverseImage B i AddCommGrpCat.{u + 1}).mapExtAddHom
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q : Ext.{w} _ _ q →+ Ext.{w} _ _ q) by
    intro x y hxy
    apply hs
    rw [smallEtaleCohomologyRestrictionMap_apply, smallEtaleCohomologyRestrictionMap_apply]
      at hxy
    have h2 := congrArg (fun z => (Ext.mk₀ c.hom).comp z (zero_add q)) hxy
    simpa [c, i, Ext.mk₀_comp_mk₀_assoc] using h2
  let T : B.Scheme := B.closedFibre A X f hX₀
  let E₁ := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  let E₂ := SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}
  let F₂ := etaleAbelianInverseImage.{u, 0} (B.inclusion.map i)
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map i)).IsContinuous
      X.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    SmallEtale.isContinuous_inclusionSmallEtaleBaseChange B i
  let adjU := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map i)) AddCommGrpCat.{u + 1}
    X.obj.smallEtaleTopology T.obj.smallEtaleTopology
  let α := SmallEtale.sheafEquivPullbackBaseChangeIso B i AddCommGrpCat.{u + 1} adjU
    (smallEtaleInverseImageAdjunction B i AddCommGrpCat.{u + 1})
  have : EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
    EnoughInjectives.of_equivalence E₁.functor
  have : EnoughInjectives (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}) :=
    EnoughInjectives.of_equivalence E₂.functor
  have : E₁.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : E₁.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : E₂.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : E₂.inverse.Additive := Functor.additive_of_preserves_binary_products _
  refine injective_mapExtAddHom_of_equivalence_square.{w, u + 1}
    (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) F₂ E₁ E₂ α _ _ q ?_
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  let κ := equivCommuteConstant (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
    X.obj.smallEtaleTopology (SmallEtale.toEtaleSite B X.obj X.property)
    (SmallEtale.finalIsTerminal B X.obj X.property) (MorphismProperty.Over.mkIdTerminal _ _)
  refine injective_mapExtAddHom_of_iso.{u + 1, u + 1} F₂ (κ.app _) (Iso.refl _) q ?_
  have hF' : (n : ℤ) • 𝟙 (E₁.functor.obj F) = 0 := by
    rw [← E₁.functor.map_id, ← Functor.map_zsmul, hF, Functor.map_zero]
  exact injective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_of_nsmul A f hn
    (E₁.functor.obj F) hF' q

/-- **Restriction to the closed fibre is bijective in every degree.** Let `A` be a strictly
henselian local ring, `f : X ⟶ Spec A` proper, `X₀` the closed fibre, contained in the big étale
site `B`, and `i : X₀ ⟶ X` its inclusion. For every abelian sheaf `F` on the small étale site of
`X` all of whose sections are killed by `n ≥ 1` (a sheaf of `ℤ/nℤ`-modules), the restriction map
`i^* : Hᵖ(X, F) ⟶ Hᵖ(X₀, i^* F)` is bijective for every `p`. -/
@[weil "lem_fk106_hp_restriction_bijective_induction_step"]
theorem bijective_smallEtaleCohomologyRestrictionMap_closedFibre_of_nsmul {n : ℕ} (hn : 0 < n)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : ∀ (U : SmallEtale B X.obj X.property) (x : F.obj.obj (op U)), n • x = 0) (p : ℕ) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap.{w} B
      (B.closedFibreInclusion A X f hX₀) F p) := by
  have hF' : (n : ℤ) • 𝟙 F = 0 := by
    refine (zsmul_id_eq_zero_iff F (n : ℤ)).2 fun U x ↦ ?_
    rw [natCast_zsmul]
    exact hF U.unop x
  exact ⟨injective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul B A X f hX₀ hn F hF' p,
    surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul B A X f hX₀ hn F hF' p⟩

/-- **The induction hypothesis `B_p` holds for every `p`.** For the inclusion `i : X₀ ⟶ X` of the
closed fibre of a proper `f : X ⟶ Spec A` over a strictly henselian local ring and `n ≥ 1`,
restriction `Hᵠ(X, H) ⟶ Hᵠ(X₀, i^* H)` is bijective for every sheaf `H` killed by `n` and every
`q < p`. -/
theorem cohomologyRestrictionBijectiveBelow_closedFibre {n : ℕ} (hn : 0 < n) (p : ℕ) :
    CohomologyRestrictionBijectiveBelow.{w} B (B.closedFibreInclusion A X f hX₀) n p :=
  fun H hH q _ ↦ bijective_smallEtaleCohomologyRestrictionMap_closedFibre_of_nsmul B A X f hX₀ hn
    H hH q

end SmallEtale

end AlgebraicGeometry
