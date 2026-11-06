module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomologyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.Homology.Ext.MapExactFunctorTransport
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Attr

/-!
# Surjectivity of restriction to the closed fibre on `H¹` with finite constant coefficients

Let `A` be a henselian local ring, `f : X ⟶ Spec A` a proper morphism, `X₀` the closed fibre of
`f` and `i : X₀ ⟶ X` its inclusion. For a finite abelian group `M` (for instance `ℤ/nℤ`), the
restriction map `i^* : H¹(X, M) ⟶ H¹(X₀, i^* M)` on étale cohomology is surjective
[Stacks, Tag 0A5G]. Here this is proved on the small étale sites `AlgebraicGeometry.SmallEtale`
of a big étale site containing `X` and `X₀`, for the restriction map
`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`.

## Main results

* `AlgebraicGeometry.surjective_smallEtaleCohomologyRestrictionMap_closedFibre_one`: for `A`
  henselian local, `f` proper and `M` finite, restriction `H¹(X, M) ⟶ H¹(X₀, i^* M)` is
  surjective.
* `CategoryTheory.surjective_mapExtAddHom_of_equivalence_square`: surjectivity of the map induced
  on `Ext` by an exact functor transfers along a square of equivalences.

## Implementation notes

The result is [Stacks, Tag 0A5G] for Mathlib's small étale sites
(`Stacks.EtaleCohomology.surjective_etaleConstantCohomologyRestriction_one_of_isProper`),
transported along the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` of the categories of
abelian sheaves on the two presentations of the small étale site. These commute with inverse image
(`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`) and with the constant sheaf
functor (`CategoryTheory.equivCommuteConstant`), and an exact equivalence induces bijections on
`Ext` (`Stacks.Homology.bijective_mapExactFunctor_of_equivalence`).

Freitag and Kiehl state the result for `A` noetherian strictly henselian, `f` projective,
`M = ℤ/nℤ` with `n` invertible in `A`, under the hypothesis `dim X₀ ≤ 1`; none of these
hypotheses is needed in degree one, and the statement here is the general one: `A` henselian,
`f` proper, `M` finite.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1][FreitagKiehl]
* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory

section Transport

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  [Abelian C₂] {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁] {D₂ : Type u₄}
  [Category.{v₄} D₂] [Abelian D₂]
  [HasExt.{w} C₁] [HasExt.{w} C₂] [HasExt.{w'} D₁] [HasExt.{w'} D₂]

/-- Surjectivity of the map induced on `Ext` by an exact functor is unchanged when the two
objects are replaced by isomorphic ones. -/
theorem surjective_mapExtAddHom_of_iso (F : C₁ ⥤ D₁) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X X' Y Y' : C₁} (a : X ≅ X') (b : Y ≅ Y') (n : ℕ)
    (h : Function.Surjective (F.mapExtAddHom X' Y' n : Ext.{w} X' Y' n →+ Ext.{w'} _ _ n)) :
    Function.Surjective (F.mapExtAddHom X Y n : Ext.{w} X Y n →+ Ext.{w'} _ _ n) := by
  intro y
  obtain ⟨x', hx'⟩ := h (Stacks.Homology.extConj (F.map a.inv) (F.map b.hom) y)
  refine ⟨Stacks.Homology.extConj a.hom b.inv x', ?_⟩
  simp only [Functor.mapExtAddHom_apply] at hx' ⊢
  rw [Stacks.Homology.extConj_mapExactFunctor, hx', Stacks.Homology.extConj_extConj,
    ← F.map_comp, ← F.map_comp, a.hom_inv_id, b.hom_inv_id, F.map_id, F.map_id,
    Stacks.Homology.extConj_id]

/-- **Surjectivity on `Ext` transfers along a square of equivalences.** For exact functors
`F₁ : C₁ ⥤ C₂` and `F₂ : D₁ ⥤ D₂`, exact equivalences `e₁ : C₁ ≌ D₁`, `e₂ : C₂ ≌ D₂` and an
isomorphism `e₁ ⋙ F₂ ≅ F₁ ⋙ e₂`, if `F₂` induces a surjection
`Extⁿ(e₁ X, e₁ Y) ⟶ Extⁿ(F₂ e₁ X, F₂ e₁ Y)`, then `F₁` induces a surjection
`Extⁿ(X, Y) ⟶ Extⁿ(F₁ X, F₁ Y)`. -/
theorem surjective_mapExtAddHom_of_equivalence_square
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
    (h : Function.Surjective (F₂.mapExtAddHom (e₁.functor.obj X) (e₁.functor.obj Y) n :
      Ext.{w'} _ _ n →+ Ext.{w'} _ _ n)) :
    Function.Surjective (F₁.mapExtAddHom X Y n : Ext.{w} X Y n →+ Ext.{w} _ _ n) := by
  have : PreservesFiniteLimits (e₁.functor ⋙ F₂) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (e₁.functor ⋙ F₂) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (F₁ ⋙ e₂.functor) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (F₁ ⋙ e₂.functor) := comp_preservesFiniteColimits _ _
  intro y
  obtain ⟨x', hx'⟩ := h (Stacks.Homology.extConj (α.hom.app X) (α.inv.app Y)
    (y.mapExactFunctor e₂.functor : Ext.{w'} _ _ n))
  obtain ⟨x, rfl⟩ :=
    (Stacks.Homology.bijective_mapExactFunctor_of_equivalence.{w, w'} e₁ X Y n).2 x'
  refine ⟨x, ?_⟩
  apply Stacks.Homology.injective_mapExactFunctor_of_equivalence.{w, w'} e₂
  simp only [Functor.mapExtAddHom_apply] at hx' ⊢
  have key : ((x.mapExactFunctor e₁.functor : Ext.{w'} _ _ n).mapExactFunctor F₂ :
      Ext.{w'} _ _ n) = Stacks.Homology.extConj (α.hom.app X) (α.inv.app Y)
        ((x.mapExactFunctor F₁ : Ext.{w} _ _ n).mapExactFunctor e₂.functor :
          Ext.{w'} _ _ n) := by
    rw [← Stacks.Homology.ext_mapExactFunctor_comp_functor,
      ← Stacks.Homology.ext_mapExactFunctor_comp_functor,
      Stacks.Homology.ext_mapExactFunctor_of_iso' (F₁ ⋙ e₂.functor) (e₁.functor ⋙ F₂) α.symm x]
    rfl
  rw [key] at hx'
  have := congrArg (Stacks.Homology.extConj (α.inv.app X) (α.hom.app Y)) hx'
  simpa only [Stacks.Homology.extConj_extConj, Iso.inv_hom_id_app, Stacks.Homology.extConj_id,
    Functor.comp_obj] using this

end Transport

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-- The closed fibre `X₀` of `f : X ⟶ Spec A`, regarded as an object of a big étale site which
contains it. -/
abbrev BigEtaleSite.closedFibre (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [IsLocalRing A]
    (X : B.Scheme) (f : X.obj ⟶ Spec (.of A))
    (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f)) : B.Scheme :=
  B.obj (Stacks.EtaleCohomology.closedFibre A f) hX₀

/-- The inclusion `X₀ ⟶ X` of the closed fibre, as a morphism of a big étale site. -/
abbrev BigEtaleSite.closedFibreInclusion (B : BigEtaleSite.{u}) (A : Type u) [CommRing A]
    [IsLocalRing A] (X : B.Scheme) (f : X.obj ⟶ Spec (.of A))
    (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f)) : B.closedFibre A X f hX₀ ⟶ X :=
  ObjectProperty.homMk (Stacks.EtaleCohomology.closedFibreInclusion A f)

section ClosedFibre

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [HenselianLocalRing A]
  (X : B.Scheme) (f : X.obj ⟶ Spec (.of A)) [IsProper f]
  (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f)) (M : Type) [AddCommGroup M]
  [Finite M]

/-- On Mathlib's small étale sites, the exact inverse image along the inclusion of the closed fibre
induces a surjection on `Ext¹` out of the constant sheaf `ℤ` into the constant sheaf `M`
([Stacks, Tag 0A5G], in the form
`Stacks.EtaleCohomology.surjective_etaleConstantCohomologyRestriction_one_of_isProper`). -/
theorem surjective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_one :
    Function.Surjective ((etaleAbelianInverseImage.{u, 0}
        (Stacks.EtaleCohomology.closedFibreInclusion A f)).mapExtAddHom
      ((constantSheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)))
      (etaleConstantSheaf.{u, 0} X.obj M) 1 :
        Ext.{u + 1} _ _ 1 →+ Ext.{u + 1} _ _ 1) := by
  have hS := surjective_etaleConstantCohomologyRestriction_one_of_isProper A f M
  let c := (etaleAbelianInverseImageConstantIso.{u, 0}
    (Stacks.EtaleCohomology.closedFibreInclusion A f)).app (AddCommGrpCat.of (ULift ℤ))
  let d := (etaleAbelianInverseImageConstantIso.{u, 0}
    (Stacks.EtaleCohomology.closedFibreInclusion A f)).app
    (AddCommGrpCat.of (ULift.{u + 1, 0} M))
  intro y
  obtain ⟨x, hx⟩ := hS (((Ext.mk₀ c.inv).comp y (zero_add 1)).comp (Ext.mk₀ d.hom) (add_zero 1))
  refine ⟨x, ?_⟩
  rw [etaleConstantCohomologyRestriction_apply] at hx
  have h1 := congrArg (fun z => z.comp (Ext.mk₀ d.inv) (add_zero 1)) hx
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
    Ext.comp_mk₀_id] at h1
  have h2 := congrArg (fun z => (Ext.mk₀ c.hom).comp z (zero_add 1)) h1
  simp only [Ext.mk₀_comp_mk₀_assoc, c, d, Iso.hom_inv_id, Ext.mk₀_id_comp,
    Ext.comp_mk₀_id] at h2
  exact h2

/-- **Restriction to the closed fibre is surjective on `H¹` with finite constant coefficients.**
Let `A` be a henselian local ring, `f : X ⟶ Spec A` proper, `X₀` the closed fibre of `f`,
contained in the big étale site `B`, and `i : X₀ ⟶ X` its inclusion. For every finite abelian
group `M`, the restriction map `i^* : H¹(X, M) ⟶ H¹(X₀, i^* M)` on the small étale sites is
surjective [Stacks, Tag 0A5G]. -/
@[weil "lem_fk106_dim_le_1_h1_surjective"]
theorem surjective_smallEtaleCohomologyRestrictionMap_closedFibre_one
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1})] :
    Function.Surjective (smallEtaleCohomologyRestrictionMap.{w} B
      (B.closedFibreInclusion A X f hX₀)
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M))) 1) := by
  let i := B.closedFibreInclusion A X f hX₀
  have : PreservesFiniteLimits (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) :=
    smallEtaleInverseImage_preservesFiniteLimits B i
  have : PreservesFiniteColimits (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) :=
    smallEtaleInverseImage_preservesFiniteColimits B i
  have : (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  let c := (smallEtaleInverseImageConstantSheafIso B i AddCommGrpCat.{u + 1}
    (AddCommGrpCat.of (ULift ℤ)))
  suffices hs : Function.Surjective ((smallEtaleInverseImage B i AddCommGrpCat.{u + 1}).mapExtAddHom
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)))
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M))) 1 : Ext.{w} _ _ 1 →+ Ext.{w} _ _ 1) by
    intro y
    obtain ⟨x, hx⟩ := hs ((Ext.mk₀ c.hom).comp y (zero_add 1))
    refine ⟨x, ?_⟩
    rw [smallEtaleCohomologyRestrictionMap_apply]
    rw [Functor.mapExtAddHom_apply] at hx
    erw [hx]
    rw [Ext.mk₀_comp_mk₀_assoc]
    simp [c]
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
  refine surjective_mapExtAddHom_of_equivalence_square.{w, u + 1}
    (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) F₂ E₁ E₂ α _ _ 1 ?_
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  let κ := equivCommuteConstant (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
    X.obj.smallEtaleTopology (SmallEtale.toEtaleSite B X.obj X.property)
    (SmallEtale.finalIsTerminal B X.obj X.property) (MorphismProperty.Over.mkIdTerminal _ _)
  refine surjective_mapExtAddHom_of_iso.{u + 1, u + 1} F₂ (κ.app _) (κ.app _) 1 ?_
  exact surjective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_one B A X f M

end ClosedFibre

end AlgebraicGeometry
