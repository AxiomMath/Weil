module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Homology.CompositeCollapse
public import Weil.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Attr

/-!
# Cohomology of a direct image with vanishing higher direct images

Let `f : X ⟶ Y` be a morphism of schemes and `F` an abelian étale sheaf on `X` such that the
higher direct images `R^q f_* F` vanish for every `q > 0`. Then `H^i(Y, f_* F) ≅ H^i(X, F)` for
every `i ≥ 0`.

Indeed, `f_*` is additive, left exact and carries injective sheaves to injective sheaves, so for
an injective resolution `F → I^•` the complex `f_* I^•` is, by the vanishing of the higher direct
images, an injective resolution of `f_* F`. Its global sections `Γ(Y, f_* I^•)` are
`Γ(X, I^•)`, because `Γ(Y, f_* G) = G(X ×_Y Y) = G(X)` naturally in the sheaf `G`. Taking
cohomology gives the isomorphism; it is the edge isomorphism of the Leray spectral sequence in
the case where that spectral sequence degenerates.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.smallPushforwardCompΓIso`: `Γ(Y, -) ∘ f_* ≅ Γ(X, -)`.
* `AlgebraicGeometry.BigEtaleSite.cohomologySmallPushforwardAddEquivOfIsZero`:
  `H^i(Y, f_* F) ≃+ H^i(X, F)` when `R^q f_* F = 0` for every `q > 0`.

## Implementation notes

The étale sites are the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of a big
étale site `B`, and `f_*` is `AlgebraicGeometry.BigEtaleSite.smallPushforward`. The coefficients
are `AddCommGrpCat.{u + 1}` for the universe `u` of the schemes, the universe of the objects of
the small étale site: there the direct image is known to preserve injective objects
(`AlgebraicGeometry.BigEtaleSite.injective_smallPushforward_obj`), and the cohomology
`CategoryTheory.Sheaf.H` is identified with the derived functors of global sections by
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`. The `Ext`-groups defining the
cohomology are a hypothesis `HasExt.{u + 1}` on both sheaf categories, as no global instance
exists.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.5
* [Stacks Project, Tag 03QC](https://stacks.math.columbia.edu/tag/03QC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- Global sections of abelian sheaves on a small étale site, with coefficients in
`AddCommGrpCat.{u + 1}`, are additive. -/
instance additive_Γ_smallEtale_addCommGrpCat (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    (Sheaf.Γ (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1} _

/-- The direct image of abelian sheaves with coefficients in `AddCommGrpCat.{u + 1}` preserves
injective objects. -/
instance preservesInjectiveObjects_smallPushforward_addCommGrpCat :
    (B.smallPushforward f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects where
  injective_obj {J} _ := injective_smallPushforward_obj B f J

/-- The base change `X ×_Y Y` of the final object of the small étale site of `Y` is a final
object of the small étale site of `X`. -/
def isTerminalSmallEtaleBaseChangeObjFinal :
    IsTerminal ((smallEtaleBaseChange B f).obj (SmallEtale.final B Y.obj Y.property)) :=
  (SmallEtale.finalIsTerminal B Y.obj Y.property).isTerminalObj _

/-- **Global sections of a direct image.** `Γ(Y, f_* G) = G(X ×_Y Y) = Γ(X, G)`, naturally in the
abelian sheaf `G` on the small étale site of `X`. -/
def smallPushforwardCompΓIso :
    B.smallPushforward f AddCommGrpCat.{u + 1} ⋙
        Sheaf.Γ (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
      (SmallEtale.finalIsTerminal B Y.obj Y.property)) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
      (isTerminalSmallEtaleBaseChangeObjFinal B f)).symm

/-- **Cohomology of a direct image with vanishing higher direct images.** Let `f : X ⟶ Y` be a
morphism of a big étale site and `F` an abelian sheaf on the small étale site of `X` with
`R^q f_* F = 0` for every `q > 0`. Then `H^i(Y, f_* F) ≅ H^i(X, F)` for every `i`. -/
@[weil "lem_fk105_cohomology_direct_image_higher_vanish"]
def cohomologySmallPushforwardAddEquivOfIsZero
    [HasExt.{u + 1} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : ∀ q : ℕ, 0 < q → IsZero ((higherDirectImage.{u + 1} B f q).obj F)) (i : ℕ) :
    ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F).H i ≃+ F.H i :=
  let e := smallPushforwardCompΓIso B f
  let eR : (B.smallPushforward f AddCommGrpCat.{u + 1} ⋙
        Sheaf.Γ (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}).rightDerived i ≅
      (Sheaf.Γ (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).rightDerived i :=
    { hom := NatTrans.rightDerived e.hom i
      inv := NatTrans.rightDerived e.inv i
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id] }
  (((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1} _ i).app _).symm ≪≫
    (Stacks.RightDerivedComp.objIso (B.smallPushforward f AddCommGrpCat.{u + 1})
      (InjectiveResolution.of F) hF
      (Sheaf.Γ (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) i).symm ≪≫
    eR.app F ≪≫
    (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1} _ i).app F
    ).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.BigEtaleSite
