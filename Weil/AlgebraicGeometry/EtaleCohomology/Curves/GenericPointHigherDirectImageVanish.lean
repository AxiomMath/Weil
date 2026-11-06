module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeGroupEtaleOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleHigherDirectImageStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.RefinedTorsionLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtension
public import Weil.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericDirectImageCohomologyVanishGe3
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.NormalSepClosedConstantDirectImage

/-!
# Higher direct images from the generic point of a curve

Let `k` be an algebraically closed field, `X` a curve over `k` with function field `K`,
`η : Spec K ⟶ X` the canonical morphism onto the generic point, and `𝒢` a torsion abelian sheaf
on the small étale site of `Spec K`. Then `R^q η_* 𝒢 = 0` for every `q ≥ 2`.

The higher direct image `R^q η_* 𝒢` is the sheafification of `V ↦ H^q(Spec K ×_X V, 𝒢)` on the
small étale site of `X`. Every `Spec K ×_X V` is étale over `Spec K`, hence a disjoint union of
spectra of finite separable extensions `L` of `K`, and its cohomology is the product of the
cohomology of the summands. Each such `L` is algebraic over `K`, so it has transcendence degree
one over `k`, and its cohomological dimension is at most one; the restriction of `𝒢` to
`Spec L` is again torsion, so its cohomology vanishes in degrees `q ≥ 2`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_field_of_torsion`: the
  higher direct images in degree `q > 0` of a torsion sheaf along a morphism out of the spectrum
  of a field `K` vanish, as soon as `H^q(Spec L, ℋ) = 0` for every finite separable extension
  `L` of `K` and every torsion sheaf `ℋ` on `Spec L`.
* `Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_of_torsion_of_trdeg_le_one`:
  `R^q η_* 𝒢 = 0` for `q ≥ 2` whenever the function field of the integral scheme `X` has
  transcendence degree at most one over a separably closed field `k`.
* `Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_of_torsion_of_isCurve`:
  `R^q η_* 𝒢 = 0` for `q ≥ 2`, on Mathlib's small étale sites.
* `AlgebraicGeometry.BigEtaleSite.isZero_higherDirectImage_genericPointHom_of_isTorsionSheaf`:
  the same on the bounded small étale sites `AlgebraicGeometry.SmallEtale` of a big étale site.

## Implementation notes

The source computes the stalks of `R^q η_* 𝒢` at the geometric points of `X` as colimits of the
groups `H^q(Spec K ×_X U, 𝒢)` over étale neighbourhoods, and shows that every term vanishes. Here
the vanishing of the groups `H^q(Spec K ×_X V, 𝒢)` for every étale `V ⟶ X` with affine source
is used directly: it kills the presheaf whose sheafification is `R^q η_* 𝒢`, so no stalks and no
colimits are needed. The argument follows
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field`,
with the multiplicative group replaced by an arbitrary torsion sheaf, and the vanishing over a
field of transcendence degree one is
`AlgebraicGeometry.Scheme.subsingleton_H_spec_of_trdeg_le_one`.

A curve is `AlgebraicGeometry.IsCurve`: an integral separated scheme of finite type over `k` of
dimension one. Neither separatedness nor algebraic closedness is used: the general form needs
only an integral scheme whose function field has transcendence degree at most one over a
separably closed field. Coefficients are abelian groups in `AddCommGrpCat.{u + 1}` for
`X : Scheme.{u}`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.5
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open Stacks.Cohomology.SheafifiedHigherDirectImage

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- The derived sections of an abelian sheaf `𝒢` on `X_ét` over a scheme `U` étale over `X`
are the étale cohomology of the restriction of `𝒢` to `U`; so if the latter vanishes in degree
`q`, so do the former. -/
theorem isZero_rightDerived_etaleSections_of_subsingleton_sheafH_etaleRestriction
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (h : Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleRestriction.{u, u + 1} j).obj G) q)) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk j))).rightDerived q).obj G) := by
  let : PreservesFiniteColimits ((smallEtaleCompose j).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} U.smallEtaleTopology X.smallEtaleTopology) :=
    have : PreservesColimitsOfSize.{0, 0} (etaleRestriction.{u, u + 1} j) :=
      (etaleDirectImageAdj.{u, u + 1} j).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesFiniteColimits _
  let : ((smallEtaleCompose j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology).PreservesInjectiveObjects :=
    RelativeMayerVietoris.etaleRestriction_preservesInjectiveObjects.{u, u + 1} j
  let : IsIso (Scheme.Etale.mk (𝟙 U)).hom := inferInstanceAs (IsIso (𝟙 U))
  let T : U.Etale := Scheme.Etale.mk (𝟙 U)
  let eW : Scheme.Etale.mk j ≅ (smallEtaleCompose j).obj T :=
    MorphismProperty.Over.isoMk (Iso.refl U) (by change 𝟙 U ≫ 𝟙 U ≫ j = j; simp)
  let S := sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
  refine IsZero.of_iso ?_
    ((Stacks.DerivedFunctor.rightDerivedIso (S.mapIso eW.op) q).symm.app _ ≪≫
      (pushforwardRightDerivedSectionsIso (J := U.smallEtaleTopology) (K := X.smallEtaleTopology)
        AddCommGrpCat.{u + 1} (smallEtaleCompose j) q T).symm.app _ ≪≫
      (Stacks.DerivedFunctor.rightDerivedIso (Sheaf.ΓNatIsoSheafSections U.smallEtaleTopology
        AddCommGrpCat.{u + 1} (isTerminalOfIsIsoHom T)) q).symm.app _)
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    U.smallEtaleTopology _ q).1 h

/-- The restriction of a torsion sheaf along an étale morphism is a torsion sheaf. -/
theorem torsionSheafProperty_etaleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) :
    Stacks.Torsion.torsionSheafProperty _ ((etaleRestriction.{u, u + 1} j).obj G) := by
  rw [Stacks.Torsion.torsionSheafProperty_iff_isLocallyAnnihilatedBy] at hG ⊢
  exact Stacks.Torsion.isLocallyAnnihilatedBy_pushforward _ _ (smallEtaleCompose j) _ G hG

/-- The derived sections in degree `q > 0` of a torsion sheaf `𝒢` on the small étale site of a
field `K`, over any object of that site, vanish as soon as `H^q(Spec L, ℋ) = 0` for every finite
separable extension `L` of `K` and every torsion sheaf `ℋ` on `Spec L`. -/
theorem isZero_rightDerived_etaleSections_of_field_of_torsion (K : Type u) [Field K]
    (W : (Spec (.of K)).Etale) (G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) (q : ℕ) (hq : 0 < q)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
      (H : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      Stacks.Torsion.torsionSheafProperty _ H → Subsingleton (Sheaf.H.{u + 1, u + 1} H q)) :
    IsZero ((((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op W)).rightDerived q).obj G) := by
  obtain ⟨I, L, hL, hAlg, hFin, hSep, e, -⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K W.hom).mp inferInstance
  let (i : I) : Field (L i) := hL i
  let (i : I) : Algebra K (L i) := hAlg i
  let (i : I) : Module.Finite K (L i) := hFin i
  let (i : I) : Algebra.IsSeparable K (L i) := hSep i
  let (i : I) : Etale (Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) := inferInstance
  let U (i : I) : (Spec (.of K)).Etale :=
    .mk (Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom)
  let eW : W ≅ etaleCoproduct U :=
    MorphismProperty.Over.isoMk e (by
      change e.hom ≫ (Sigma.desc fun i ↦ Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) =
        W.hom
      rw [show (Sigma.desc fun i ↦ Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) =
        e.inv ≫ W.hom from Sigma.hom_ext _ _ fun i ↦ by simp]
      simp)
  let S := sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}
  apply IsZero.of_iso _ ((Stacks.DerivedFunctor.rightDerivedIso (S.mapIso eW.op) q).symm.app _)
  refine isZero_rightDerived_etaleCoproduct_of_components.{u, u + 1} U _ q hq fun i ↦ ?_
  exact isZero_rightDerived_etaleSections_of_subsingleton_sheafH_etaleRestriction
    (Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) G q
    (h (L i) _ (torsionSheafProperty_etaleRestriction _ G hG))

/-- **The higher direct images of a torsion sheaf along a morphism out of the spectrum of a
field.** Let `K` be a field, `f : Spec K ⟶ Y` a morphism of schemes, `𝒢` a torsion sheaf on the
small étale site of `Spec K` and `q > 0`. If `H^q(Spec L, ℋ) = 0` for every finite separable
extension `L` of `K` and every torsion sheaf `ℋ` on `Spec L`, then `R^q f_* 𝒢 = 0`. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_field_of_torsion
    (K : Type u) [Field K] {Y : Scheme.{u}} (f : Spec (.of K) ⟶ Y)
    (G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) (q : ℕ) (hq : 0 < q)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
      (H : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      Stacks.Torsion.torsionSheafProperty _ H → Subsingleton (Sheaf.H.{u + 1, u + 1} H q)) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj G) :=
  isZero_rightDerived_etaleAbelianDirectImage_of_forall_affine_level f G q fun V _ ↦
    isZero_rightDerived_etaleSections_of_field_of_torsion K ((smallEtaleBaseChange f).obj V) G hG
      q hq h

/-- **Higher direct images from the generic point of a scheme whose function field has
transcendence degree at most one.** Let `k` be a separably closed field, `X` an integral scheme
whose function field `K` is an extension of `k` of transcendence degree at most one,
`η : Spec K ⟶ X` the canonical morphism onto the generic point, and `𝒢` a torsion sheaf on the
small étale site of `Spec K`. Then `R^q η_* 𝒢 = 0` for every `q ≥ 2`. -/
theorem isZero_rightDerived_genericPointDirectImage_of_torsion_of_trdeg_le_one
    (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (hK : Algebra.trdeg k X.functionField ≤ 1)
    (G : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).rightDerived q).obj
      G) := by
  refine isZero_rightDerived_etaleAbelianDirectImage_of_field_of_torsion
    ↥X.functionField (genericPointInclusion X) G hG q (by omega) fun L _ _ _ _ H hH ↦ ?_
  let : Algebra k L :=
    ((algebraMap X.functionField L).comp (algebraMap k X.functionField)).toAlgebra
  have : IsScalarTower k X.functionField L := .of_algebraMap_eq' rfl
  have htr := trdeg_add_eq k X.functionField (A := L)
  rw [show Algebra.trdeg X.functionField L = 0 from trdeg_eq_zero, add_zero] at htr
  exact Scheme.subsingleton_H_spec_of_trdeg_le_one k L (htr ▸ hK) H hH q hq

/-- **Higher direct images from the generic point of a curve.** Let `k` be an algebraically
closed field, `X` a curve over `k` with function field `K`, `η : Spec K ⟶ X` the canonical
morphism onto the generic point, and `𝒢` a torsion sheaf on the small étale site of `Spec K`.
Then `R^q η_* 𝒢 = 0` for every `q ≥ 2`. -/
@[weil "lem_fk105_generic_point_higher_direct_image_vanish"]
theorem isZero_rightDerived_genericPointDirectImage_of_torsion_of_isCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] (G : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).rightDerived q).obj
      G) :=
  let := functionFieldAlgebra k g
  isZero_rightDerived_genericPointDirectImage_of_torsion_of_trdeg_le_one k
    (trdeg_functionField_eq_one k g).le G hG q hq

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.BigEtaleSite

variable {k : Type u} [Field k] [IsAlgClosed k] {X : AlgebraicGeometry.Scheme.{u}}
  (g : X ⟶ Spec (.of k))
  [IsCurve k g] (B : BigEtaleSite.{u}) (hX : B.Contains X) (hK : B.Contains (Spec X.functionField))

include g in
/-- **Higher direct images from the generic point of a curve**, on the bounded small étale
sites of a big étale site `B`. Let `k` be an algebraically closed field, `X` a curve over `k`
with function field `K`, `η : Spec K ⟶ X` the canonical morphism onto the generic point, and `𝒢`
a torsion sheaf on the small étale site of `Spec K`. Then `R^q η_* 𝒢 = 0` for every `q ≥ 2`. -/
@[weil "lem_fk105_generic_point_higher_direct_image_vanish"]
theorem isZero_higherDirectImage_genericPointHom_of_isTorsionSheaf
    (G : Sheaf (SmallEtale.topology B (Spec X.functionField) hK) AddCommGrpCat.{u + 1})
    (hG : SmallEtale.IsTorsionSheaf B (Spec X.functionField) hK G) (q : ℕ) (hq : 2 ≤ q) :
    IsZero ((higherDirectImage.{u + 1} B (genericPointHom X B hX hK) q).obj G) := by
  let EK := SmallEtale.sheafEquiv B (Spec X.functionField) hK AddCommGrpCat.{u + 1}
  let EX := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have hG' : Stacks.Torsion.torsionSheafProperty _ (EK.functor.obj G) :=
    (SmallEtale.torsionSheafProperty_toEtaleSite_iff B _ hK _).1
      ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso (EK.unitIso.app G) hG)
  have h0 :=
    Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_of_torsion_of_isCurve
    g _ hG' q hq
  have e := (etaleAbelianHigherDirectImageIso.{u, 0} B (genericPointHom X B hX hK) q).app
    (EK.functor.obj G)
  have h1 := h0.of_iso e.symm
  have h2 := (EX.inverse.map_isZero h1).of_iso (EX.unitIso.app _)
  exact h2.of_iso ((higherDirectImage.{u + 1} B _ q).mapIso (EK.unitIso.app G))

end AlgebraicGeometry.BigEtaleSite

