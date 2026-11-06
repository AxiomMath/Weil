module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Limits
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Curves.SmoothCurveHIGmVanish
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeGroupEtaleOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupTranscendenceDegreeOneVanishing
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaDescent
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.NormalSepClosedConstantDirectImage

/-!
# Higher direct images of `𝐆_m` along the generic points of a smooth curve

Let `k` be an algebraically closed field, `X` a smooth curve over `k` (separated, quasi-compact
and smooth of relative dimension one, not necessarily connected), `η_X = ∐_ξ Spec κ(ξ)` its
scheme of generic points and `j_X : η_X ⟶ X` the canonical morphism. Then

`R^i j_{X*} 𝐆_{m,η_X} = 0` for every `i > 0`.

The higher direct image is the sheafification of `V ↦ H^i(η_X ×_X V, 𝐆_m)`, so it suffices that
the derived sections of `𝐆_m` over every scheme `W` étale over `η_X` vanish in positive degree.
Such a `W` is the disjoint union of its base changes `W ×_{η_X} Spec κ(ξ)`, each étale over the
field `κ(ξ)`, hence a disjoint union of spectra of finite separable extensions `L` of `κ(ξ)`.
Each `κ(ξ)` is the function field of the irreducible component `closure {ξ}` of `X`, which is
open and a curve over `k`, so `κ(ξ)` and every such `L` have transcendence degree one over `k`,
and `H^i(Spec L, 𝐆_m) = 0` for `i > 0` by Tsen's theorem.

## Main results

* `Scheme.isZero_rightDerived_etaleSections_multiplicativeSheaf_genericPointsScheme`:
  the positive-degree derived sections of `𝐆_m` on `η_X` over any object of `(η_X)_étale`
  vanish, as soon as `H^q(Spec L, 𝐆_m) = 0` for every finite separable extension `L` of every
  residue field at a generic point.
* `AlgebraicGeometry.Scheme.subsingleton_sheafH_multiplicativeSheaf_spec_of_mem_genericPoints`:
  `H^q(Spec L, 𝐆_m) = 0` for `q ≥ 1` and every algebraic extension `L` of the residue field at
  a generic point of a smooth curve over an algebraically closed field.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_genericPointsMorphism_multiplicativeSheaf`:
  `R^q j_{X*} 𝐆_m = 0` for `q > 0` on a smooth curve over an algebraically closed field.
* `BigEtaleSite.isZero_higherDirectImage_genericPointsMorphism_multiplicativeSheaf`:
  the same on the size-bounded small étale sites of a big étale site.

## Implementation notes

Sheaves are on Mathlib's small étale sites `X.smallEtaleTopology` with coefficients in
`AddCommGrpCat.{u + 1}`, the direct image is `Stacks.EtaleCohomology.etaleAbelianDirectImage`
and `𝐆_m` is `Stacks.Kummer.multiplicativeSheaf`, the setting of the integral case
`Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_smoothCurve`
(Stacks 03RJ), which is the special case of a connected curve. A smooth curve is not assumed
connected: it is `[IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]`.

The form on the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of a big étale site
is obtained from the one on Mathlib's sites through
`AlgebraicGeometry.BigEtaleSite.etaleAbelianHigherDirectImageIso`, which conjugates the higher
direct images by the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv`; there `𝐆_m` is the
restriction of `Stacks.Kummer.multiplicativeSheaf` along that equivalence.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open Stacks.Cohomology.SheafifiedHigherDirectImage Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Derived sections of `𝐆_m` over an object pushed along an étale morphism.** Let
`j : U ⟶ X` be étale and `T` an object of `U_étale`. The derived sections of `𝐆_{m,X}` over the
`X`-scheme `T ⟶ U ⟶ X` are those of `𝐆_{m,U}` over `T`. -/
theorem isZero_rightDerived_etaleSections_multiplicativeSheaf_smallEtaleCompose
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (T : U.Etale) (q : ℕ)
    (h : IsZero ((((sheafSections U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op T)).rightDerived q).obj (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} U))) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((smallEtaleCompose j).obj T))).rightDerived q).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X)) := by
  let : PreservesFiniteColimits ((smallEtaleCompose j).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} U.smallEtaleTopology X.smallEtaleTopology) :=
    have : PreservesColimitsOfSize.{0, 0} (etaleRestriction.{u, u + 1} j) :=
      (etaleDirectImageAdj.{u, u + 1} j).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesFiniteColimits _
  let : ((smallEtaleCompose j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology).PreservesInjectiveObjects :=
    RelativeMayerVietoris.etaleRestriction_preservesInjectiveObjects.{u, u + 1} j
  exact IsZero.of_iso h
    ((pushforwardRightDerivedSectionsIso (J := U.smallEtaleTopology) (K := X.smallEtaleTopology)
      AddCommGrpCat.{u + 1} (smallEtaleCompose j) q T).symm.app _)

/-- The inclusion of a summand `Spec κ(ξ)` into the scheme of generic points is étale: it is an
open immersion. -/
instance etale_genericPointsSchemeι (X : Scheme.{u}) (η : _root_.genericPoints X) :
    Etale (X.genericPointsSchemeι η) :=
  have : IsOpenImmersion (X.genericPointsSchemeι η) :=
    inferInstanceAs (IsOpenImmersion (Sigma.ι _ η))
  inferInstance

/-- **Derived sections of `𝐆_m` on the scheme of generic points.** Let `X` be a scheme such that
`H^q(Spec L, 𝐆_m) = 0` for every finite separable extension `L` of the residue field `κ(ξ)` at
every generic point `ξ` of `X`. Then the `q`-th derived sections of `𝐆_m` on `η_X` over any
scheme étale over `η_X` vanish. -/
theorem isZero_rightDerived_etaleSections_multiplicativeSheaf_genericPointsScheme
    (X : Scheme.{u}) (W : X.genericPointsScheme.Etale) (q : ℕ) (hq : 0 < q)
    (h : ∀ (ξ : _root_.genericPoints X) (L : Type u) [Field L] [Algebra (X.residueField ξ) L]
      [Module.Finite (X.residueField ξ) L] [Algebra.IsSeparable (X.residueField ξ) L],
      Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q)) :
    IsZero ((((sheafSections X.genericPointsScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op W)).rightDerived q).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme)) := by
  let ι := X.genericPointsSchemeι
  let W' (ξ : _root_.genericPoints X) : (Spec (X.residueField ξ)).Etale :=
    Scheme.Etale.mk (pullback.snd W.hom (ι ξ))
  let U (ξ : _root_.genericPoints X) : X.genericPointsScheme.Etale :=
    (smallEtaleCompose (ι ξ)).obj (W' ξ)
  let e : W.left ≅ ∐ fun ξ => pullback W.hom (ι ξ) :=
    (isColimitCofanPullbackSigma W.hom).coconePointUniqueUpToIso (colimit.isColimit _)
  let eW : W ≅ etaleCoproduct U :=
    MorphismProperty.Over.isoMk e (by
      change e.hom ≫ Sigma.desc (fun ξ => pullback.snd W.hom (ι ξ) ≫ ι ξ) = W.hom
      rw [← cancel_epi e.inv, Iso.inv_hom_id_assoc]
      refine Sigma.hom_ext _ _ fun ξ => ?_
      rw [Sigma.ι_desc, ← pullback.condition]
      simp only [e, ← Category.assoc]
      congr 1
      exact ((isColimitCofanPullbackSigma W.hom).comp_coconePointUniqueUpToIso_inv
        (colimit.isColimit _) ⟨ξ⟩).symm)
  let S := sheafSections X.genericPointsScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
  apply IsZero.of_iso _ ((Stacks.DerivedFunctor.rightDerivedIso (S.mapIso eW.op) q).symm.app _)
  refine isZero_rightDerived_etaleCoproduct_of_components.{u, u + 1} U _ q hq fun ξ => ?_
  exact isZero_rightDerived_etaleSections_multiplicativeSheaf_smallEtaleCompose (ι ξ) (W' ξ) q
    (isZero_rightDerived_etaleSections_multiplicativeSheaf_over_field (X.residueField ξ) (W' ξ)
      q hq (h ξ))

section SmoothCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The open subscheme `U` on the irreducible closed set `closure {ξ}` has the point `ξ` as the
image of its generic point. -/
theorem opensι_genericPoint_eq_of_coe_eq_closure {X : Scheme.{u}} (ξ : X) (U : X.Opens)
    [IrreducibleSpace U] (hU : (U : Set X) = closure {ξ}) :
    U.ι (genericPoint U) = ξ := by
  have h := (genericPoint_spec U).image U.ι.continuous
  rw [Set.image_univ, Scheme.Opens.range_ι, hU, closure_closure] at h
  exact h.eq isGenericPoint_closure

/-- The function field of an irreducible open subscheme `U` maps onto the residue field of the
image of the generic point of `U`. -/
theorem exists_surjective_functionField_opens_residueField {X : Scheme.{u}} (U : X.Opens)
    [IrreducibleSpace U] (x : X) (hx : U.ι (genericPoint U) = x) :
    ∃ φ : U.toScheme.functionField ⟶ X.residueField x, Function.Surjective φ := by
  have : IsIso (U.ι.stalkMap (genericPoint U)) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι _
  refine ⟨inv (U.ι.stalkMap (genericPoint U)) ≫ (X.presheaf.stalkCongr (.of_eq hx)).hom ≫
      X.residue x, ?_⟩
  have h1 : Function.Surjective (X.residue x) := IsLocalRing.residue_surjective
  have ha : Function.Bijective (inv (U.ι.stalkMap (genericPoint U))) :=
    ConcreteCategory.bijective_of_isIso _
  have hb : Function.Bijective (X.presheaf.stalkCongr (.of_eq hx)).hom :=
    ConcreteCategory.bijective_of_isIso _
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (h1.comp hb.2).comp ha.2

include f in
/-- **The residue fields at the generic points of a smooth curve over an algebraically closed
field have vanishing positive-degree `𝐆_m`-cohomology over every algebraic extension.** Let `X`
be a smooth curve over an algebraically closed field `k` and `ξ` a generic point of `X`. Then
`H^q(Spec L, 𝐆_m) = 0` for `q ≥ 1` and every algebraic extension `L` of `κ(ξ)`: the residue
field `κ(ξ)` is the function field of the open irreducible component `closure {ξ}`, a curve over
`k`, so `L` has transcendence degree one over `k` (Tsen). -/
theorem subsingleton_sheafH_multiplicativeSheaf_spec_of_mem_genericPoints [IsAlgClosed k]
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]
    (ξ : _root_.genericPoints X) (L : Type u) [Field L] [Algebra (X.residueField ξ) L]
    [Algebra.IsAlgebraic (X.residueField ξ) L] (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hZ : closure {(ξ : X)} ∈ irreducibleComponents X := ξ.2
  have hO := isOpen_of_mem_irreducibleComponents_of_smooth f hZ
  obtain ⟨U, hUeq⟩ : ∃ U : X.Opens, (U : Set X) = closure {(ξ : X)} := ⟨⟨_, hO⟩, rfl⟩
  have hUZ : (U : Set X) ∈ irreducibleComponents X := hUeq ▸ hZ
  have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUZ.1
  have hC := isCurve_opensι_comp_of_mem_irreducibleComponents f U hUZ
  let := functionFieldAlgebra k (U.ι ≫ f)
  have hK := trdeg_functionField_eq_one k (U.ι ≫ f)
  have hu0 : U.ι (genericPoint U) = ξ := opensι_genericPoint_eq_of_coe_eq_closure ξ U hUeq
  obtain ⟨φ, hφ⟩ := exists_surjective_functionField_opens_residueField U _ hu0
  have : IsIntegral U.toScheme := hC.toIsVariety.toIsIntegral
  let : Algebra U.toScheme.functionField (X.residueField ξ) := φ.hom.toAlgebra
  have : Algebra.IsIntegral U.toScheme.functionField (X.residueField ξ) :=
    Algebra.isIntegral_of_surjective hφ
  have : Algebra.IsAlgebraic U.toScheme.functionField (X.residueField ξ) :=
    Algebra.IsIntegral.isAlgebraic
  let : Algebra U.toScheme.functionField L :=
    ((algebraMap (X.residueField ξ) L).comp (algebraMap U.toScheme.functionField _)).toAlgebra
  have : IsScalarTower U.toScheme.functionField (X.residueField ξ) L := .of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic U.toScheme.functionField L :=
    Algebra.IsAlgebraic.trans U.toScheme.functionField (X.residueField ξ) L
  exact subsingleton_sheafH_multiplicativeSheaf_spec_of_isAlgebraic k U.toScheme.functionField hK L
    q hq

/-- **FK I.5: the higher direct images of `𝐆_m` along the generic points of a smooth curve
vanish.** Let `X` be a smooth curve over an algebraically closed field `k` (separated,
quasi-compact and smooth of relative dimension one over `k`, not necessarily connected), and
`j_X : η_X ⟶ X` its scheme of generic points. Then `R^q j_{X*} 𝐆_{m,η_X} = 0` for every
`q > 0`. -/
@[weil "lem_fk105_generic_point_higher_direct_image_gm_vanish"]
theorem isZero_rightDerived_genericPointsMorphism_multiplicativeSheaf [IsAlgClosed k]
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f] (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} X.genericPointsMorphism).rightDerived q).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme)) :=
  isZero_rightDerived_smallEtalePushforward_of_affine_sections.{u, u + 1} X.genericPointsMorphism
    _ q fun _ _ =>
      isZero_rightDerived_etaleSections_multiplicativeSheaf_genericPointsScheme X _ q hq
        fun ξ L _ _ _ _ =>
          subsingleton_sheafH_multiplicativeSheaf_spec_of_mem_genericPoints f ξ L q hq

end SmoothCurve

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.BigEtaleSite

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Abelian sheaves on the size-bounded small étale site, with coefficients in
`AddCommGrpCat.{u + 1}`, form a Grothendieck abelian category. -/
theorem _root_.AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_addCommGrpCat_succ
    (B : BigEtaleSite.{u}) (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

attribute [local instance]
  AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_addCommGrpCat_succ in
/-- **FK I.5 on the size-bounded small étale sites.** Let `B` be a big étale site containing a
smooth curve `X` over an algebraically closed field `k` and its scheme of generic points `η_X`,
and `j_X : η_X ⟶ X` the canonical morphism, as a morphism of `B`. Then
`R^q j_{X*} 𝐆_{m,η_X} = 0` for every `q > 0`, where `𝐆_{m,η_X}` is the sheaf of invertible
functions on the small étale site of `η_X`. -/
@[weil "lem_fk105_generic_point_higher_direct_image_gm_vanish"]
theorem isZero_higherDirectImage_genericPointsMorphism_multiplicativeSheaf
    [IsAlgClosed k] [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]
    (B : BigEtaleSite.{u}) (hX : B.Contains X) (hη : B.Contains X.genericPointsScheme)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((BigEtaleSite.higherDirectImage.{u + 1} B
      (ObjectProperty.homMk X.genericPointsMorphism : B.obj _ hη ⟶ B.obj X hX) q).obj
        ((SmallEtale.sheafEquiv B X.genericPointsScheme hη AddCommGrpCat.{u + 1}).inverse.obj
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme))) := by
  have h := ((BigEtaleSite.etaleAbelianHigherDirectImageIso.{u, u + 1} B
    (ObjectProperty.homMk X.genericPointsMorphism : B.obj _ hη ⟶ B.obj X hX) q).app
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme))
  have hz := Scheme.isZero_rightDerived_genericPointsMorphism_multiplicativeSheaf f q hq
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  exact (E.inverse.map_isZero (hz.of_iso h.symm)).of_iso (E.unitIso.app _)

end AlgebraicGeometry.BigEtaleSite

end
