module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import Weil.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomologyBijective
public import Weil.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import Weil.Attr

/-!
# Restriction to the closed fibre over a strictly henselian local ring

Let `A` be a strictly henselian local ring with residue field `k`, `f : X ⟶ Spec A` a proper
morphism, `X₀ = X ×_{Spec A} Spec k` the closed fibre and `i : X₀ ⟶ X` its inclusion. For every
abelian sheaf `F` on the small étale site of `X` killed by an integer `n ≥ 1` (a sheaf of
`ℤ/nℤ`-modules), the restriction map `i^* : Hᵠ(X, F) ⟶ Hᵠ(X₀, i^* F)` is bijective in every
degree `q`.

The proof is that of [Stacks, Tag 0A3S] combined with the proper base change theorem. Degree zero
holds for every abelian sheaf over a henselian base. For an injective sheaf `J` of
`ℤ/ℓℤ`-modules on `X` (`ℓ ≥ 1`), the closed point `Spec k ⟶ Spec A` is a geometric point since `k`
is separably closed, and its geometric fibre is `X₀`; by the proper base change theorem in the form
of [Stacks, Tag 0DDF] (1), `Hᵠ(X₀, i^* J)` is the stalk of `Rᵠ f_* J` at this point, which vanishes
for `q > 0` since `J` has no higher direct images ([Stacks, Tag 03FD]). Dimension shifting along
embeddings of sheaves killed by `ℓ` into such injectives
(`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective`)
gives bijectivity in every degree.

As a consequence, every constructible sheaf of `ℤ/nℤ`-modules `F` on `X` admits an injective map
into a constructible sheaf of `ℤ/nℤ`-modules `G` such that restriction to the closed fibre is
bijective on `H⁰` and surjective on `Hᵠ` for `q > 0`: one may take `G = F`.

## Main results

* `AlgebraicGeometry.subsingleton_H_closedFibre_toSheaf_of_injective`: on Mathlib's small étale
  sites, the restriction to the closed fibre of an injective sheaf of `ℤ/ℓℤ`-modules has
  vanishing cohomology in positive degrees.
* `AlgebraicGeometry.bijective_etaleCohomologyRestrictionMap_closedFibre_of_nsmul`: on Mathlib's
  small étale sites, restriction to the closed fibre is bijective in every degree on sheaves
  killed by `n ≥ 1`.
* `AlgebraicGeometry.surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul`: the same
  (surjectivity) on the small étale sites `AlgebraicGeometry.SmallEtale` of a big étale site.
* `AlgebraicGeometry.exists_mono_isConstructibleAbelianSheaf_restriction_closedFibre`: every
  constructible sheaf killed by `n` embeds into a constructible sheaf killed by `n` whose
  restriction to the closed fibre is bijective on `H⁰` and surjective on `Hᵠ`, `q > 0`.

## Implementation notes

A sheaf of `ℤ/nℤ`-modules is recorded as an abelian sheaf `F` with `(n : ℤ) • 𝟙 F = 0`; a
`ℤ/nℤ`-linear map of such sheaves is a morphism of abelian sheaves, and their cohomology is that
of the underlying abelian sheaves.

Freitag and Kiehl assume `A` noetherian, `f` projective, `n` invertible in `A` and `dim X₀ ≤ 1`,
and take for `G` a finite direct sum of direct images of constant sheaves `ℤ/nℤ` along finite
morphisms, for which they prove the two cohomological properties by their own route. The proper
base change theorem gives these properties for every sheaf killed by `n` over any strictly
henselian local ring, `f` proper, with no bound on `dim X₀`, so the embedding `F ⟶ G` can be
taken to be the identity of `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1][FreitagKiehl]
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

/- FK's hypotheses (A noetherian, f projective, n invertible, dim X_s ≤ 1) are dropped; G = F. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry

section MathlibSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

/-- Abelian sheaves on a small étale site, at the coefficients `AddCommGrpCat.{u + 1}`, form a
Grothendieck abelian category; this pins the coefficient universe. -/
local instance (priority := 2000) isGrothendieckAbelian_sheaf_smallEtale_succ_closedFibre
    (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, 0} Z

variable (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **Injective `ℤ/ℓℤ`-modules restrict to acyclic sheaves on the closed fibre.** Let `A` be a
strictly henselian local ring, `f : X ⟶ Spec A` proper, `ℓ > 0` and `J` an injective sheaf of
`ℤ/ℓℤ`-modules on `X_étale`. Then `Hᵠ(X₀, J|_{X₀}) = 0` for every `q > 0`: the closed point of
`Spec A` is a geometric point, with geometric fibre `X₀`, so by [Stacks, Tag 0DDF] (1) this group
is the stalk of `Rᵠ f_* J`, and `J` has no higher direct images ([Stacks, Tag 03FD]). -/
theorem subsingleton_H_closedFibre_toSheaf_of_injective {ℓ : ℕ} (hℓ : 0 < ℓ)
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (closedFibreInclusion A f)).obj ((SheafOfModules.toSheaf _).obj J)) q) := by
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    inferInstanceAs (Field (IsLocalRing.ResidueField A))
  have : IsSepClosed (A ⧸ IsLocalRing.maximalIdeal A) :=
    inferInstanceAs (IsSepClosed (IsLocalRing.ResidueField A))
  set G := (SheafOfModules.toSheaf _).obj J
  have hG : ℓ • 𝟙 G = 0 := nsmul_id_toSheaf_eq_zero.{u, u + 1} ℓ J
  have hT := torsionSheafProperty_of_nsmul_id_eq_zero G ℓ hℓ hG
  have hR : IsZero (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj G) :=
    IsZero.of_iso
      (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, 0} f ℓ J
        q (by exact_mod_cast hq))
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
        (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
        (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective G q).symm
  let e := etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper f
    (residueFieldPoint A) G hT q
  have : (((pointSmallEtale (residueFieldPoint A)).ulift.{u + 1}).sheafFiber
    (A := AddCommGrpCat.{u + 1})).Additive := Functor.additive_of_preserves_binary_products _
  have hS := (((pointSmallEtale (residueFieldPoint A)).ulift.{u + 1}).sheafFiber
    (A := AddCommGrpCat.{u + 1})).map_isZero hR
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (hS.of_iso e.symm)

/-- **Restriction to the closed fibre is bijective on sheaves killed by `n ≥ 1`.** Let `A` be a
strictly henselian local ring, `f : X ⟶ Spec A` proper and `i : X₀ ⟶ X` the inclusion of the
closed fibre. For every abelian sheaf `F` on `X_étale` with `n • F = 0`, `n > 0`, the restriction
map `i^* : Hᵠ(X, F) ⟶ Hᵠ(X₀, i^* F)` is bijective for every `q`. -/
theorem bijective_etaleCohomologyRestrictionMap_closedFibre_of_nsmul {n : ℕ} (hn : 0 < n)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : (n : ℤ) • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion A f) F q) :=
  bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective A f n
    (fun J _ q hq ↦ subsingleton_H_closedFibre_toSheaf_of_injective A f hn J q hq) q F hF

/-- On Mathlib's small étale sites, the exact inverse image along the inclusion of the closed
fibre induces a surjection on `Extᵠ` out of the constant sheaf `ℤ` into every sheaf killed by
`n ≥ 1`. -/
theorem surjective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_of_nsmul
    {n : ℕ} (hn : 0 < n) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) (q : ℕ) :
    Function.Surjective ((etaleAbelianInverseImage.{u, 0}
        (closedFibreInclusion A f)).mapExtAddHom
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q :
        Ext.{u + 1} _ _ q →+ Ext.{u + 1} _ _ q) := by
  have hS := (bijective_etaleCohomologyRestrictionMap_closedFibre_of_nsmul A f hn F hF q).2
  let c := (etaleAbelianInverseImageConstantIso.{u, 0}
    (closedFibreInclusion A f)).app (AddCommGrpCat.of (ULift ℤ))
  intro y
  obtain ⟨x, hx⟩ := hS ((Ext.mk₀ c.inv).comp y (zero_add q))
  refine ⟨x, ?_⟩
  rw [etaleCohomologyRestrictionMap_apply] at hx
  have h2 := congrArg (fun z => (Ext.mk₀ c.hom).comp z (zero_add q)) hx
  simp only [Ext.mk₀_comp_mk₀_assoc, c, Iso.hom_inv_id, Ext.mk₀_id_comp] at h2
  exact h2

end MathlibSite

section SmallEtale

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A]
  (X : B.Scheme) (f : X.obj ⟶ Spec (.of A)) [IsProper f]
  (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f))
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
    AddCommGrpCat.{u + 1})]

/-- **Restriction to the closed fibre is surjective on sheaves killed by `n ≥ 1`.** Let `A` be a
strictly henselian local ring, `f : X ⟶ Spec A` proper, `X₀` the closed fibre, contained in the
big étale site `B`, and `i : X₀ ⟶ X` its inclusion. For every abelian sheaf `F` on the small
étale site of `X` with `n • F = 0`, `n > 0`, the restriction map `i^* : Hᵠ(X, F) ⟶ Hᵠ(X₀, i^* F)`
is surjective for every `q`. -/
theorem surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul {n : ℕ} (hn : 0 < n)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) (q : ℕ) :
    Function.Surjective (smallEtaleCohomologyRestrictionMap.{w} B
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
  suffices hs : Function.Surjective ((smallEtaleInverseImage B i AddCommGrpCat.{u + 1}).mapExtAddHom
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q : Ext.{w} _ _ q →+ Ext.{w} _ _ q) by
    intro y
    obtain ⟨x, hx⟩ := hs ((Ext.mk₀ c.hom).comp y (zero_add q))
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
    (smallEtaleInverseImage B i AddCommGrpCat.{u + 1}) F₂ E₁ E₂ α _ _ q ?_
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  let κ := equivCommuteConstant (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
    X.obj.smallEtaleTopology (SmallEtale.toEtaleSite B X.obj X.property)
    (SmallEtale.finalIsTerminal B X.obj X.property) (MorphismProperty.Over.mkIdTerminal _ _)
  refine surjective_mapExtAddHom_of_iso.{u + 1, u + 1} F₂ (κ.app _) (Iso.refl _) q ?_
  have hF' : (n : ℤ) • 𝟙 (E₁.functor.obj F) = 0 := by
    rw [← E₁.functor.map_id, ← Functor.map_zsmul, hF, Functor.map_zero]
  exact surjective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_of_nsmul A f hn
    (E₁.functor.obj F) hF' q

variable [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Constructible sheaves embed into sheaves with good restriction to the closed fibre.** Let
`A` be a strictly henselian local ring, `f : X ⟶ Spec A` proper, `X₀` the closed fibre, contained
in the big étale site `B`, and `i : X₀ ⟶ X` its inclusion. Every constructible abelian sheaf `F`
on the small étale site of `X` killed by `n ≥ 1` (a constructible sheaf of `ℤ/nℤ`-modules) admits
a monomorphism `F ⟶ G` into a constructible sheaf `G` killed by `n` such that
`i^* : H⁰(X, G) ⟶ H⁰(X₀, i^* G)` is bijective and `i^* : Hᵠ(X, G) ⟶ Hᵠ(X₀, i^* G)` is surjective
for every `q > 0`. -/
@[weil "lem_fk106_constructible_embeds_in_good_sheaf"]
theorem exists_mono_isConstructibleAbelianSheaf_restriction_closedFibre {n : ℕ} (hn : 0 < n)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) (hFc : IsConstructibleAbelianSheaf B X F) :
    ∃ (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (φ : F ⟶ G),
      Mono φ ∧ IsConstructibleAbelianSheaf B X G ∧ (n : ℤ) • 𝟙 G = 0 ∧
      Function.Bijective
        (smallEtaleCohomologyRestrictionMap.{w} B (B.closedFibreInclusion A X f hX₀) G 0) ∧
      ∀ q, 0 < q → Function.Surjective
        (smallEtaleCohomologyRestrictionMap.{w} B (B.closedFibreInclusion A X f hX₀) G q) :=
  ⟨F, 𝟙 F, inferInstance, hFc, hF,
    bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero B A X f hX₀ F,
    fun q _ ↦ surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul B A X f hX₀ hn
      F hF q⟩

end SmallEtale

end AlgebraicGeometry
