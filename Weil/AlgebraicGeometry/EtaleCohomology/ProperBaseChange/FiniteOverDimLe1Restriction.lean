module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperStrictlyHenselianFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineGeometricFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import Weil.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomologyBijective
public import Weil.AlgebraicGeometry.Sites.Bridges.ConstantSheaf
public import Weil.Attr

/-!
# Restriction to the closed fibre over a strictly henselian local ring

Let `A` be a strictly henselian local ring, `f : X ⟶ Spec A` a proper morphism, `X₀` its closed
fibre and `i : X₀ ⟶ X` the inclusion. For every abelian sheaf `F` on the small étale site of `X`
killed by a positive integer `ℓ`, the restriction map `i^* : H^q(X, F) ⟶ H^q(X₀, i^* F)` is
bijective in every degree `q`.

The proof is the first paragraph of the proof of the proper base change theorem
([Stacks, Tag 095T]): by dimension shifting
(`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective`) it is
enough that the restriction `i^* J` of every injective sheaf of `ℤ/ℓℤ`-modules `J` on `X` has
vanishing higher cohomology on `X₀`. Since `J` has vanishing higher cohomology on `X`
([Stacks, Tag 03FD]), this follows from the comparison, for a torsion sheaf `G` on `X`, of the
vanishing of `H^q(X, G)` and of `H^q(X₀, i^* G)`:

* `H^q(X, G) ≅ H^q(X_Ω, G|_{X_Ω})` for the geometric closed fibre `X_Ω = X ×_{Spec A} Spec Ω`,
  `Ω` an algebraic closure of the residue field `k` of `A`: both are the stalk of `R^q f_* G` at
  the closed geometric point, by [Stacks, Tag 03Q9] over a strictly henselian base and by proper
  base change ([Stacks, Tag 0DDF]);
* `X_Ω ⟶ X₀` is the base change of `Spec Ω ⟶ Spec k`, a universal homeomorphism since `k` is
  separably closed and `Ω / k` purely inseparable, so it induces bijections on étale cohomology
  ([Stacks, Tag 03SI]).

The result is then transported to the small étale sites `AlgebraicGeometry.SmallEtale` of a big
étale site along the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv`, and specialized to the
sheaves `⨁ⱼ pⱼ_* (ℤ/nℤ)_{X'ⱼ}`.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_closedFibre_of_subsingleton`: for a torsion sheaf `G`
  on `X`, vanishing of `H^q(X, G)` implies vanishing of `H^q(X₀, i^* G)`.
* `AlgebraicGeometry.bijective_etaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero`:
  restriction to the closed fibre is bijective in every degree on sheaves killed by `ℓ > 0`.
* `AlgebraicGeometry.surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero`:
  the same surjectivity on the small étale sites of a big étale site.
* `bijective_zero_and_surjective_smallEtaleRestriction_closedFibre_of_iso_biproduct`
  : for `F ≅ ⨁ⱼ pⱼ_* (ℤ/nℤ)_{X'ⱼ}`, restriction `H^ν(X, F) ⟶ H^ν(X₀, i^* F)` is bijective for
  `ν = 0` and surjective for `ν > 0`.

## Implementation notes

Freitag and Kiehl state the last result for `A` noetherian, `n` invertible in `A`, `f`
projective, the `pⱼ : X'ⱼ ⟶ X` finite and `dim X₀ ≤ 1`, and prove it by reduction to the
constant sheaf on each `X'ⱼ`. None of these hypotheses is used here: the argument above needs
only that `A` is strictly henselian, `f` proper and `F` killed by a positive integer. The constant
sheaf `(ℤ/nℤ)_{X'ⱼ}` is the sheaf of locally constant `ℤ/nℤ`-valued maps
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale`), and the
direct image is `AlgebraicGeometry.BigEtaleSite.smallPushforward`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

/- FK's
hypotheses (A noetherian, n invertible, f projective, p_j finite, dim X_s ≤ 1) are dropped; f is
proper, A strictly henselian, n > 0. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Cohomology.ZModSheaf Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry

section MathlibSite

variable (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **Vanishing of cohomology passes to the closed fibre.** Let `A` be a strictly henselian local
ring, `f : X ⟶ Spec A` proper and `i : X₀ ⟶ X` the inclusion of the closed fibre. For a torsion
abelian sheaf `G` on `X`, if `H^q(X, G) = 0` then `H^q(X₀, i^* G) = 0`. -/
theorem subsingleton_sheafH_closedFibre_of_subsingleton
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ)
    (hq : Subsingleton (Sheaf.H.{u + 1} G q)) :
    Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (closedFibreInclusion A f)).obj G) q) := by
  let k := IsLocalRing.ResidueField A
  let Ω := AlgebraicClosure k
  have : IsPurelyInseparable k Ω :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure k Ω).mp inferInstance
  let s : Spec (.of Ω) ⟶ Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let x : Spec (.of Ω) ⟶ Spec (.of A) := s ≫ residueFieldPoint A
  have hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint A := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :=
      inferInstanceAs (IsLocalHom (IsLocalRing.residue A))
    have h0 : s default = IsLocalRing.closedPoint (IsLocalRing.ResidueField A) :=
      Subsingleton.elim (α := Spec (.of (IsLocalRing.ResidueField A))) _ _
    change residueFieldPoint A (s default) = _
    rw [h0]
    have : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A) :=
      inferInstanceAs (IsLocalRing (IsLocalRing.ResidueField A))
    exact Spec_closedPoint
  -- vanishing on the geometric closed fibre `X_Ω`, by proper base change
  have h1 := (subsingleton_sheafH_iff_geometricClosedFibre_of_isProper f x hx G hG q).1 hq
  -- `X_Ω ⟶ X₀` is a universal homeomorphism
  let i := closedFibreInclusion A f
  let π : pullback f x ⟶ closedFibre A f :=
    pullback.lift (f := f) (g := residueFieldPoint A) (pullback.fst f x) (pullback.snd f x ≫ s)
      (by simpa only [Category.assoc] using pullback.condition (f := f) (g := x))
  have hπ : π ≫ i = pullback.fst f x := pullback.lift_fst _ _ _
  have hπs : π ≫ closedFibreProjection A f = pullback.snd f x ≫ s := pullback.lift_snd _ _ _
  have hsq : IsPullback π (pullback.snd f x) (closedFibreProjection A f) s := by
    apply IsPullback.of_right (h₁₂ := i) (h₂₂ := residueFieldPoint A)
    · simpa only [hπ] using IsPullback.of_hasPullback f x
    · exact hπs
    · exact isPullback_closedFibre A f
  have : UniversalHomeomorphism π :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
      (specMap_universalHomeomorphism_of_isPurelyInseparable k Ω).universally_isHomeomorph⟩
  have hb := etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, 0, u + 1} π
    ((etaleAbelianInverseImage.{u, 0} i).obj G) q
  let e := (etaleAbelianInverseImageCompIso'.{u, 0} π i (pullback.fst f x) hπ.symm).app G
  have h2 : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} π).obj
      ((etaleAbelianInverseImage.{u, 0} i).obj G)) q) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ z : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} π).obj
        ((etaleAbelianInverseImage.{u, 0} i).obj G)) q,
        (z.comp (Ext.mk₀ e.inv) (add_zero q)).comp (Ext.mk₀ e.hom) (add_zero q) = z := by
      intro z
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id]
      exact Ext.comp_mk₀_id z
    rw [← key a, ← key b, Subsingleton.elim (a.comp (Ext.mk₀ e.inv) (add_zero q))
      (b.comp (Ext.mk₀ e.inv) (add_zero q))]
  exact hb.1.subsingleton

/-- **Restriction to the closed fibre is bijective on torsion sheaves.** Let `A` be a strictly
henselian local ring, `f : X ⟶ Spec A` proper and `i : X₀ ⟶ X` the inclusion of the closed
fibre. For every abelian sheaf `F` on `X` killed by a positive integer `ℓ` and every `q`, the
restriction map `H^q(X, F) ⟶ H^q(X₀, i^* F)` is bijective. -/
theorem bijective_etaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (closedFibre A f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    {ℓ : ℕ} (hℓ : 0 < ℓ) (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (ℓ : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion A f) F q) := by
  refine bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective A f ℓ
    (fun J _ q hq => ?_) q F hF
  refine subsingleton_sheafH_closedFibre_of_subsingleton A f _ ?_ q
    (subsingleton_H_toSheaf_of_injective J q hq)
  refine torsionSheafProperty_of_zsmul_id_eq_zero hℓ ?_
  rw [zsmul_id_eq_zero_iff]
  intro V x
  rw [natCast_zsmul]
  exact nsmul_toSheaf_eq_zero.{u + 1, u + 1} X.smallEtaleTopology ℓ J V x

/-- The exact inverse image along the inclusion of the closed fibre induces a surjection on
`Ext^q` out of the constant sheaf `ℤ` into a sheaf killed by a positive integer: the form of
`AlgebraicGeometry.bijective_etaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero`
without the constant-sheaf comparison. -/
theorem surjective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_of_zsmul_id_eq_zero
    {ℓ : ℕ} (hℓ : 0 < ℓ) (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (ℓ : ℤ) • 𝟙 F = 0) :
    Function.Surjective ((etaleAbelianInverseImage.{u, 0} (closedFibreInclusion A f)).mapExtAddHom
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q :
        Ext.{u + 1} _ _ q →+ Ext.{u + 1} _ _ q) := by
  have hS :=
    (bijective_etaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero A f hℓ q F hF).2
  let c := (etaleAbelianInverseImageConstantIso.{u, 0} (closedFibreInclusion A f)).app
    (AddCommGrpCat.of (ULift ℤ))
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

/-- **Restriction to the closed fibre is surjective on torsion sheaves**, on the small étale
sites of a big étale site. Let `A` be a strictly henselian local ring, `f : X ⟶ Spec A` proper,
`X₀` the closed fibre of `f`, contained in the big étale site `B`, and `i : X₀ ⟶ X` its
inclusion. For every abelian sheaf `F` killed by a positive integer `ℓ` and every `q`, the
restriction map `H^q(X, F) ⟶ H^q(X₀, i^* F)` is surjective. -/
theorem surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1})]
    {ℓ : ℕ} (hℓ : 0 < ℓ) (q : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : (ℓ : ℤ) • 𝟙 F = 0) :
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
  refine surjective_mapExtAddHom_etaleAbelianInverseImage_closedFibreInclusion_of_zsmul_id_eq_zero
    A f hℓ q _ ?_
  rw [← E₁.functor.map_id, ← Functor.map_zsmul, hF, Functor.map_zero]

/-- The sheaf of locally constant `ℤ/nℤ`-valued maps is killed by `n`. -/
theorem zsmul_id_locallyConstantSheafAbSmallEtale_zmod_eq_zero (Y : B.Scheme) (n : ℕ) :
    (n : ℤ) • 𝟙 (SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B Y.obj
      Y.property (ULift.{u + 1} (ZMod n))) = 0 := by
  rw [zsmul_id_eq_zero_iff]
  intro V x
  have ha : ∀ a : ULift.{u + 1} (ZMod n), (n : ℤ) • a = 0 := fun a => by
    ext
    simp
  let x' : LocallyConstant ((SmallEtale.toScheme B Y.obj Y.property).obj V.unop)
      (ULift.{u + 1} (ZMod n)) := x
  change (n : ℤ) • x' = 0
  exact LocallyConstant.ext fun y => ha (x' y)

/-- The direct image of a sheaf killed by `n` is killed by `n`. -/
theorem zsmul_id_smallPushforward_obj_eq_zero {Y : B.Scheme} (g : Y ⟶ X)
    (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) (n : ℤ)
    (hG : n • 𝟙 G = 0) :
    n • 𝟙 ((BigEtaleSite.smallPushforward B g AddCommGrpCat.{u + 1}).obj G) = 0 := by
  rw [zsmul_id_eq_zero_iff] at hG ⊢
  intro V x
  exact hG _ x

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts in
/-- **Restriction of `H^ν(X, ⨁ⱼ pⱼ_* (ℤ/nℤ))` to the closed fibre.** Let `A` be a strictly
henselian local ring, `f : X ⟶ Spec A` proper, `X₀` the closed fibre of `f`, contained in the big
étale site `B`, and `i : X₀ ⟶ X` its inclusion. Let `n > 0`, let `pⱼ : X'ⱼ ⟶ X` (`j < r`) be
morphisms of `B`, and let `F` be an abelian sheaf on the small étale site of `X` isomorphic to
`⨁ⱼ pⱼ_* (ℤ/nℤ)_{X'ⱼ}`. Then the restriction map `i^* : H^ν(X, F) ⟶ H^ν(X₀, i^* F)` is bijective
for `ν = 0` and surjective for `ν > 0`. -/
@[weil "lem_fk106_finite_over_dim_le_1_restriction"]
theorem bijective_zero_and_surjective_smallEtaleRestriction_closedFibre_of_iso_biproduct
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1})]
    {r : ℕ} (X' : Fin r → B.Scheme) (p : ∀ j, X' j ⟶ X) {n : ℕ} (hn : 0 < n)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (e : F ≅ ⨁ fun j => (BigEtaleSite.smallPushforward B (p j) AddCommGrpCat.{u + 1}).obj
      (SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B (X' j).obj
        (X' j).property (ULift.{u + 1} (ZMod n)))) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap.{w} B
        (B.closedFibreInclusion A X f hX₀) F 0) ∧
      ∀ ν : ℕ, 0 < ν → Function.Surjective (smallEtaleCohomologyRestrictionMap.{w} B
        (B.closedFibreInclusion A X f hX₀) F ν) := by
  refine ⟨bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero B A X f hX₀ F,
    fun ν _ => surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_zsmul_id_eq_zero
      B A X f hX₀ hn ν F ?_⟩
  have hsum : (n : ℤ) • 𝟙 (⨁ fun j => (BigEtaleSite.smallPushforward B (p j)
      AddCommGrpCat.{u + 1}).obj (SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale
        B (X' j).obj (X' j).property (ULift.{u + 1} (ZMod n)))) = 0 := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    rw [Preadditive.comp_zsmul, Category.comp_id, comp_zero, ← Category.id_comp (biproduct.ι _ j),
      ← Preadditive.zsmul_comp, zsmul_id_smallPushforward_obj_eq_zero B X (p j) _ _
        (zsmul_id_locallyConstantSheafAbSmallEtale_zmod_eq_zero B (X' j) n), zero_comp]
  calc (n : ℤ) • 𝟙 F = e.hom ≫ ((n : ℤ) • 𝟙 _) ≫ e.inv := by
        rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, e.hom_inv_id]
    _ = 0 := by rw [hsum, zero_comp, comp_zero]

end SmallEtale

end AlgebraicGeometry
