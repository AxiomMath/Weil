module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLevelExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import Weil.Attr

/-!
# The levels of `H^ν(X_k̄, ℤ_ℓ)` as étale cohomology of the geometric fibre

Let `X` be a scheme proper over a field `k`, `k̄` an extension field of `k` and `ℓ` a prime. The
ℓ-adic cohomology `H^ν(X_k̄, ℚ_ℓ) = ℚ_ℓ ⊗ limₙ H^ν(X_k̄, ℤ/ℓⁿ⁺¹)` of `Weil.rationalCohomology` is
Stacks' `Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomology` for the
constant ℓ-adic sheaf, the compactification `id_X` and the closure `k̄`: the extension of scalars to
`ℚ_ℓ` of the limit of the inverse system
`n ↦ H^ν_c(X_k̄, (ℤ_ℓ)ₙ)`
(`Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologySystem`).

This file identifies that inverse system, as a system of abelian groups, with the system
`n ↦ H^ν(X_k̄, ℤ/ℓⁿ⁺¹)` of Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H` of the constant
abelian sheaves `ℤ/ℓⁿ⁺¹` on Mathlib's small étale site of the geometric fibre
`X_k̄ = X ×_{Spec k} Spec k̄` (`Stacks.Frobenius.fieldBaseChange`), with the maps induced by the
reductions `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`.

The proof has three steps.

* Since `id_X` compactifies `X`, `H^ν_c(X_k̄, K) = Ext^ν(ℤ_ℓ, K|_{X_k̄})` in sheaves of
  `ℤ_ℓ`-modules on `X_k̄`, naturally in `K`
  (`Stacks.EtaleCohomology.extConstantAddEquivCompactSupportCohomology`).
* `Ext^ν` of sheaves of `ℤ_ℓ`-modules out of the constant sheaf is the cohomology of the
  underlying abelian sheaf, naturally (`Stacks.EtaleCohomology.extForgetSheafHAddEquiv`, Stacks
  Tag 03FD).
* The abelian sheaf underlying `(ℤ_ℓ)ₙ|_{X_k̄}` is the constant sheaf `ℤ/ℓⁿ⁺¹`, by an isomorphism
  sending `1` to the image of the generator of `(ℤ_ℓ)ₙ`
  (`Weil.geometricConstantPadicLevelIso`). Since the transitions of `ℤ_ℓ` carry generator to
  generator, these isomorphisms carry the transitions to the reductions
  (`Weil.geometricConstantPadicLevelIso_hom_naturality`).

## Main definitions

* `Weil.geometricConstantPadicLevelIso`: `ℤ/ℓⁿ⁺¹_{X_k̄} ≅ (ℤ_ℓ)ₙ|_{X_k̄}` as abelian sheaves.
* `Weil.geometricConstantLevelCohomologyAddEquiv`:
  `H^ν_c(X_k̄, (ℤ_ℓ)ₙ) ≃+ Sheaf.H (ℤ/ℓⁿ⁺¹_{X_k̄}) ν`.
* `Weil.uliftZModSystem`: the inverse system `n ↦ ℤ/ℓⁿ⁺¹` with the reductions.
* `Weil.geometricConstantLevelCohomologySystemIso`: the isomorphism of inverse systems of abelian
  groups `(n ↦ H^ν_c(X_k̄, (ℤ_ℓ)ₙ)) ≅ (n ↦ H^ν(X_k̄, ℤ/ℓⁿ⁺¹))`.

## Main results

* `Weil.geometricConstantLevelCohomologyAddEquiv_transition`: the transitions correspond to the
  maps induced by the reductions `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`.

## Implementation notes

The identification of the levels is pinned down by the generators: the constant system of
`Stacks.EtaleCohomology.LAdicSheaf.constantSystem` has as level `n` the sheaf `j_!` of the constant
sheaf `ℤ/ℓⁿ⁺¹` along the final object, which corepresents sections over the final object, as does
the constant sheaf. The isomorphism `ℤ/ℓⁿ⁺¹_X ⟶ (ℤ_ℓ)ₙ` used here is the one sending `1` to the
generator, so its compatibility with the transitions is the statement that the transitions carry
generator to generator. (Stacks' `Stacks.EtaleCohomology.LAdicSheaf.constantLevelCohomologyAddEquiv`
uses an isomorphism obtained from cokernels, compatible with the transitions only up to an
automorphism of `ℤ/ℓⁿ⁺¹`.)

The cohomology `Sheaf.H` is taken for any `HasExt` structure on abelian sheaves of `X_k̄`, so the
results specialise to `CategoryTheory.IsGrothendieckAbelian.hasExt`.

## References

* [Stacks Project, Tag 03UT](https://stacks.math.columbia.edu/tag/03UT)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.EtaleCohomology Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace Weil

section General

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

variable (R : Type) [CommRing R]

/-- The generator of `j_!` of the constant sheaf `R` along the final object, read on Mathlib's
small étale site over the final object `X ⟶ X`. -/
noncomputable def sheafEquivShriekFinalSection :
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)).functor.obj
      (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property))).obj.obj
        (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property))) :=
  (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)).unit.app
    (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property))).hom.app
      (op (final B X.1 X.property))).hom
    (moduleShriekConstantGenerator B X R (final B X.1 X.property))

/-- A morphism out of `j_!` of the constant sheaf `R` along the final object, read on Mathlib's
small étale site, is determined by, and determines, its value on the generator. -/
theorem bijective_eval_sheafEquivShriekFinalSection
    (H : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Function.Bijective (fun φ : (SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} R)).functor.obj
      (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)) ⟶ H =>
        (φ.hom.app (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
          (sheafEquivShriekFinalSection B X R)) := by
  let E := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)
  have h : (fun φ : E.functor.obj
      (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)) ⟶ H =>
        (φ.hom.app (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
          (sheafEquivShriekFinalSection B X R)) =
      (moduleShriekConstantSectionEquiv.{u, 0, 0} B X R (final B X.1 X.property)
        (E.inverse.obj H)) ∘ (E.toAdjunction.homEquiv _ _) := by
    funext φ
    simp only [Function.comp_apply]
    rw [moduleShriekConstantSectionEquiv_apply, Adjunction.homEquiv_unit]
    rfl
  rw [h]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

/-- The morphism from the constant sheaf `R_X` of `R`-modules on Mathlib's small étale site to
`j_!` of the constant sheaf along the final object which sends `1` to the generator. -/
noncomputable def constantToSheafEquivShriekFinal :
    Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} R X.1.smallEtaleTopology ⟶
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)).functor.obj
        (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)) :=
  ((constantSheafAdj X.1.smallEtaleTopology (ModuleCat.{u + 1} R)
    (isTerminal_toEtaleSite_final B X.1 X.property)).homEquiv _ _).symm
    ((Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} R _).symm
      (sheafEquivShriekFinalSection B X R))

/-- Composing with `constantToSheafEquivShriekFinal` and taking the value at `1` is taking the value
at the generator. -/
theorem constantToSheafEquivShriekFinal_comp_eval
    (H : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (φ : (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)).functor.obj
        (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)) ⟶ H) :
    Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} R _
      ((constantSheafAdj X.1.smallEtaleTopology (ModuleCat.{u + 1} R)
        (isTerminal_toEtaleSite_final B X.1 X.property)).homEquiv _ _
          (constantToSheafEquivShriekFinal B X R ≫ φ)) =
      (φ.hom.app (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
          (sheafEquivShriekFinalSection B X R) := by
  rw [Adjunction.homEquiv_naturality_right, constantToSheafEquivShriekFinal, Equiv.apply_symm_apply]
  change (φ.hom.app (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
    (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} R _
      ((Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} R _).symm
        (sheafEquivShriekFinalSection B X R))) = _
  rw [AddEquiv.apply_symm_apply]

/-- `R_X ⟶ j_! R` (`1 ↦` the generator) is an isomorphism: both objects corepresent the sections
over the final object. -/
instance isIso_constantToSheafEquivShriekFinal : IsIso (constantToSheafEquivShriekFinal B X R) := by
  refine isIso_of_coyoneda_map_bijective _ (fun H => ?_)
  have h : (fun φ => constantToSheafEquivShriekFinal B X R ≫ φ) =
      (((constantSheafAdj X.1.smallEtaleTopology (ModuleCat.{u + 1} R)
        (isTerminal_toEtaleSite_final B X.1 X.property)).homEquiv _ H).trans
          (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} R _).toEquiv).symm ∘
      (fun φ : (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)).functor.obj
          (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)) ⟶ H =>
        (φ.hom.app (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
          (sheafEquivShriekFinalSection B X R)) := by
    funext φ
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply]
    exact constantToSheafEquivShriekFinal_comp_eval B X R H φ
  rw [h]
  exact (Equiv.bijective _).comp (bijective_eval_sheafEquivShriekFinalSection B X R H)


variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- Restriction of scalars commutes with reading a sheaf of the small étale site of Stacks 021B on
Mathlib's small étale site, through the unit and counit of `AlgebraicGeometry.SmallEtale.sheafEquiv`
(so that its effect on sections is `restrictScalarsSheafEquivObjIso_hom_unit`). -/
noncomputable def restrictScalarsSheafEquivObjIso
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ')) :
    (etaleModuleRestrictScalars ρ X.1).obj
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ')).functor.obj F) ≅
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.obj
        ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).obj F) :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).counitIso.symm.app _ ≪≫
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.mapIso
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).mapIso
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ')).unitIso.symm.app F))

/-- `restrictScalarsSheafEquivObjIso` carries the image of a section under the unit of the
equivalence for `Λ'` to its image under the unit of the equivalence for `Λ`. -/
theorem restrictScalarsSheafEquivObjIso_hom_unit
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ'))
    (V : SmallEtale B X.1 X.property) (x : F.obj.obj (op V)) :
    ((restrictScalarsSheafEquivObjIso B X ρ F).hom.hom.app
      (op ((toEtaleSite B X.1 X.property).obj V))).hom
        ((((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ')).unit.app F).hom.app
          (op V)).hom x) =
      ((((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).unit.app
          ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).obj F)).hom.app (op V)).hom
            x) := by
  let E := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)
  let E' := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ')
  let R := sheafCompose (SmallEtale.topology B X.1 X.property) (ModuleCat.restrictScalars.{u + 1} ρ)
  let φ : E.inverse.obj ((etaleModuleRestrictScalars ρ X.1).obj (E'.functor.obj F)) ⟶ R.obj F :=
    R.map (E'.unitIso.inv.app F)
  have key : E.inverse.map (restrictScalarsSheafEquivObjIso B X ρ F).hom =
      φ ≫ E.unit.app (R.obj F) := by
    change E.inverse.map (E.counitInv.app _ ≫ E.functor.map φ) = _
    rw [Functor.map_comp, ← Equivalence.unit_app_inverse]
    exact (E.unit.naturality φ).symm
  have h := congrArg (fun g => (g.hom.app (op V)).hom
    (((E'.unit.app F).hom.app (op V)).hom x)) key
  refine h.trans ?_
  change ((E.unit.app (R.obj F)).hom.app (op V)).hom
    (((E'.unitIso.inv.app F).hom.app (op V)).hom (((E'.unit.app F).hom.app (op V)).hom x)) = _
  congr 1
  change ((E'.unit.app F ≫ E'.unitIso.inv.app F).hom.app (op V)).hom x = x
  rw [show E'.unit.app F ≫ E'.unitIso.inv.app F = 𝟙 F from E'.unitIso.hom_inv_id_app F]
  rfl

end General

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **The unit section of the level `n` of `ℤ_ℓ`.** The level `n` of the constant ℓ-adic sheaf,
a sheaf of `ℤ_ℓ`-modules on the small étale site of Stacks 021B, is `j_!` of the constant sheaf
`ℤ/ℓⁿ⁺¹` along the final object, and has a generator over the final object
(`AlgebraicGeometry.moduleShriekConstantGenerator`); this is its image on Mathlib's small étale
site, over the final object `X ⟶ X`. -/
noncomputable def constantPadicLevelSection (n : ℕ) :
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
      (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).obj.obj
        (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property))) :=
  (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).unit.app
    (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).hom.app
      (op (final B X.1 X.property))).hom
    (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) (final B X.1 X.property))

/-- The transition map of `ℤ_ℓ` carries the unit section at level `n + 1` to the unit section at
level `n`. -/
theorem padicTransition_constantPadicLevelSection (n : ℕ) :
    (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).hom.app
        (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
      (constantPadicLevelSection B X ℓ (n + 1)) = constantPadicLevelSection B X ℓ n := by
  have h := (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).unit.naturality
    (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)
  have h' := congrArg (fun φ => (φ.hom.app (op (final B X.1 X.property))).hom
    (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) (final B X.1 X.property))) h
  change (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).unit.app
      (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).hom.app
        (op (final B X.1 X.property))).hom
      (((LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n).hom.app
        (op (final B X.1 X.property))).hom
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) (final B X.1 X.property))) =
    (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).hom.app
        (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
      (constantPadicLevelSection B X ℓ (n + 1)) at h'
  refine h'.symm.trans ?_
  unfold constantPadicLevelSection
  exact congrArg (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).unit.app
      (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).hom.app
        (op (final B X.1 X.property))).hom
    (LAdicSheaf.shriekConstantTransition_generator B X ℓ _ n)

section Abelian

/-- Additive maps out of `ℤ/N` agree when they agree at `1`. -/
theorem uliftZMod_hom_ext {N : ℕ} {A : AddCommGrpCat.{u + 1}}
    (f g : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).obj
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) ⟶ A)
    (h : f.hom (ULift.up 1) = g.hom (ULift.up 1)) : f = g := by
  ext ⟨x⟩
  have hx : (ULift.up x : ULift.{u + 1} (ZMod N)) = ((x.cast : ℤ)) • ULift.up 1 := by
    apply ULift.ext
    change x = ((x.cast : ℤ)) • (1 : ZMod N)
    rw [zsmul_eq_mul, mul_one, ZMod.intCast_zmod_cast]
  change f.hom (ULift.up x) = g.hom (ULift.up x)
  rw [hx, map_zsmul, map_zsmul, h]

/-- The reduction `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`, on the lifted groups. -/
noncomputable def uliftZModPowReduction (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) AddCommGrpCat.{u + 1}).obj
        (ModuleCat.of (ZMod (ℓ ^ (n + 1 + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))) ⟶
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}).obj
        (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) :=
  AddCommGrpCat.ofHom
    { toFun := fun x => ULift.up (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
        (ZMod (ℓ ^ (n + 1))) x.down)
      map_zero' := ULift.ext _ _ (map_zero _)
      map_add' := fun x y => ULift.ext _ _ (map_add _ x.down y.down) }

/-- **The inverse system `n ↦ ℤ/ℓⁿ⁺¹`** of abelian groups, with the reductions. -/
noncomputable def uliftZModSystem : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n => AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))
    (uliftZModPowReduction.{u} ℓ)

omit [Fact ℓ.Prime] in
/-- The map of `uliftZModSystem` from `n + 1` to `n` is the reduction. -/
@[simp]
theorem uliftZModSystem_map_succ (n : ℕ) :
    (uliftZModSystem.{u} ℓ).map (homOfLE (n.le_add_right 1)).op = uliftZModPowReduction.{u} ℓ n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The level `n` of `ℤ_ℓ` on `X` is the constant sheaf `ℤ/ℓⁿ⁺¹`**, as abelian sheaves on
Mathlib's small étale site, by the isomorphism sending `1` to the unit section
(`constantPadicLevelIso_hom_one`). -/
noncomputable def constantPadicLevelIso (n : ℕ) :
    (constantSheaf X.1.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}).obj
          (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))) ≅
      (etaleModuleUnderlyingAbelian X.1 ℤ_[ℓ]).obj
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod (ℓ ^ (n + 1)))
      X.1.smallEtaleTopology).symm.app
      (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) ≪≫
    (etaleModuleUnderlyingAbelian X.1 (ZMod (ℓ ^ (n + 1)))).mapIso
      (asIso (constantToSheafEquivShriekFinal B X (ZMod (ℓ ^ (n + 1))))) ≪≫
    (etaleModuleUnderlyingAbelian X.1 ℤ_[ℓ]).mapIso
      (restrictScalarsSheafEquivObjIso B X (PadicInt.toZModPow (n + 1))
        ((LAdicSheaf.constantSystem B X ℓ).level n))

/-- `constantPadicLevelIso` sends `1` to the unit section `constantPadicLevelSection`. -/
theorem constantPadicLevelIso_hom_one (n : ℕ) :
    (((constantSheafAdj X.1.smallEtaleTopology AddCommGrpCat.{u + 1}
      (isTerminal_toEtaleSite_final B X.1 X.property)).homEquiv _ _
        (constantPadicLevelIso B X ℓ n).hom).hom
        (ULift.up 1)) = constantPadicLevelSection B X ℓ n := by
  let hT := isTerminal_toEtaleSite_final B X.1 X.property
  let Λ := ZMod (ℓ ^ (n + 1))
  let a := constantToSheafEquivShriekFinal B X Λ
  let adj := constantSheafAdj X.1.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  let f₁ := (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ X.1.smallEtaleTopology).inv.app
      (ModuleCat.of Λ (ULift.{u + 1} Λ)) ≫ (etaleModuleUnderlyingAbelian X.1 Λ).map a
  let c := restrictScalarsSheafEquivObjIso B X (PadicInt.toZModPow (n + 1))
          ((LAdicSheaf.constantSystem B X ℓ).level n)
  let g₁ : (etaleModuleUnderlyingAbelian X.1 Λ).obj ((SmallEtale.sheafEquiv B X.1 X.property
      (ModuleCat.{u + 1} Λ)).functor.obj (moduleShriekConstant.{u, 0, 0} B X Λ
        (final B X.1 X.property))) ⟶ _ := (etaleModuleUnderlyingAbelian X.1 ℤ_[ℓ]).map c.hom
  have h₃ := congrArg (fun f => f.hom (ULift.up 1)) (adj.homEquiv_naturality_right f₁ g₁)
  refine h₃.trans ?_
  have h₁ := etaleModuleUnderlyingAbelianConstantMap_comp_map Λ X.1 hT a
  have h₂ : uliftIntToULiftHom Λ ≫ adj.homEquiv _ _ f₁ =
      uliftIntToULiftHom Λ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((etaleModuleConstantAdj Λ X.1 hT).homEquiv _ _ a) := by
    rw [← adj.homEquiv_naturality_left]
    have e : (constantSheaf X.1.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (uliftIntToULiftHom Λ) ≫ f₁ =
        etaleModuleUnderlyingAbelianConstantMap Λ X.1 ≫
          (etaleModuleUnderlyingAbelian X.1 Λ).map a :=
      (Category.assoc _ _ _).symm
    rw [e, h₁]
    exact Equiv.apply_symm_apply _ _
  have hg : (uliftIntToULiftHom Λ).hom (ULift.up 1) = ULift.up 1 :=
    ULift.ext _ _ (one_zsmul _)
  replace h₂ := congrArg (fun f => f.hom (ULift.up 1)) h₂
  change (adj.homEquiv _ _ f₁).hom ((uliftIntToULiftHom Λ).hom (ULift.up 1)) =
    ((etaleModuleConstantAdj Λ X.1 hT).homEquiv _ _ a).hom
      ((uliftIntToULiftHom Λ).hom (ULift.up 1)) at h₂
  rw [hg] at h₂
  change (c.hom.hom.app _).hom ((adj.homEquiv _ _ f₁).hom (ULift.up 1)) = _
  rw [h₂]
  have ha : ((etaleModuleConstantAdj Λ X.1 hT).homEquiv _ _ a).hom (ULift.up 1) =
      sheafEquivShriekFinalSection B X Λ := by
    change Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ _
      (((constantSheafAdj X.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _ _)
        (((constantSheafAdj X.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _ _).symm
          ((Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ _).symm
            (sheafEquivShriekFinalSection B X Λ)))) = _
    rw [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rw [ha]
  exact restrictScalarsSheafEquivObjIso_hom_unit B X (PadicInt.toZModPow (n + 1))
    ((LAdicSheaf.constantSystem B X ℓ).level n) (final B X.1 X.property)
    (moduleShriekConstantGenerator B X Λ (final B X.1 X.property))

/-- **The transitions of `ℤ_ℓ` on `X` are the reductions `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`.** -/
theorem constantPadicLevelIso_hom_naturality (n : ℕ) :
    (constantSheaf X.1.smallEtaleTopology AddCommGrpCat.{u + 1}).map (uliftZModPowReduction ℓ n) ≫
        (constantPadicLevelIso B X ℓ n).hom =
      (constantPadicLevelIso B X ℓ (n + 1)).hom ≫ (etaleModuleUnderlyingAbelian X.1 ℤ_[ℓ]).map
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
          (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) := by
  let adj := constantSheafAdj X.1.smallEtaleTopology AddCommGrpCat.{u + 1}
    (isTerminal_toEtaleSite_final B X.1 X.property)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  apply uliftZMod_hom_ext
  have hr : (uliftZModPowReduction ℓ n).hom (ULift.up 1) = ULift.up 1 := ULift.ext _ _ (map_one _)
  change (adj.homEquiv _ _ (constantPadicLevelIso B X ℓ n).hom).hom
      ((uliftZModPowReduction ℓ n).hom (ULift.up 1)) =
    (((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)).hom.app
        (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property)))).hom
      ((adj.homEquiv _ _ (constantPadicLevelIso B X ℓ (n + 1)).hom).hom (ULift.up 1))
  rw [hr, constantPadicLevelIso_hom_one, constantPadicLevelIso_hom_one]
  exact (padicTransition_constantPadicLevelSection B X ℓ n).symm

end Abelian

section GeometricFibre

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The level `n` of `ℤ_ℓ` restricted to the geometric fibre `X_k̄ = X ×_k k̄` is the constant
sheaf `ℤ/ℓⁿ⁺¹`**, as abelian sheaves on Mathlib's small étale site of `X_k̄`: the inverse image of
`constantPadicLevelIso`. -/
noncomputable def geometricConstantPadicLevelIso (n : ℕ) :
    (constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}).obj
          (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))) ≅
      (etaleModuleUnderlyingAbelian (fieldBaseChange (Over.mk f) kbar) ℤ_[ℓ]).obj
        ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
            (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n))) :=
  (etaleAbelianInverseImageConstantIso.{u, 0} (fieldBaseChangeProj (Over.mk f) kbar)).symm.app _ ≪≫
    (etaleAbelianInverseImage.{u, 0} (fieldBaseChangeProj (Over.mk f) kbar)).mapIso
      (constantPadicLevelIso B X ℓ n) ≪≫
    (etaleModuleUnderlyingAbelianInverseImageIso ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).app _

/-- **The transitions of `ℤ_ℓ` on `X_k̄` are the reductions `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`.** -/
theorem geometricConstantPadicLevelIso_hom_naturality (n : ℕ) :
    (constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (uliftZModPowReduction ℓ n) ≫ (geometricConstantPadicLevelIso B X ℓ f kbar n).hom =
      (geometricConstantPadicLevelIso B X ℓ f kbar (n + 1)).hom ≫
        (etaleModuleUnderlyingAbelian (fieldBaseChange (Over.mk f) kbar) ℤ_[ℓ]).map
          ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
              (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n))) := by
  have h₁ := (etaleAbelianInverseImageConstantIso.{u, 0}
    (fieldBaseChangeProj (Over.mk f) kbar)).inv.naturality (uliftZModPowReduction ℓ n)
  have h₃ := (etaleModuleUnderlyingAbelianInverseImageIso ℤ_[ℓ]
    (fieldBaseChangeProj (Over.mk f) kbar)).hom.naturality
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n))
  dsimp only [Functor.comp_map] at h₁ h₃
  simp only [geometricConstantPadicLevelIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc]
  erw [constantPadicLevelIso_hom_naturality B X ℓ n]
  rw [Functor.map_comp_assoc]
  erw [h₃]


variable [IsProper f]

/-- Post-composition with an isomorphism, on `Ext`. -/
noncomputable def extPostcompAddEquiv {C : Type*} [Category* C] [Abelian C] [HasExt.{u + 1} C]
    {A M M' : C} (e : M ≅ M') (n : ℕ) : Ext.{u + 1} A M n ≃+ Ext.{u + 1} A M' n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun y := y.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  right_inv y := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]
  map_add' x y := Ext.add_comp _ _ _ _

/-- `extPostcompAddEquiv` turns composition with `g` into composition with `r` when
`g ≫ e₂ = e₁ ≫ r`. -/
theorem extPostcompAddEquiv_comp_mk₀ {C : Type*} [Category* C] [Abelian C] [HasExt.{u + 1} C]
    {A M₁ M₂ M₁' M₂' : C} (e₁ : M₁ ≅ M₁') (e₂ : M₂ ≅ M₂') (g : M₁ ⟶ M₂) (r : M₁' ⟶ M₂')
    (h : g ≫ e₂.hom = e₁.hom ≫ r) {n : ℕ} (y : Ext.{u + 1} A M₁ n) :
    extPostcompAddEquiv e₂ n (y.comp (Ext.mk₀ g) (add_zero n)) =
      (extPostcompAddEquiv e₁ n y).comp (Ext.mk₀ r) (add_zero n) := by
  change (y.comp (Ext.mk₀ g) (add_zero n)).comp (Ext.mk₀ e₂.hom) (add_zero n) =
    (y.comp (Ext.mk₀ e₁.hom) (add_zero n)).comp (Ext.mk₀ r) (add_zero n)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀, h]

variable [HasExt.{u + 1}
  (Sheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The level `n` of `H^ν(X_k̄, ℤ_ℓ)` is `H^ν(X_k̄, ℤ/ℓⁿ⁺¹)`.** For `X` proper over `k`,
compactified by itself, the `ℤ_ℓ`-module `H^ν_c(X_k̄, (ℤ_ℓ)ₙ)` of the inverse system whose limit
is `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomology` is, as an abelian
group, Mathlib's sheaf cohomology `Sheaf.H` of the constant sheaf `ℤ/ℓⁿ⁺¹` on the small étale site
of `X_k̄ = X ×_{Spec k} Spec k̄`. -/
noncomputable def geometricConstantLevelCohomologyAddEquiv (ν n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar ν).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ≃+
      Sheaf.H.{u + 1} ((constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))) ν :=
  (extConstantAddEquivCompactSupportCohomology ℤ_[ℓ] f kbar
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ν).trans
    ((extForgetSheafHAddEquiv ℤ_[ℓ] (fieldBaseChange (Over.mk f) kbar) _ ν).trans
      (extPostcompAddEquiv (geometricConstantPadicLevelIso B X ℓ f kbar n).symm ν))

set_option maxRecDepth 10000 in
/-- The three steps of `geometricConstantLevelCohomologyAddEquiv`. -/
theorem geometricConstantLevelCohomologyAddEquiv_apply (ν n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar ν).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) :
    geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν n x =
      extPostcompAddEquiv (geometricConstantPadicLevelIso B X ℓ f kbar n).symm ν
        (extForgetSheafH ℤ_[ℓ] (fieldBaseChange (Over.mk f) kbar) _ ν
          (extConstantAddEquivCompactSupportCohomology ℤ_[ℓ] f kbar
            ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
              (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ν x)) :=
  rfl

variable [Finite k] in
/-- **Compatibility with the transition maps**: the transition `H^ν_c(X_k̄, (ℤ_ℓ)ₙ₊₁) ⟶
H^ν_c(X_k̄, (ℤ_ℓ)ₙ)` is, on `Sheaf.H`, the map induced by the reduction `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`. -/
theorem geometricConstantLevelCohomologyAddEquiv_transition (ν n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar ν).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) (n + 1))) :
    geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν n
        ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ν).map
            (homOfLE (n.le_add_right 1)).op x) =
      (geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν (n + 1) x).comp
        (Ext.mk₀ ((constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
          AddCommGrpCat.{u + 1}).map (uliftZModPowReduction ℓ n))) (add_zero ν) := by
  have := Fintype.ofFinite k
  rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
  have h := extConstantAddEquivCompactSupportCohomology_map ℤ_[ℓ] f kbar
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ν x
  rw [geometricConstantLevelCohomologyAddEquiv_apply]
  erw [geometricConstantLevelCohomologyAddEquiv_apply]
  erw [h]
  erw [extForgetSheafH_comp_mk₀]
  have sq : (etaleModuleUnderlyingAbelian (fieldBaseChange (Over.mk f) kbar) ℤ_[ℓ]).map
          ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
              (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n))) ≫
        (geometricConstantPadicLevelIso B X ℓ f kbar n).symm.hom =
      (geometricConstantPadicLevelIso B X ℓ f kbar (n + 1)).symm.hom ≫
        (constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
          AddCommGrpCat.{u + 1}).map (uliftZModPowReduction ℓ n) := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc,
      ← geometricConstantPadicLevelIso_hom_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact extPostcompAddEquiv_comp_mk₀ _ _ _ _ sq _

/-- The constant sheaf on `ℤ`, out of which `Sheaf.H` is `Ext`. -/
abbrev geometricConstantIntSheaf :
    Sheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **The inverse system `n ↦ H^ν_c(X_k̄, (ℤ_ℓ)ₙ)` is the inverse system
`n ↦ H^ν(X_k̄, ℤ/ℓⁿ⁺¹)`**, as inverse systems of abelian groups: the second has the maps induced
by the reductions `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹`. -/
noncomputable def geometricConstantLevelCohomologySystemIso [Finite k] (ν : ℕ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ν ⋙
        forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1} ≅
      uliftZModSystem.{u} ℓ ⋙
        constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        extFunctorObj (geometricConstantIntSheaf B X f kbar) ν :=
  let F := LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ν ⋙
        forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}
  let G := uliftZModSystem.{u} ℓ ⋙
        constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        extFunctorObj (geometricConstantIntSheaf B X f kbar) ν
  let ι : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n) := fun n =>
    (geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν n).toAddCommGrpIso
  let α : F ⟶ G :=
    NatTrans.ofOpSequence (fun n => (ι n).hom)
      (fun n => by
        ext x
        change geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν n
            ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
              (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ν).map
                (homOfLE (n.le_add_right 1)).op x) =
          (geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν (n + 1) x).comp
            (Ext.mk₀ ((constantSheaf (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
              AddCommGrpCat.{u + 1}).map ((uliftZModSystem.{u} ℓ).map
                (homOfLE (n.le_add_right 1)).op))) (add_zero ν)
        rw [uliftZModSystem_map_succ]
        exact geometricConstantLevelCohomologyAddEquiv_transition B X ℓ f kbar ν n x)
  haveI : ∀ n, IsIso (α.app n) := fun ⟨n⟩ => (ι n).isIso_hom
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  asIso α

/-- The components of `geometricConstantLevelCohomologySystemIso` are
`geometricConstantLevelCohomologyAddEquiv`. -/
theorem geometricConstantLevelCohomologySystemIso_hom_app_apply [Finite k] (ν n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar ν).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) :
    ((geometricConstantLevelCohomologySystemIso B X ℓ f kbar ν).hom.app (op n)).hom x =
      geometricConstantLevelCohomologyAddEquiv B X ℓ f kbar ν n x :=
  rfl

end GeometricFibre

end Weil
