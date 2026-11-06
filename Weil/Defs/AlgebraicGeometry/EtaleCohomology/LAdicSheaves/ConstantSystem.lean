module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Additive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafLocalSections
public import Weil.Defs.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.NumberTheory.Padics.RingHoms
public import Weil.Attr

/-!
# The constant `ℓ`-adic sheaf of a finite `ℤ_ℓ`-module

Let `X` be a Noetherian scheme, `ℓ` a prime and `M` a finitely generated `ℤ_ℓ`-module. The
constant `ℓ`-adic sheaf `M_X` has as its level `n` the constant sheaf on the small étale site of
`X` with value the `ℤ/ℓⁿ⁺¹ℤ`-module `M / ℓⁿ⁺¹ M`, and as transition maps the morphisms of constant
sheaves induced by the projections `M / ℓⁿ⁺² M → M / ℓⁿ⁺¹ M`. Each level is the constant sheaf of
a finite module, hence locally constant of finite type and constructible, and the scalar
reduction of level `n + 1` is level `n`, so `M_X` is an `ℓ`-adic sheaf in the sense of
[Tag 03UM](https://stacks.math.columbia.edu/tag/03UM).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.modPowReduction`: the reduction `M ↦ ℤ/ℓⁿ⁺¹ℤ ⊗_{ℤ_ℓ} M`.
* `Stacks.EtaleCohomology.LAdicSheaf.modPowReductionEquiv`: `ℤ/ℓⁿ⁺¹ℤ ⊗_{ℤ_ℓ} M ≃ M / ℓⁿ⁺¹ M`.
* `Stacks.EtaleCohomology.LAdicSheaf.modPowReductionTransition`: the transition
  `ℤ/ℓⁿ⁺²ℤ ⊗ M → ℤ/ℓⁿ⁺¹ℤ ⊗ M`, which is `M / ℓⁿ⁺² M → M / ℓⁿ⁺¹ M`.
* `Stacks.EtaleCohomology.LAdicSheaf.constantRestrictScalarsComparison`: the comparison from the
  constant sheaf of a restriction of scalars to the restriction of scalars of a constant sheaf.
* `Stacks.EtaleCohomology.LAdicSheaf.constantOfModule`: the constant `ℓ`-adic sheaf `M_X`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.constantOfModule_level`: level `n` of `M_X` is the constant
  sheaf of `ℤ/ℓⁿ⁺¹ℤ ⊗ M`.
* `Stacks.EtaleCohomology.LAdicSheaf.constantOfModule_transition`: the transition maps of `M_X`
  are the morphisms of constant sheaves induced by the transitions of the reductions of `M`.
* `Stacks.EtaleCohomology.LAdicSheaf.modPowReductionEquiv_one_tmul`,
  `Stacks.EtaleCohomology.LAdicSheaf.modPowReductionTransition_one_tmul`: on the generators
  `1 ⊗ m`, the identification with `M / ℓⁿ⁺¹ M` is `m ↦ m mod ℓⁿ⁺¹`, and the transition is
  `m mod ℓⁿ⁺² ↦ m mod ℓⁿ⁺¹`.
* `Stacks.EtaleCohomology.LAdicSheaf.modPowReductionEquivOfModule`: the module of level `n` is
  the term `S(M)_n` of the projective system `CategoryTheory.ProjectiveSystem.ofModule`.

## Implementation notes

The levels are indexed by `n : ℕ`, level `n` carrying coefficients in `ℤ/ℓⁿ⁺¹ℤ`, which is
Tag 03UM's convention for `ℓ`-adic sheaves; the zero terms in negative degrees of the
`ℤ`-indexed system are not recorded. The value of level `n` is the extension of scalars
`ℤ/ℓⁿ⁺¹ℤ ⊗_{ℤ_ℓ} M` rather than the quotient `M / ℓⁿ⁺¹ M`: the two are identified by
`Stacks.EtaleCohomology.LAdicSheaf.modPowReductionEquiv`, and the tensor form carries its
`ℤ/ℓⁿ⁺¹ℤ`-module structure and its functoriality in `n` canonically. The constant sheaf is
Mathlib's `CategoryTheory.constantSheaf`, the sheafification of the constant presheaf.

The compatibility condition of Tag 03UM is proved by uniqueness of adjoints: the composite
`M ↦ ℤ/ℓⁿ⁺²ℤ ⊗ M ↦ (−)_X ↦` scalar reduction is left adjoint to global sections followed by
restriction of scalars to `ℤ_ℓ`, and so is `M ↦ ℤ/ℓⁿ⁺¹ℤ ⊗ M ↦ (−)_X`, so the two are isomorphic
(`Stacks.EtaleCohomology.LAdicSheaf.reductionCompIso`). The transition map of `M_X` is the
adjoint of that isomorphism, so its scalar reduction is an isomorphism by construction, and
`Stacks.EtaleCohomology.LAdicSheaf.constantOfModule_transition` identifies it with the morphism
of constant sheaves induced by the module transition.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

/- The constant ℓ-adic sheaf of a module.
FK index the system by `ℤ` with zero terms below `0`; the ℓ-adic sheaves used here are
StacksFrontier's `LAdicSheaf` (ℕ-indexed). Not done here: an isomorphism with StacksFrontier's
`LAdicSheaf.constantSystem` at `M = ℤ_ℓ`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Opposite Pointwise
open scoped ChangeOfRings

universe u

namespace Stacks.EtaleCohomology

namespace LAdicSheaf

section Modules

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Reduction modulo `ℓⁿ⁺¹`: the extension of scalars along `ℤ_ℓ → ℤ/ℓⁿ⁺¹ℤ`, sending `M` to
`ℤ/ℓⁿ⁺¹ℤ ⊗_{ℤ_ℓ} M`. -/
abbrev modPowReduction (n : ℕ) :
    ModuleCat.{u + 1} ℤ_[ℓ] ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))) :=
  ModuleCat.extendScalars.{0, 0, u + 1} (PadicInt.toZModPow (n + 1))

/-- The reduction modulo `ℓⁿ⁺¹` of a finite `ℤ_ℓ`-module is a finite `ℤ/ℓⁿ⁺¹ℤ`-module. -/
instance finite_modPowReduction (M : ModuleCat.{u + 1} ℤ_[ℓ]) [Module.Finite ℤ_[ℓ] M] (n : ℕ) :
    Module.Finite (ZMod (ℓ ^ (n + 1))) ((modPowReduction ℓ n).obj M) := by
  let := (PadicInt.toZModPow (p := ℓ) (n + 1)).toAlgebra
  exact Module.Finite.base_change ℤ_[ℓ] (ZMod (ℓ ^ (n + 1))) M

/-- Reduction from `ℤ/ℓⁿ⁺²ℤ` to `ℤ/ℓⁿ⁺¹ℤ` after reduction from `ℤ_ℓ` to `ℤ/ℓⁿ⁺²ℤ` is reduction
from `ℤ_ℓ` to `ℤ/ℓⁿ⁺¹ℤ`. -/
lemma finiteLevelRingHom_comp_toZModPow (n : ℕ) :
    (finiteLevelRingHom ℓ n).comp (PadicInt.toZModPow (n + 1 + 1)) =
      PadicInt.toZModPow (p := ℓ) (n + 1) :=
  PadicInt.zmod_cast_comp_toZModPow _ _ (by omega)

/-- `ℤ_ℓ / ker(ℤ_ℓ → ℤ/ℓⁿ⁺¹ℤ) ≃ ℤ/ℓⁿ⁺¹ℤ` as `ℤ_ℓ`-modules. -/
def quotientKerToZModPowEquiv (n : ℕ) :
    (ℤ_[ℓ] ⧸ RingHom.ker (PadicInt.toZModPow (p := ℓ) (n + 1))) ≃ₗ[ℤ_[ℓ]]
      (ModuleCat.restrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
        (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ZMod (ℓ ^ (n + 1)))) where
  __ := (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective
    (PadicInt.toZModPow (p := ℓ) (n + 1)))).toAddEquiv
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow (p := ℓ) (n + 1))))
        (Ideal.Quotient.mk _ (r * x)) = PadicInt.toZModPow (n + 1) r *
      (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow (p := ℓ) (n + 1)))) (Ideal.Quotient.mk _ x)
    simp

/-- `ker(ℤ_ℓ → ℤ/ℓⁿ⁺¹ℤ) M = ℓⁿ⁺¹ M`. -/
lemma ker_toZModPow_smul_top (M : Type*) [AddCommGroup M] [Module ℤ_[ℓ] M] (n : ℕ) :
    (RingHom.ker (PadicInt.toZModPow (p := ℓ) (n + 1)) • ⊤ : Submodule ℤ_[ℓ] M) =
      (ℓ : ℤ_[ℓ]) ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M) := by
  rw [PadicInt.ker_toZModPow, Submodule.ideal_span_singleton_smul]

/-- `ℤ/ℓⁿ⁺¹ℤ ⊗_{ℤ_ℓ} M ≃ M / ℓⁿ⁺¹ M`, for the `ℤ_ℓ`-module structure of the tensor product
through its left factor. -/
abbrev tensorModPowEquiv (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) :
    TensorProduct ℤ_[ℓ] ((ModuleCat.restrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
        (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ZMod (ℓ ^ (n + 1))))) M ≃ₗ[ℤ_[ℓ]]
      M ⧸ ((ℓ : ℤ_[ℓ]) ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M)) :=
  (TensorProduct.congr (quotientKerToZModPowEquiv ℓ n).symm (LinearEquiv.refl ℤ_[ℓ] M)).trans
    ((TensorProduct.quotTensorEquivQuotSMul M _).trans
      (Submodule.quotEquivOfEq _ _ (ker_toZModPow_smul_top ℓ M n)))

/-- **The reduction of `M` modulo `ℓⁿ⁺¹` is `M / ℓⁿ⁺¹ M`**: `ℤ/ℓⁿ⁺¹ℤ ⊗_{ℤ_ℓ} M`, read as a
`ℤ_ℓ`-module by restriction of scalars, is `M / ℓⁿ⁺¹ M`. -/
@[weil "def_fk112_constant_l_adic_sheaf_of_module"]
def modPowReductionEquiv (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) :
    (ModuleCat.restrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
        ((modPowReduction ℓ n).obj M) ≃ₗ[ℤ_[ℓ]]
      M ⧸ ((ℓ : ℤ_[ℓ]) ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M)) where
  toFun t := tensorModPowEquiv ℓ M n t
  invFun x := (tensorModPowEquiv ℓ M n).symm x
  left_inv t := (tensorModPowEquiv ℓ M n).symm_apply_apply t
  right_inv x := (tensorModPowEquiv ℓ M n).apply_symm_apply x
  map_add' x y := (tensorModPowEquiv ℓ M n).map_add x y
  map_smul' r t := by
    induction t using TensorProduct.induction_on with
    | zero => exact (tensorModPowEquiv ℓ M n).map_smul r 0
    | tmul s m => exact (tensorModPowEquiv ℓ M n).map_smul r (s ⊗ₜ m)
    | add x y hx hy =>
      have h1 := smul_add (M := ℤ_[ℓ]) (A := (ModuleCat.restrictScalars
        (PadicInt.toZModPow (p := ℓ) (n + 1))).obj ((modPowReduction ℓ n).obj M)) r x y
      refine (congrArg (tensorModPowEquiv ℓ M n) h1).trans ?_
      refine ((tensorModPowEquiv ℓ M n).map_add _ _).trans ?_
      rw [hx, hy, ← smul_add, ← map_add]

lemma modPowReductionEquiv_symm_mk (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) (m : M) :
    (modPowReductionEquiv ℓ M n).symm (Submodule.Quotient.mk m) =
      (1 : ZMod (ℓ ^ (n + 1))) ⊗ₜ[ℤ_[ℓ],PadicInt.toZModPow (p := ℓ) (n + 1)] m := by
  change quotientKerToZModPowEquiv ℓ n (Ideal.Quotient.mk _ 1) ⊗ₜ[ℤ_[ℓ]] m = _
  congr 1
  exact map_one (PadicInt.toZModPow (p := ℓ) (n + 1))

/-- `modPowReductionEquiv` sends `1 ⊗ m` to `m mod ℓⁿ⁺¹`. -/
@[simp]
lemma modPowReductionEquiv_one_tmul (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) (m : M) :
    modPowReductionEquiv ℓ M n
        ((1 : ZMod (ℓ ^ (n + 1))) ⊗ₜ[ℤ_[ℓ],PadicInt.toZModPow (p := ℓ) (n + 1)] m) =
      Submodule.Quotient.mk m :=
  ((LinearEquiv.symm_apply_eq _).mp (modPowReductionEquiv_symm_mk ℓ M n m)).symm

/-- The module of level `n` is the term `S(M)_n = M / ℓⁿ⁺¹ M` of the projective system of `M`,
`CategoryTheory.ProjectiveSystem.ofModule`. -/
def modPowReductionEquivOfModule (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) :
    (ModuleCat.restrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
        ((modPowReduction ℓ n).obj M) ≃ₗ[ℤ_[ℓ]]
      ((CategoryTheory.ProjectiveSystem.ofModule (ℓ : ℤ_[ℓ])).obj M).term n :=
  (modPowReductionEquiv ℓ M n).trans
    ((CategoryTheory.ProjectiveSystem.ofModuleTermEquiv (ℓ : ℤ_[ℓ]) M
      (Int.natCast_nonneg n)).symm)

/-- **The transition maps of the reductions of `M`**: the `ℤ/ℓⁿ⁺²ℤ`-linear map
`ℤ/ℓⁿ⁺²ℤ ⊗ M → ℤ/ℓⁿ⁺¹ℤ ⊗ M` extending `m ↦ 1 ⊗ m`; under `modPowReductionEquiv` it is the
projection `M / ℓⁿ⁺² M → M / ℓⁿ⁺¹ M` (`modPowReductionTransition_one_tmul`). -/
def modPowReductionTransition (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) :
    (modPowReduction ℓ (n + 1)).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} (finiteLevelRingHom ℓ n)).obj
        ((modPowReduction ℓ n).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0}
    (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).homEquiv _ _).symm
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0}
      (PadicInt.toZModPow (p := ℓ) (n + 1))).unit.app M ≫
      (ModuleCat.restrictScalarsComp' _ _ _
        (finiteLevelRingHom_comp_toZModPow ℓ n).symm).hom.app _)

/-- The transition `ℤ/ℓⁿ⁺²ℤ ⊗ M → ℤ/ℓⁿ⁺¹ℤ ⊗ M` sends `1 ⊗ m` to `1 ⊗ m`. -/
@[simp]
lemma modPowReductionTransition_one_tmul (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) (m : M) :
    (modPowReductionTransition ℓ M n).hom
        ((1 : ZMod (ℓ ^ (n + 1 + 1))) ⊗ₜ[ℤ_[ℓ],PadicInt.toZModPow (p := ℓ) (n + 1 + 1)] m) =
      (1 : ZMod (ℓ ^ (n + 1))) ⊗ₜ[ℤ_[ℓ],PadicInt.toZModPow (p := ℓ) (n + 1)] m := by
  exact (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (modPowReductionTransition ℓ M n) m).symm.trans
      (congrArg (fun g => ModuleCat.Hom.hom g m) (Equiv.apply_symm_apply _ _))

end Modules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- The constant sheaf functor at level `n`. -/
abbrev constantLevelFunctor (n : ℕ) :
    ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))) ⥤ FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  constantSheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))

/-- Global sections at level `n`: evaluation at the final object of the small étale site. -/
abbrev sectionsLevelFunctor (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B X ℓ n ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))) :=
  (sheafSections (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj (op (SmallEtale.final B X.1 X.property))

/-- The constant sheaf is left adjoint to global sections, at level `n`. -/
abbrev constantLevelAdj (n : ℕ) :
    constantLevelFunctor B X ℓ n ⊣ sectionsLevelFunctor B X ℓ n :=
  constantSheafAdj (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) (SmallEtale.finalIsTerminal B X.1 X.property)

/-- Global sections followed by restriction of scalars to `ℤ_ℓ` at level `n` is global sections
of the restriction of scalars to `ℤ/ℓⁿ⁺²ℤ`, followed by restriction of scalars to `ℤ_ℓ`. -/
def sectionsRestrictScalarsIso (n : ℕ) :
    sectionsLevelFunctor B X ℓ n ⋙
        ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)) ≅
      (restrictScalarsFunctor B X ℓ n ⋙ sectionsLevelFunctor B X ℓ (n + 1)) ⋙
        ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) :=
  Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' _ _ _
      (finiteLevelRingHom_comp_toZModPow ℓ n).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl _) _

/-- The adjunction of the composite `M ↦ ℤ/ℓⁿ⁺²ℤ ⊗ M ↦ (−)_X ↦` scalar reduction. -/
abbrev reductionCompAdj (n : ℕ) :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0}
    (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).comp
    ((constantLevelAdj B X ℓ (n + 1)).comp (scalarAdjunction B X ℓ n))

/-- The adjunction of the composite `M ↦ ℤ/ℓⁿ⁺¹ℤ ⊗ M ↦ (−)_X`. -/
abbrev levelCompAdj (n : ℕ) :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} (PadicInt.toZModPow (p := ℓ) (n + 1))).comp
    (constantLevelAdj B X ℓ n)

/-- **Scalar reduction of the constant sheaf.** The scalar reduction of the constant sheaf of
`ℤ/ℓⁿ⁺²ℤ ⊗ M` is the constant sheaf of `ℤ/ℓⁿ⁺¹ℤ ⊗ M`, naturally in the `ℤ_ℓ`-module `M`: both
functors are left adjoint to global sections read as a `ℤ_ℓ`-module. -/
def reductionCompIso (n : ℕ) :
    modPowReduction ℓ (n + 1) ⋙ constantLevelFunctor B X ℓ (n + 1) ⋙
        scalarReductionFunctor B X ℓ n ≅
      modPowReduction ℓ n ⋙ constantLevelFunctor B X ℓ n :=
  (conjugateIsoEquiv (levelCompAdj B X ℓ n) (reductionCompAdj B X ℓ n)).symm
    (sectionsRestrictScalarsIso B X ℓ n)

/-- The comparison from the constant sheaf of the restriction of scalars of a `ℤ/ℓⁿ⁺¹ℤ`-module
`N` to the restriction of scalars of the constant sheaf of `N`: the morphism out of a constant
sheaf corresponding to the restriction of scalars of the unit `N ⟶ Γ(X, N_X)`. -/
def constantRestrictScalarsComparison (n : ℕ) (N : ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :
    (constantLevelFunctor B X ℓ (n + 1)).obj
        ((ModuleCat.restrictScalars.{u + 1} (finiteLevelRingHom ℓ n)).obj N) ⟶
      (restrictScalarsFunctor B X ℓ n).obj ((constantLevelFunctor B X ℓ n).obj N) :=
  ((constantLevelAdj B X ℓ (n + 1)).homEquiv _ _).symm
    ((ModuleCat.restrictScalars.{u + 1} (finiteLevelRingHom ℓ n)).map
      ((constantLevelAdj B X ℓ n).unit.app N))

/-- The adjoint of the scalar-reduction isomorphism `reductionCompIso` is the morphism of
constant sheaves induced by the module transition `modPowReductionTransition`. -/
theorem homEquiv_reductionCompIso (M : ModuleCat.{u + 1} ℤ_[ℓ]) (n : ℕ) :
    ((scalarAdjunction B X ℓ n).homEquiv _ _) ((reductionCompIso B X ℓ n).app M).hom =
      (constantLevelFunctor B X ℓ (n + 1)).map (modPowReductionTransition ℓ M n) ≫
        constantRestrictScalarsComparison B X ℓ n ((modPowReduction ℓ n).obj M) := by
  apply ((constantLevelAdj B X ℓ (n + 1)).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0}
    (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).homEquiv _ _).injective
  have h := unit_conjugateEquiv_symm (levelCompAdj B X ℓ n) (reductionCompAdj B X ℓ n)
    (sectionsRestrictScalarsIso B X ℓ n).hom M
  have hL : ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0}
      (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).homEquiv _ _)
      (((constantLevelAdj B X ℓ (n + 1)).homEquiv _ _)
        (((scalarAdjunction B X ℓ n).homEquiv _ _) ((reductionCompIso B X ℓ n).app M).hom)) =
      (reductionCompAdj B X ℓ n).homEquiv _ _ ((reductionCompIso B X ℓ n).app M).hom := rfl
  rw [hL, Adjunction.homEquiv_unit]
  erw [← h]
  rw [Adjunction.homEquiv_naturality_left, constantRestrictScalarsComparison]
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  rw [modPowReductionTransition]
  erw [Equiv.apply_symm_apply]
  ext m
  rfl

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1]

/-- **The constant `ℓ`-adic sheaf `M_X` of a finite `ℤ_ℓ`-module `M`.** Its level `n` is the
constant sheaf on the small étale site of `X` with value `ℤ/ℓⁿ⁺¹ℤ ⊗ M = M / ℓⁿ⁺¹ M`, which is
constructible, being locally constant of finite type; its transition maps are the morphisms of
constant sheaves induced by the projections `M / ℓⁿ⁺² M → M / ℓⁿ⁺¹ M`
(`constantOfModule_transition`), whose scalar reductions are the isomorphisms
`reductionCompIso`. -/
@[weil "def_fk112_constant_l_adic_sheaf_of_module"]
def constantOfModule (M : ModuleCat.{u + 1} ℤ_[ℓ]) [Module.Finite ℤ_[ℓ] M] :
    LAdicSheaf.{u, u + 1} B X ℓ where
  level n := (constantLevelFunctor B X ℓ n).obj ((modPowReduction ℓ n).obj M)
  constructible n :=
    isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X (ZMod (ℓ ^ (n + 1))) _
      (Stacks.ConstantSheaf.finiteTypeLocallyConstant_constantSheaf _ _
        (by simpa [ModuleCat.isFG] using finite_modPowReduction ℓ M n))
  transition n := ((scalarAdjunction B X ℓ n).homEquiv _ _)
    ((reductionCompIso B X ℓ n).app M).hom
  reduction_isIso n := by
    rw [FiniteLevelSheaf.scalarReductionMap, Equiv.symm_apply_apply]
    infer_instance

/-- Level `n` of `M_X` is the constant sheaf of `ℤ/ℓⁿ⁺¹ℤ ⊗ M`. -/
@[weil "def_fk112_constant_l_adic_sheaf_of_module", simp]
theorem constantOfModule_level (M : ModuleCat.{u + 1} ℤ_[ℓ]) [Module.Finite ℤ_[ℓ] M] (n : ℕ) :
    (constantOfModule B X ℓ M).level n =
      (constantSheaf (SmallEtale.topology B X.1 X.property)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj ((modPowReduction ℓ n).obj M) :=
  rfl

/-- **The transition maps of `M_X`** are the morphisms of constant sheaves induced by the
transitions `ℤ/ℓⁿ⁺²ℤ ⊗ M → ℤ/ℓⁿ⁺¹ℤ ⊗ M` of the reductions of `M`, that is by the projections
`M / ℓⁿ⁺² M → M / ℓⁿ⁺¹ M`, followed by the comparison with the restriction of scalars of a
constant sheaf. -/
@[weil "def_fk112_constant_l_adic_sheaf_of_module"]
theorem constantOfModule_transition (M : ModuleCat.{u + 1} ℤ_[ℓ]) [Module.Finite ℤ_[ℓ] M]
    (n : ℕ) :
    (constantOfModule B X ℓ M).transition n =
      (constantLevelFunctor B X ℓ (n + 1)).map (modPowReductionTransition ℓ M n) ≫
        constantRestrictScalarsComparison B X ℓ n ((modPowReduction ℓ n).obj M) :=
  homEquiv_reductionCompIso B X ℓ M n

end LAdicSheaf

end Stacks.EtaleCohomology
