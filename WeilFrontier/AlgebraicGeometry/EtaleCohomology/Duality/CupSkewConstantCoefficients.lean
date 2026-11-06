module

public import WeilFrontier.CategoryTheory.Monoidal.ExtUnitGradedComm
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleInjectiveStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLevelExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TrivialRepresentationDual

/-!
# Anticommutativity of the cup product with coefficients isomorphic to the unit

Let `C` be an abelian monoidal category in which the Yoneda algebra `Ext^*(𝟙, 𝟙)` is graded
commutative (`Weil.Ext.comp_eq_negOnePow_smul_comp_of_unit`). If `M` is isomorphic to the unit
and `- ⊗ M` is exact, then for every pairing `μ : M ⊗ M ⟶ T` the cup product
`Ext^p(𝟙, M) × Ext^p(𝟙, M) ⟶ Ext^{2p}(𝟙, T)` is anticommutative when `p` is odd: transporting
along `e : M ≅ 𝟙` turns it into the cup product on `Ext^*(𝟙, 𝟙)` attached to
`(e⁻¹ ⊗ e⁻¹) ≫ μ`.

This applies to ℓ-adic sheaves on a proper scheme `X` over a field `k` whose levels are the
constant sheaves `ℤ/ℓⁿ⁺¹`: extended by zero along the identity compactification and pulled back
to `X_k̄`, the level `n` is the tensor unit `ℤ/ℓⁿ⁺¹` of étale sheaves of `ℤ/ℓⁿ⁺¹`-modules on
`X_k̄`. Two such sheaves are the constant ℓ-adic sheaf `ℤ_ℓ` and, for connected `X`, the sheaf
`ℱ_1` of the trivial rank-one representation of `π₁(X, x̄)`: the level modules of the trivial
representation carry the trivial action, and the sheaf of a trivial action is constant.

## Main results

* `Weil.Ext.cup_eq_cup_comp_mk₀_hom`: transport of the cup product along `e : M ≅ 𝟙`.
* `Weil.Ext.cup_eq_neg_cup_of_odd_of_iso`: the cup product with coefficients isomorphic to the
  unit is anticommutative in odd degree.
* `Weil.LAdicSheaf.etaleLevelRepresentationSheafOneIso`: the levels of `ℱ_1` are constant.
* `Weil.LAdicSheaf.levelInverseImageIsoUnit`: constant levels, extended by zero along the
  identity and pulled back to `X_k̄`, are the tensor unit; the cases
  `Weil.LAdicSheaf.constantSystemLevelInverseImageIsoUnit` (`ℤ_ℓ`) and
  `Weil.LAdicSheaf.representationSheafOneLevelInverseImageIsoUnit` (`ℱ_1`).
* `Weil.LAdicSheaf.cup_skew_of_etaleLevelIso`: for such coefficients and odd `d`, the cup product
  on `Ext^d(ℤ/ℓⁿ⁺¹, Mₙ)` on `X_k̄` is anticommutative; the cases
  `Weil.LAdicSheaf.cup_skew_constantSystem` and `Weil.LAdicSheaf.cup_skew_representationSheaf_one`.

## Implementation notes

The levels are those of `Stacks.EtaleCohomology.LAdicSheaf.constantSystem` (the constant system
`ℤ_ℓ`), read through `Stacks.EtaleCohomology.LAdicSheaf.etaleLevelConstantSystemIso`; the unit of
the monoidal category of étale sheaves of modules is by definition the constant sheaf
(`Stacks.Cohomology.GlobalSections.tensorUnitIsoConstantModuleSheaf`).
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

namespace Weil

namespace Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  [EnoughInjectives C]

/-- Transport of the cup product along isomorphisms `e : M ≅ 𝟙` of both coefficients: the cup
product attached to `μ : M ⊗ M ⟶ T` of `a, b ∈ Ext(𝟙, M)` is the cup product attached to
`(e⁻¹ ⊗ e⁻¹) ≫ μ` of `a ∘ e`, `b ∘ e ∈ Ext(𝟙, 𝟙)`. -/
theorem cup_eq_cup_comp_mk₀_hom {M T : C} (e : M ≅ 𝟙_ C) [(tensorRight M).Additive]
    [PreservesFiniteLimits (tensorRight M)] [PreservesFiniteColimits (tensorRight M)]
    [(tensorRight (𝟙_ C)).Additive] [PreservesFiniteLimits (tensorRight (𝟙_ C))]
    [PreservesFiniteColimits (tensorRight (𝟙_ C))]
    (μ : M ⊗ M ⟶ T) {i j n : ℕ} (a : Abelian.Ext.{w} (𝟙_ C) M i)
    (b : Abelian.Ext.{w} (𝟙_ C) M j) (h : j + i = n) :
    Stacks.ExtCup.cup μ a b h =
      Stacks.ExtCup.cup ((𝟙_ C) ◁ e.inv ≫ e.inv ▷ M ≫ μ)
        (a.comp (Abelian.Ext.mk₀ e.hom) (add_zero i))
        (b.comp (Abelian.Ext.mk₀ e.hom) (add_zero j)) h := by
  have ha : a = (a.comp (Abelian.Ext.mk₀ e.hom) (add_zero i)).comp (Abelian.Ext.mk₀ e.inv)
      (add_zero i) := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  have hb : b = (b.comp (Abelian.Ext.mk₀ e.hom) (add_zero j)).comp (Abelian.Ext.mk₀ e.inv)
      (add_zero j) := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  conv_lhs => rw [ha, hb]
  rw [Stacks.ExtCup.comp_mk₀_cup, Stacks.ExtCup.cup_comp_mk₀_right]

/-- **The cup product is anticommutative in odd degree for coefficients isomorphic to the
unit**, under the hypotheses of `Weil.Ext.comp_eq_negOnePow_smul_comp_of_unit`: for
`e : M ≅ 𝟙` with `- ⊗ M` exact, a pairing `μ : M ⊗ M ⟶ T`, `p` odd and
`a, b ∈ Ext^p(𝟙, M)`, `a ∪_μ b = -(b ∪_μ a)`. -/
theorem cup_eq_neg_cup_of_odd_of_iso (P : C → Prop) (hunit : P (𝟙_ C))
    (hexact : ∀ X, P X → (tensorRight X).Additive ∧ PreservesFiniteLimits (tensorRight X) ∧
      PreservesFiniteColimits (tensorRight X))
    (hemb : ∀ X, P X → ∃ (S : CategoryTheory.ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ X),
      Injective S.X₂ ∧ P S.X₂ ∧ P S.X₃)
    (hleft : ∀ Z : C, PreservesFiniteColimits (tensorLeft Z))
    (hmono : ∀ S : CategoryTheory.ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      ∀ Z, Mono (Z ◁ S.f))
    {M T : C} (e : M ≅ 𝟙_ C) [(tensorRight M).Additive]
    [PreservesFiniteLimits (tensorRight M)] [PreservesFiniteColimits (tensorRight M)]
    (μ : M ⊗ M ⟶ T) {p n : ℕ} (hp : Odd p) (a b : Abelian.Ext.{w} (𝟙_ C) M p)
    (h : p + p = n) :
    Stacks.ExtCup.cup μ a b h = -Stacks.ExtCup.cup μ b a h := by
  obtain ⟨_, _, _⟩ := hexact _ hunit
  rw [cup_eq_cup_comp_mk₀_hom e, cup_eq_cup_comp_mk₀_hom e]
  exact cup_eq_neg_cup_of_odd P hunit hexact hemb hleft hmono _ hp _ _ h

end Ext

section TrivialLevelModule

open Stacks.EtaleCohomology Stacks.GroupCohomology

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ℓ : ℕ}
  [Fact ℓ.Prime] {r : ℕ}


variable (r) in
/-- The finite module `(ℤ/ℓᵏ)^r`, lifted to the universe `u + 1`. -/
def levelModuleULift (k : ℕ) :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} (ZMod (ℓ ^ k))) :=
  ⟨ModuleCat.of _ (ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv (ULift.moduleEquiv (R := ZMod (ℓ ^ k))).symm)⟩

/-- The identity of `(ℤ/ℓᵏ)^r`, from the level module of the trivial representation to the
module with the trivial action. -/
def levelModuleOneHom (h : Continuous ⇑(1 : G →* GL (Fin r) ℤ_[ℓ])) (k : ℕ) :
    levelModule.{u + 1, u + 1} (1 : G →* GL (Fin r) ℤ_[ℓ]) h k ⟶
      (finiteTypeContinuousModuleTrivial (ZMod (ℓ ^ k)) G).obj (levelModuleULift r k) :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := 𝟙 _
      comm := fun g => by
        ext x
        apply ULift.ext
        change (levelULiftRepresentation.{u + 1, u + 1} (1 : G →* GL (Fin r) ℤ_[ℓ]) k g x).down =
          x.down
        refine (levelULiftRepresentation_apply_down.{u + 1, u + 1} (1 : G →* GL (Fin r) ℤ_[ℓ]) k g
          (show ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) from x)).trans ?_
        rw [levelRepresentation_apply]
        simp }))

/-- **The level modules of the trivial representation carry the trivial action.** -/
def levelModuleOneIso (h : Continuous ⇑(1 : G →* GL (Fin r) ℤ_[ℓ])) (k : ℕ) :
    levelModule.{u + 1, u + 1} (1 : G →* GL (Fin r) ℤ_[ℓ]) h k ≅
      (finiteTypeContinuousModuleTrivial (ZMod (ℓ ^ k)) G).obj (levelModuleULift r k) :=
  haveI := isIso_of_bijective (ZMod (ℓ ^ k)) G (levelModuleOneHom h k)
    ⟨fun _ _ hab => hab, fun b => ⟨b, rfl⟩⟩
  asIso (levelModuleOneHom h k)

end TrivialLevelModule

/-- `(R¹)` lifted is `R` lifted, as `R`-modules. -/
def uliftFinOneModuleIso (R : Type) [CommRing R] :
    ModuleCat.of R (ULift.{u + 1} (Fin 1 → R)) ≅ ModuleCat.of R (ULift.{u + 1} R) :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv.trans
    ((LinearEquiv.funUnique (Fin 1) R R).trans ULift.moduleEquiv.symm))

section ConstantLevel

open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

/-- **The constant sheaf on the small étale site of Stacks 021B, read on Mathlib's small étale
site, is the constant sheaf.** -/
def sheafEquivConstantSheafIso (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [Ring Λ]
    [HasWeakSheafify (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)]
    (M : ModuleCat.{u + 1} Λ) :
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.obj
        ((constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj M) ≅
      (constantSheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M := by
  haveI : ∀ Z : (X.1.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Z (SmallEtale.toEtaleSite B X.1 X.2).op) (ModuleCat.{u + 1} Λ) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  exact (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.mapIso
      ((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
        (SmallEtale.topology B X.1 X.2) X.1.smallEtaleTopology
        (SmallEtale.toEtaleSite B X.1 X.2) (ModuleCat.{u + 1} Λ)).app M).symm ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).counitIso.app _

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

/- A Noetherian scheme is quasi-separated. Stated as a local instance because the general
instance search for it times out with these imports. -/
local instance quasiSeparatedSpace_of_isNoetherian (Y : Scheme.{u})
    [AlgebraicGeometry.IsNoetherian Y] : QuasiSeparatedSpace Y :=
  @IsLocallyNoetherian.quasiSeparatedSpace Y IsNoetherian.toIsLocallyNoetherian

/-- **The level `n` of the sheaf `ℱ_1` of the trivial rank-one representation is the constant
sheaf `ℤ/ℓⁿ⁺¹`**, on Mathlib's small étale site of a connected `X`. -/
def LAdicSheaf.etaleLevelRepresentationSheafOneIso [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (h : Continuous ⇑(1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) (n : ℕ) :
    LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.representationSheaf B X x 1 h) n ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology := by
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  have key : ∀ (σ : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) (hσ : Continuous σ),
      σ = 1 →
      ((lisseSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj (levelModule.{u + 1, u + 1} σ hσ (n + 1)) ≅
        (constantSheaf (SmallEtale.topology B X.1 X.2)
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj (levelModuleULift 1 (n + 1)).obj) := by
    rintro σ hσ rfl
    exact (lisseSheaf B X x (ZMod (ℓ ^ (n + 1)))).mapIso (levelModuleOneIso hσ (n + 1)) ≪≫
      ((AlgebraicGeometry.constantIsoTrivialRepresentationSheafSmall B X x
        (ZMod (ℓ ^ (n + 1)))).app (levelModuleULift 1 (n + 1))).symm
  exact (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.mapIso
      (key _ (continuous_integralModel _ h) (integralModel_one h)) ≪≫
    sheafEquivConstantSheafIso B X _ _ ≪≫
    (constantSheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).mapIso
      (uliftFinOneModuleIso _)

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **Levels isomorphic to the constant sheaf are the tensor unit on `X_k̄`**: if the level `n`
of an ℓ-adic sheaf `F` on the proper `X` is the constant sheaf `ℤ/ℓⁿ⁺¹`, then extended by zero
along the identity compactification and pulled back to `X_k̄` it is the unit `ℤ/ℓⁿ⁺¹` of étale
sheaves of `ℤ/ℓⁿ⁺¹`-modules on `X_k̄`. -/
def LAdicSheaf.levelInverseImageIsoUnit (F : AlgebraicGeometry.SmallEtale.LAdicSheaf B X ℓ) (n : ℕ)
    (e : LAdicSheaf.etaleLevel B X ℓ F n ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n)) ≅
      𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar)) :=
  (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeProj (Over.mk f) kbar)).mapIso
    ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) (𝟙 X.1)).mapIso e ≪≫
      (etaleModuleExtensionByZeroIdIso (ZMod (ℓ ^ (n + 1))) X.1).app _) ≪≫
    inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (fieldBaseChangeProj (Over.mk f) kbar) ≪≫
    (Stacks.Cohomology.GlobalSections.tensorUnitIsoConstantModuleSheaf _ _).symm

/-- **The levels of the constant ℓ-adic sheaf, read on `X_k̄`, are the tensor unit**: extended
by zero along the identity compactification of the proper `X` and pulled back to `X_k̄`, the
level `n` of `ℤ_ℓ` is the unit `ℤ/ℓⁿ⁺¹` of étale sheaves of `ℤ/ℓⁿ⁺¹`-modules on `X_k̄`. -/
def LAdicSheaf.constantSystemLevelInverseImageIsoUnit (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ≅
      𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar)) :=
  LAdicSheaf.levelInverseImageIsoUnit B X ℓ f kbar _ n
    (LAdicSheaf.etaleLevelConstantSystemIso B X ℓ n)

/-- **The levels of the sheaf `ℱ_1` of the trivial rank-one representation, read on `X_k̄`, are
the tensor unit.** -/
def LAdicSheaf.representationSheafOneLevelInverseImageIsoUnit [ConnectedSpace X.1]
    (x : GeometricPoint X.1)
    (h : Continuous ⇑(1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.representationSheaf B X x 1 h) n)) ≅
      𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar)) :=
  LAdicSheaf.levelInverseImageIsoUnit B X ℓ f kbar _ n
    (LAdicSheaf.etaleLevelRepresentationSheafOneIso B X ℓ x h n)

/-- **The cup product on the middle cohomology of coefficients with constant levels is
anticommutative.** Let `F` be an ℓ-adic sheaf on the proper `X` whose levels are the constant
sheaves `ℤ/ℓⁿ⁺¹`, `μₙ` pairings of its levels (read on `j_! = id`) into `ℤ/ℓⁿ⁺¹`, `d` odd, and
`a, b ∈ Ext^d(ℤ/ℓⁿ⁺¹, Mₙ)` on `X_k̄`, where `Mₙ` is the pulled back level. Then
`a ∪ b = -(b ∪ a)` for the pulled back pairing. The pulled back levels are the tensor unit
(`Weil.LAdicSheaf.levelInverseImageIsoUnit`), and the Yoneda algebra of the unit is graded
commutative, sheaves with injective stalks (`Weil.HasInjectiveStalks`) providing the dimension
shifting. -/
theorem LAdicSheaf.cup_skew_of_etaleLevelIso (F : AlgebraicGeometry.SmallEtale.LAdicSheaf B X ℓ)
    (e : ∀ n, LAdicSheaf.etaleLevel B X ℓ F n ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology) {d : ℕ} (hd : Odd d)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology) :
    ∀ (n : ℕ)
      [(MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n)))).Additive]
      [PreservesFiniteLimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))))]
      [PreservesFiniteColimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))))]
      (a b : Abelian.Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))) d)
      (h : d + d = 2 * d),
      Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) a b h =
        -Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) b a h := by
  intro n _ _ _ a b h
  exact Ext.cup_eq_neg_cup_of_odd_of_iso (HasInjectiveStalks (ℓ := ℓ) (k := n))
    hasInjectiveStalks_unit tensorRight_exact_of_hasInjectiveStalks
    exists_shortExact_injective_of_hasInjectiveStalks preservesFiniteColimits_tensorLeft
    (fun _ hS h₁ h₂ h₃ Z => mono_whiskerLeft_f_of_shortExact hS h₁ h₂ h₃ Z)
    (LAdicSheaf.levelInverseImageIsoUnit B X ℓ f kbar F n (e n)) _ hd a b h

/-- **The hypothesis `hcup` for the constant ℓ-adic sheaf `ℤ_ℓ`**: the cup product on the
middle cohomology of its pulled back levels is anticommutative in odd degree. -/
theorem LAdicSheaf.cup_skew_constantSystem {d : ℕ} (hd : Odd d)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology) :
    ∀ (n : ℕ)
      [(MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.constantSystem B X ℓ) n)))).Additive]
      [PreservesFiniteLimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.constantSystem B X ℓ) n))))]
      [PreservesFiniteColimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.constantSystem B X ℓ) n))))]
      (a b : Abelian.Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.constantSystem B X ℓ) n))) d)
      (h : d + d = 2 * d),
      Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) a b h =
        -Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) b a h :=
  LAdicSheaf.cup_skew_of_etaleLevelIso B X ℓ f kbar _
    (LAdicSheaf.etaleLevelConstantSystemIso B X ℓ) hd μ

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The hypothesis `hcup` for the sheaf `ℱ_1` of the trivial rank-one representation**: the
cup product on the middle cohomology of its pulled back levels is anticommutative in odd
degree. -/
theorem LAdicSheaf.cup_skew_representationSheaf_one [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (hρ : Continuous ⇑(1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) {d : ℕ} (hd : Odd d)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.representationSheaf B X x 1 hρ) n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.representationSheaf B X x 1 hρ) n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology) :
    ∀ (n : ℕ)
      [(MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.representationSheaf B X x 1 hρ) n)))).Additive]
      [PreservesFiniteLimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.representationSheaf B X x 1 hρ) n))))]
      [PreservesFiniteColimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.representationSheaf B X x 1 hρ) n))))]
      (a b : Abelian.Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.representationSheaf B X x 1 hρ) n))) d)
      (h : d + d = 2 * d),
      Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) a b h =
        -Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) b a h :=
  LAdicSheaf.cup_skew_of_etaleLevelIso B X ℓ f kbar _
    (LAdicSheaf.etaleLevelRepresentationSheafOneIso B X ℓ x hρ) hd μ

end ConstantLevel

end Weil
