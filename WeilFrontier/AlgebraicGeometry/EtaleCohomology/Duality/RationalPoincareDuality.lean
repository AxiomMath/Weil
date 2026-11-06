module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilIIPurityAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveRelativeDualityInputProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssemblyLeaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationLevelPairingPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels
public import WeilFrontier.LinearAlgebra.PerfectPairing.FrobeniusDuality
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TrivialRepresentationDual

/-!
# The Frobenius-equivariant Poincaré pairing on `Hⁱ(X_k̄, F ⊗ ℚ_ℓ)` at a rational point

Let `X` be proper over a finite field `k` with `p ^ q` elements, `k̄` an algebraically closed
extension of `k`, and suppose `Y = X_k̄` is connected and smooth of relative dimension `d`.
StacksFrontier builds, for ℓ-adic sheaves `F`, `F'` with a pairing `μ` of their levels, finite level
Poincaré pairings `εₙ` of `Hⁱ(Y, Fₙ)` and `H^{2d-i}(Y, F'ₙ)` with values in `ℤ/ℓⁿ⁺¹`,
nondegenerate on both sides and multiplied by `q^d` under the geometric Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing`), and uses them to prove purity
(`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_rationalPoint`). This file
returns the pairing itself, after `⊗ ℚ_ℓ`: a perfect `ℚ_ℓ`-bilinear pairing `β` of
`Hⁱ(Y, F ⊗ ℚ_ℓ)` and `H^{2d-i}(Y, F' ⊗ ℚ_ℓ)` with `β(π^* v, π^* w) = q^d β(v, w)`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_levelPairing`:
  finite level pairings with Frobenius factor `c` give a perfect `ℚ_ℓ`-pairing with factor `c`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_rationalPoint`:
  the `q^d`-equivariant perfect pairing for `X` with a rational point, the two inputs of
  Poincaré duality over `k̄` (`PoincareDualityCore`, `TopCohomologyPointClass`) discharged by
  StacksFrontier's proofs.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S


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

section LevelPairing

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **A perfect `ℚ_ℓ`-pairing from finite level Poincaré pairings.** If the levels of `F` and `F'`
are flat with perfect `RΓ_c(X_k̄, -)`, and for every `n` a pairing `εₙ` of `Hⁱ_c(X_k̄, Fₙ)` and
`Hʲ_c(X_k̄, F'ₙ)` with values in `ℤ/ℓⁿ⁺¹` is nondegenerate on both sides and multiplied by `c`
under the geometric Frobenius, then there is a perfect `ℚ_ℓ`-bilinear pairing `β` of
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` and `Hʲ_c(X_k̄, F' ⊗ ℚ_ℓ)` with `β(π^* v, π^* w) = c β(v, w)`. -/
theorem LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_levelPairing (F F' : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    (hF' : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n))
    (hP' : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F' n))))
    (i i' : ℤ) (c : ℕ)
    (ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar i').obj
        (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → x = 0) (hr : ∀ n y, (∀ x, ε n x y = 0) → y = 0)
    (hε : ∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x)
      ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n)) i').hom y) =
        (c : ZMod (ℓ ^ (n + 1))) * ε n x y) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F' i' →ₗ[ℚ_[ℓ]]
          ℚ_[ℓ],
      β.IsPerfPair ∧ ∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F'
            i').hom w) = (c : ℚ_[ℓ]) * β v w := by
  let e := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i
  let e' := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F' hF' hP' i'
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    Stacks.InverseSystem.finite_limit_of_iso _ i e
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F' i') :=
    Stacks.InverseSystem.finite_limit_of_iso _ i' e'
  obtain ⟨c₁, h₁⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _ i e
  obtain ⟨c₂, h₂⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _ i' e'
  have hraise {N M : Type (u + 1)} [AddCommGroup N] [AddCommGroup M] (π : M →+ N) (c K : ℕ)
      (hcK : c ≤ K) (h : ∀ y, ∃ a, π a = (ℓ ^ c) • y) (y : N) : ∃ a, π a = (ℓ ^ K) • y := by
    obtain ⟨a, ha⟩ := h y
    refine ⟨(ℓ ^ (K - c)) • a, ?_⟩
    rw [map_nsmul, ha, smul_smul, ← pow_add, Nat.sub_add_cancel hcK]
  exact LAdicPairing.exists_isPerfPair_extendScalars_of_levels
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F' i')
    c (max c₁ c₂)
    (fun n =>
      (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n).hom.toAddMonoidHom)
    (fun n =>
      (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F' i' n).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
          i).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n))
          i').hom.toAddMonoidHom)
    (fun n a => congrArg (fun φ => φ.hom a)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F i n))
    (fun n b => congrArg (fun φ => φ.hom b)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F' i' n))
    (fun n => (h₁ n).1) (fun n => (h₂ n).1)
    (fun n => hraise _ c₁ _ (le_max_left _ _) (h₁ n).2)
    (fun n => hraise _ c₂ _ (le_max_right _ _) (h₂ n).2)
    ε hl hr hε

end LevelPairing

section RationalPoint

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The `q^d`-equivariant perfect Poincaré pairing on `Hⁱ(X_k̄, F ⊗ ℚ_ℓ)` for `X` smooth and
proper, given the Frobenius on the top cohomology.** Let `X` be proper over the finite field `k`
with `p ^ q` elements such that the geometric Frobenius acts on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` as
multiplication by `q^d` for every `n` (`hC`; true when `X` has a rational point), `k̄`
algebraically closed, `Y = X_k̄` connected and smooth of
relative dimension `d` over `k̄`, `ℓ` invertible in `k̄`, and `F`, `F'` ℓ-adic sheaves with flat
levels and perfect `RΓ(X_k̄, -)` at every level, with pairings `μₙ : Fₙ ⊗ F'ₙ ⟶ ℤ/ℓⁿ⁺¹` which
are perfect on the geometric fibres of `Y`, `F'ₙ|_Y` being lisse with flat fibres. Then for
`i ≤ 2d` there is a perfect `ℚ_ℓ`-bilinear pairing `β` of `Hⁱ(Y, F ⊗ ℚ_ℓ)` and
`H^{2d-i}(Y, F' ⊗ ℚ_ℓ)` with `β(π^* v, π^* w) = q^d β(v, w)`, `q = p ^ q` the cardinality of
`k` and `π^*` the geometric Frobenius. -/
theorem LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_topFrobenius [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hC : ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z)
    (F F' : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F n))))
    (hF' : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n))
    (hP' : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F' n))))
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
            (μ n))).hom))
    (i : ℕ) (hi : i ≤ 2 * d) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar F i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar F' (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ ∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard F i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard F' (2 * d - i)).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w := by
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹IsProper f›
  have hTop := topCohomologyPointClass ℓ kbar hℓ
  obtain ⟨ε, hl, hr, hε⟩ := LAdicSheaf.exists_levelPairing B X ℓ f kbar p q hcard d hℓ
    (fun h _ => poincareDualityCore_of_leaves ℓ kbar h (properCurveRelativeDualityInput ℓ kbar))
    hTop
    (nonempty_ext_unitSheaf_top_addEquiv_zmod_pow ℓ hℓ
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d)
    hC
    F F' μ hlisse hflat hμ i hi
  exact LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_levelPairing B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard F F' hF hP hF' hP' i (2 * d - i)
    ((p ^ q) ^ d) ε hl hr hε

/-- **The `q^d`-equivariant perfect Poincaré pairing on `Hⁱ(X_k̄, F ⊗ ℚ_ℓ)` for `X` smooth and
proper with a rational point.** Let `X` be proper over the finite field `k` with `p ^ q`
elements and a `k`-rational point, `k̄` algebraically closed, `Y = X_k̄` connected and smooth of
relative dimension `d` over `k̄`, `ℓ` invertible in `k̄`, and `F`, `F'` ℓ-adic sheaves with flat
levels and perfect `RΓ(X_k̄, -)` at every level, with pairings `μₙ : Fₙ ⊗ F'ₙ ⟶ ℤ/ℓⁿ⁺¹` which
are perfect on the geometric fibres of `Y`, `F'ₙ|_Y` being lisse with flat fibres. Then for
`i ≤ 2d` there is a perfect `ℚ_ℓ`-bilinear pairing `β` of `Hⁱ(Y, F ⊗ ℚ_ℓ)` and
`H^{2d-i}(Y, F' ⊗ ℚ_ℓ)` with `β(π^* v, π^* w) = q^d β(v, w)`, `q = p ^ q` the cardinality of
`k` and `π^*` the geometric Frobenius. -/
theorem LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_rationalPoint [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (F F' : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F n))))
    (hF' : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n))
    (hP' : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F' n))))
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
            (μ n))).hom))
    (i : ℕ) (hi : i ≤ 2 * d) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar F i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar F' (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ ∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard F i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard F' (2 * d - i)).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w := by
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹IsProper f›
  exact LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_topFrobenius B X ℓ f kbar p q hcard d hℓ
    (constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass B X ℓ f
      kbar p q hcard d hℓ hpt (topCohomologyPointClass ℓ kbar hℓ))
    F F' hF hP hF' hP' μ hlisse hflat hμ i hi

/-- **The `q^d`-equivariant perfect Poincaré pairing between `Hⁱ(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` and
`H^{2d-i}(X_k̄, ℱ_{ρ₀^∨} ⊗ ℚ_ℓ)`** for `X` connected, proper and smooth of relative dimension `d`
over the finite field `k` with `p ^ q` elements, with `X_k̄` connected and the Frobenius acting
on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` as `q^d` (`hC`; true when `X` has a rational point),
`k̄` an algebraic closure of `k`, `ℓ ≠ p`, and `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous; `ℱ_{ρ₀^∨}`
is the sheaf of the contragredient of the integral model of `ρ`
(`Stacks.EtaleCohomology.LAdicSheaf.representationDualSheaf`). Every coefficient hypothesis of
`Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_topFrobenius` is
discharged as in `Stacks.EtaleCohomology.LAdicSheaf.representationDualPairingInput`. -/
theorem LAdicSheaf.exists_isPerfPair_rationalFrobenius_representationSheaf_of_topFrobenius
    [IsAlgClosure k kbar] (hℓ : ℓ ≠ p) [ConnectedSpace X.1] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hC : ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z)
    (x : GeometricPoint X.1) {r : ℕ}
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (i : ℕ) (hi : i ≤ 2 * d) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x ρ hρ)
          i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationDualSheaf B X x ρ hρ)
          (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ ∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationDualSheaf B X x ρ hρ) (2 * d - i)).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have := compactSpace_etaleFundamentalGroup X.1 x
  have : SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹_›
  have hℓu : IsUnit (ℓ : kbar) := isUnit_natCast_of_ne_charP ℓ (k := k) kbar p hℓ
  obtain ⟨μ, hμ⟩ := LAdicSheaf.representationLevelPairingInput B ℓ k kbar X f x ρ hρ
  exact LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_topFrobenius B X ℓ f kbar p q hcard d
    hℓu hC _ _
    (powExact_etaleLevel_representationLAdicSheaf B X x (integralModel ρ hρ)
      (continuous_integralModel ρ hρ))
    (fun n => isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf B X
      ℓ x (integralModel ρ hρ) (continuous_integralModel ρ hρ) f (CompactificationOf.ofProper f)
      kbar p q hcard hℓ n)
    (LAdicSheaf.powExact_etaleLevel_representationDualSheaf B X x ρ hρ)
    (fun n => isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf B X
      ℓ x (contragredient (integralModel ρ hρ))
      (continuous_contragredient (continuous_integralModel ρ hρ)) f (CompactificationOf.ofProper f)
      kbar p q hcard hℓ n)
    μ
    (fun n => isFiniteTypeLocallyConstant_inverseImage_extensionByZero_ofProper _ f kbar _
      (isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf B X x _ _ n))
    (fun n Ω _ _ s => flat_sheafFiber_inverseImage_extensionByZero_of_powExact
      (CompactificationOf.ofProper f).immersion (fieldBaseChangeProj (Over.mk f) kbar) _
      (LAdicSheaf.powExact_etaleLevel_representationDualSheaf B X x ρ hρ n) Ω s)
    hμ i hi

/-- **The `q^d`-equivariant perfect Poincaré pairing between `Hⁱ(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` and
`H^{2d-i}(X_k̄, ℱ_{ρ₀^∨} ⊗ ℚ_ℓ)`** for `X` connected, proper and smooth of relative dimension `d`
over the finite field `k` with `p ^ q` elements, with a `k`-rational point and `X_k̄` connected,
`k̄` an algebraic closure of `k`, `ℓ ≠ p`, and `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous; `ℱ_{ρ₀^∨}`
is the sheaf of the contragredient of the integral model of `ρ`
(`Stacks.EtaleCohomology.LAdicSheaf.representationDualSheaf`). Every coefficient hypothesis of
`Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_rationalFrobenius_of_rationalPoint` is
discharged as in `Stacks.EtaleCohomology.LAdicSheaf.representationDualPairingInput`. -/
theorem LAdicSheaf.exists_isPerfPair_rationalFrobenius_representationSheaf_of_rationalPoint
    [IsAlgClosure k kbar] (hℓ : ℓ ≠ p) [ConnectedSpace X.1] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (x : GeometricPoint X.1) {r : ℕ}
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (i : ℕ) (hi : i ≤ 2 * d) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x ρ hρ)
          i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationDualSheaf B X x ρ hρ)
          (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ ∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationDualSheaf B X x ρ hρ) (2 * d - i)).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹_›
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹IsProper f›
  have hℓu : IsUnit (ℓ : kbar) := isUnit_natCast_of_ne_charP ℓ (k := k) kbar p hℓ
  exact LAdicSheaf.exists_isPerfPair_rationalFrobenius_representationSheaf_of_topFrobenius B X ℓ f
    kbar p q hcard hℓ d
    (constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass B X ℓ f
      kbar p q hcard d hℓu hpt (topCohomologyPointClass ℓ kbar hℓu)) x ρ hρ i hi

/-- **The Frobenius on the top cohomology of `ℱ_1` at a rational point.** For `X` connected,
proper and smooth of relative dimension `d` over the finite field `k` with `p ^ q` elements, with
a `k`-rational point and `X_k̄` connected, if the Frobenius acts as the identity on
`H⁰(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` (`ℱ_1` the sheaf of the trivial representation), then it acts on
`H^{2d}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` as multiplication by `q^d`, and the two spaces have the same
dimension: Poincaré duality between them is a `q^d`-duality against the identity. -/
theorem LAdicSheaf.rationalFrobenius_top_representationSheaf_one_of_rationalPoint
    [IsAlgClosure k kbar] (hℓ : ℓ ≠ p) [ConnectedSpace X.1] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (x : GeometricPoint X.1) {r : ℕ}
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]))
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
      ((2 * d : ℕ) : ℤ))]
    (hF0 : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
      0).hom = LinearMap.id) :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.representationSheaf B X x 1 h1)
      ((2 * d : ℕ) : ℤ)).hom = (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) • LinearMap.id ∧
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
      ((2 * d : ℕ) : ℤ)) =
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1) 0) := by
  have h := LAdicSheaf.exists_isPerfPair_rationalFrobenius_representationSheaf_of_rationalPoint B
    X ℓ f kbar p q hcard hℓ d hpt x 1 h1 (2 * d) le_rfl
  rw [Weil.LAdicSheaf.representationDualSheaf_one] at h
  have hj : (2 * (d : ℤ) - ((2 * d : ℕ) : ℤ)) = 0 := by push_cast; ring
  rw [hj] at h
  obtain ⟨β, hperf, hβ⟩ := h
  have hc : (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  have hd := LinearMap.IsFrobeniusDuality.of_isPerfPair_natCast (B := β) hc hβ
  exact ⟨hd.eq_smul_id_of_right_eq_id hF0, Module.finrank_of_isPerfPair β⟩

end RationalPoint

end Stacks.EtaleCohomology

end
