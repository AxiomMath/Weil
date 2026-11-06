module

public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.AlternatingPoincarePairing
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityConstantSystem
public import Weil.LinearAlgebra.Matrix.BilinearForm
public import Weil.LinearAlgebra.Eigenspace.Zero

/-!
# The alternating middle Poincaré pairing on `H^d(X_k̄, ℚ_ℓ)`, without a rational point

Let `X` be proper and smooth of relative dimension `d` over a finite field `k` with `q`
elements, with `X_k̄` connected, `d` odd and `ℓ ∤ q`. The middle Poincaré pairing on
`H^d(X_k̄, ℚ_ℓ)` is perfect and alternating, and multiplied by `q^d` under the geometric
Frobenius. The only input beyond the alternating finite level pairings is that the Frobenius acts
on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` as `q^d`; for a variety with a rational point this is the point class,
and in general it follows from the existence of closed points of coprime degrees
(`constantExtRestriction_geometricFrobeniusBaseChange_top_of_frobeniusTrivialOnH0`, in the
namespace `Stacks.EtaleCohomology`).

Consequently `dim H^d(X_k̄, ℚ_ℓ)` is even, and every square root of `q^d` is an eigenvalue of
the Frobenius on `H^d(X_k̄, ℚ_ℓ)` of even multiplicity.

## Main results

* `Weil.LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_topFrobenius`: the
  alternating `q^d`-equivariant perfect pairing on `H^d(X_k̄, F ⊗ ℚ_ℓ)`, given the Frobenius on
  the top cohomology.
* `Weil.LAdicSheaf.exists_alternating_isFrobeniusDuality_constantSystem`: the same for the
  constant ℓ-adic sheaf, `d` odd, without a rational point.
* `Weil.exists_alternating_isFrobeniusDuality_rationalFrobenius`: the same for
  `Weil.rationalFrobenius` on `Weil.rationalCohomology`.
* `Weil.even_finrank_and_even_rootMultiplicity_rationalFrobenius_of_odd`: `dim H^d(X_k̄, ℚ_ℓ)`
  is even and the square roots of `q^d` have even multiplicity in the characteristic polynomial
  of the Frobenius.

## Implementation notes

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius
open Stacks.EtaleCohomology Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Weil

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

section Pairing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

section TopFrobenius

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The `q^d`-equivariant alternating perfect Poincaré pairing on `H^d(X_k̄, F ⊗ ℚ_ℓ)`, given
the Frobenius on the top cohomology.** As
`Weil.LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_rationalPoint`, with the
rational point replaced by its only consequence used: the geometric Frobenius acts on
`H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` as multiplication by `q^d` for every `n`. -/
theorem LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_topFrobenius
    [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hC : ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z)
    (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F n))))
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n)))))
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
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
            (μ n))).hom))
    (hcup : ∀ (n : ℕ)
      [Functor.Additive (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))))]
      [PreservesFiniteLimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))))]
      [PreservesFiniteColimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))))]
      (a b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))) d)
      (h : d + d = 2 * d),
      Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) a b h =
        -Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
          (ℓ ^ (n + 1)) (μ n)) b a h) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar F d →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar F d →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ (∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard F d).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard F d).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w) ∧ ∀ v, β v v = 0 := by
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹IsProper f›
  have hTop := topCohomologyPointClass ℓ kbar hℓ
  obtain ⟨ε, hl, -, hε, hskew⟩ := LAdicSheaf.exists_skew_levelPairing B X ℓ f kbar p q hcard d hℓ
    (fun h _ => poincareDualityCore_of_leaves ℓ kbar h (properCurveRelativeDualityInput ℓ kbar))
    hTop
    (nonempty_ext_unitSheaf_top_addEquiv_zmod_pow ℓ hℓ
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d)
    hC
    F μ hlisse hflat hμ hcup
  exact LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_skew_levelPairing B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard F hF hP d ((p ^ q) ^ d) ε hl hε hskew

/-- **The alternating `q^d`-equivariant pairing on `H^d(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`, `d` odd, given the
Frobenius on the top cohomology.** As
`Weil.LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_representationSheaf_one`, with
the rational point replaced by the action of the Frobenius on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` as `q^d`. -/
theorem LAdicSheaf.exists_alternating_isPerfPair_representationSheaf_one_of_topFrobenius
    [IsAlgClosure k kbar] (hℓ : ℓ ≠ p) [ConnectedSpace X.1] (d : ℕ) (hd : Odd d)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hC : ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z)
    (x : GeometricPoint X.1)
    (hρ : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 hρ)
          d →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 hρ)
          d →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ (∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x 1 hρ) d).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x 1 hρ) d).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w) ∧ ∀ v, β v v = 0 := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have := compactSpace_etaleFundamentalGroup X.1 x
  have : SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹_›
  have hℓu : IsUnit (ℓ : kbar) := isUnit_natCast_of_ne_charP ℓ (k := k) kbar p hℓ
  have h := LAdicSheaf.representationLevelPairingInput B ℓ k kbar X f x 1 hρ
  rw [LAdicSheaf.representationDualSheaf_one] at h
  obtain ⟨μ, hμ⟩ := h
  have hF := powExact_etaleLevel_representationLAdicSheaf B X x (integralModel 1 hρ)
    (continuous_integralModel 1 hρ)
  exact LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_topFrobenius B X ℓ f kbar
    p q hcard d hℓu hC _ hF
    (fun n => isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf B X
      ℓ x (integralModel 1 hρ) (continuous_integralModel 1 hρ) f (CompactificationOf.ofProper f)
      kbar p q hcard hℓ n)
    μ
    (fun n => isFiniteTypeLocallyConstant_inverseImage_extensionByZero_ofProper _ f kbar _
      (isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf B X x _ _ n))
    (fun n Ω _ _ s => flat_sheafFiber_inverseImage_extensionByZero_of_powExact
      (CompactificationOf.ofProper f).immersion (fieldBaseChangeProj (Over.mk f) kbar) _
      (hF n) Ω s)
    hμ (LAdicSheaf.cup_skew_representationSheaf_one B X ℓ f kbar x hρ hd μ)

/-- **The alternating `q^d`-equivariant pairing on `H^d(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`, `d` odd, without a
rational point.** For `X` proper and smooth of relative dimension `d` odd over the finite field
`k` with `p ^ q` elements, `k̄` an algebraic closure of `k`, `X_k̄` connected (so `X` is, which
the étale fundamental group of `X` needs) and `ℓ ≠ p`, there
is a perfect alternating `ℚ_ℓ`-bilinear pairing `β` of `H^d(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` with itself, with
`β(π^* v, π^* w) = q^d β(v, w)`, `π^*` the geometric Frobenius. -/
theorem LAdicSheaf.exists_alternating_isPerfPair_representationSheaf_one_of_connected
    [IsAlgClosure k kbar] (hℓ : ℓ ≠ p) [ConnectedSpace X.1] (d : ℕ) (hd : Odd d)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (x : GeometricPoint X.1)
    (hρ : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 hρ)
          d →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 hρ)
          d →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      β.IsPerfPair ∧ (∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x 1 hρ) d).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x 1 hρ) d).hom w) =
          (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) * β v w) ∧ ∀ v, β v v = 0 := by
  exact LAdicSheaf.exists_alternating_isPerfPair_representationSheaf_one_of_topFrobenius
    B X ℓ f kbar p q hcard hℓ d hd
    (constantExtRestriction_geometricFrobeniusBaseChange_top_of_frobeniusTrivialOnH0
      B ℓ kbar p q hcard hℓ X f d
      (Stacks.EtaleCohomology.LAdicSheaf.frobeniusTrivialOnH0FieldExtension B ℓ kbar p X f))
    x hρ

/-- **The alternating `q^d`-duality on `H^d(X_k̄, ℚ_ℓ)`, `d` odd, without a rational point.** For
`X` proper and smooth of relative dimension `d` odd over the finite field `k` with `p ^ q`
elements, `k̄` an algebraic closure of `k`, `X_k̄` connected and `ℓ ≠ p`, there is an alternating
`ℚ_ℓ`-bilinear form `β` on `H^d(X_k̄, ℚ_ℓ)` (cohomology of the constant ℓ-adic sheaf) which is a
`q^d`-duality for the geometric Frobenius. -/
theorem LAdicSheaf.exists_alternating_isFrobeniusDuality_constantSystem [IsAlgClosure k kbar]
    [QuasiSeparatedSpace X.1] (hℓ : ℓ ≠ p) (d : ℕ) (hd : Odd d) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] :
    ∃ (β : LinearMap.BilinForm ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) d))
      (hc : (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) ≠ 0),
      β.IsFrobeniusDuality
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) d).hom
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) d).hom
        (Units.mk0 _ hc) ∧ β.IsAlt := by
  have := Stacks.EtaleCohomology.connectedSpace_of_connectedSpace_fieldBaseChange kbar X.1 f
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  let x : GeometricPoint X.1 := X.1.algClosedPoint (Classical.arbitrary X.1)
  obtain ⟨β, hperf, hβ, halt⟩ :=
    LAdicSheaf.exists_alternating_isPerfPair_representationSheaf_one_of_connected
      B X ℓ f kbar p q hcard hℓ d hd x continuous_const
  have hc : (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  have hD := LinearMap.IsFrobeniusDuality.of_isPerfPair_natCast hc hβ
  let φ := (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne (ℓ := ℓ) B X x).hom
  let ψ := (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne (ℓ := ℓ) B X x).inv
  refine ⟨_, hc, LAdicSheaf.isFrobeniusDuality_compl₁₂_isogenyIso B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard φ ψ 0 (by simp [φ, ψ]) (by simp [φ, ψ])
    φ ψ 0 (by simp [φ, ψ]) (by simp [φ, ψ]) d d hD, fun v => ?_⟩
  exact halt _

end TopFrobenius

end Pairing

section RationalCohomology

variable (B : BigEtaleSite.{u}) (S : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : S.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The alternating Poincaré `q^d`-duality on `H^d(X_k̄, ℚ_ℓ)`, `d` odd** (FK IV.1): for `X`
proper and smooth of relative dimension `d` odd over the finite field `k` with `q` elements, with
`X_k̄` connected and `ℓ ∤ q`, there is an alternating bilinear form on `H^d(X_k̄, ℚ_ℓ)` which is a
`q^d`-duality for `(F_d, F_d)`. No rational point is assumed. -/
theorem exists_alternating_isFrobeniusDuality_rationalFrobenius [Fact (ℓ ≠ ringChar k)] (d : ℕ)
    (hd : Odd d) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k))] :
    ∃ (β : LinearMap.BilinForm ℚ_[ℓ] (rationalCohomology B S f ℓ d))
      (hc : ((Fintype.card k : ℚ_[ℓ]) ^ d) ≠ 0),
      β.IsFrobeniusDuality (rationalFrobenius B S f ℓ d) (rationalFrobenius B S f ℓ d)
        (Units.mk0 _ hc) ∧ β.IsAlt := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  obtain ⟨e, -, hcard⟩ := FiniteField.card k (ringChar k)
  have hℓ : ℓ ≠ ringChar k := Fact.out
  obtain ⟨β, hc, hβ, halt⟩ := LAdicSheaf.exists_alternating_isFrobeniusDuality_constantSystem B S ℓ
    f (AlgebraicClosure k) (ringChar k) e hcard hℓ d hd
  rw [rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S f ℓ (ringChar k) e
    hcard d] at hβ
  have hq : (((ringChar k ^ (e : ℕ)) ^ d : ℕ) : ℚ_[ℓ]) = (Fintype.card k : ℚ_[ℓ]) ^ d := by
    rw [hcard]; push_cast; rfl
  refine ⟨β, hq ▸ hc, ?_, halt⟩
  convert hβ using 1
  ext
  simp [hq]

/-- **The middle cohomology of odd degree is even dimensional, and the square roots of `q^d` are
Frobenius eigenvalues of even multiplicity** (FK IV.1): for `X` proper and smooth of relative
dimension `d` odd over the finite field `k` with `q` elements, with `X_k̄` connected and `ℓ ∤ q`,
`dim H^d(X_k̄, ℚ_ℓ)` is even, and every `γ ∈ ℚ̄_ℓ` with `γ² = q^d` has even multiplicity as a
root of the characteristic polynomial of `F_d`. -/
theorem even_finrank_and_even_rootMultiplicity_rationalFrobenius_of_odd
    [Fact (ℓ ≠ ringChar k)] (d : ℕ) (hd : Odd d) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k))] :
    Even (Module.finrank ℚ_[ℓ] (rationalCohomology B S f ℓ d)) ∧
      ∀ γ : AlgebraicClosure ℚ_[ℓ],
        γ ^ 2 = algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ d) →
          Even (((rationalFrobenius B S f ℓ d).charpoly.map
            (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).rootMultiplicity γ) := by
  obtain ⟨β, hc, hβ, halt⟩ := exists_alternating_isFrobeniusDuality_rationalFrobenius B S f ℓ d hd
  exact ⟨LinearMap.BilinForm.even_finrank_of_isAlt_of_injective β halt hβ.injective_left,
    fun γ hγ => LinearMap.BilinForm.even_rootMultiplicity_charpoly_map_of_isFrobeniusDuality
      (AlgebraicClosure ℚ_[ℓ]) hβ halt hγ⟩

end RationalCohomology

end Weil

end
