module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilIIPurityAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveRelativeDualityInputProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssemblyLeaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationLevelPairingPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.LAdicSkewPairing
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.CupSkewConstantCoefficients
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.TrivialRepresentationDual

/-!
# The alternating middle Poincaré pairing

Let `X` be proper over a finite field `k` with `q = p ^ q₀` elements, `k̄` an algebraically closed
extension, `Y = X_k̄` connected and smooth of relative dimension `d`, `ℓ` a prime invertible in `k̄`
and `F` an ℓ-adic sheaf on `X` with a pairing `μₙ : Fₙ ⊗ Fₙ → ℤ/ℓⁿ⁺¹` at every level. The
finite level Poincaré pairing in the middle degree

`εₙ(x, y) = t(φ x ∪_{μₙ} φ y) : H^d(X_k̄, Fₙ) × H^d(X_k̄, Fₙ) → H^{2d}(Y, ℤ/ℓⁿ⁺¹) ≅ ℤ/ℓⁿ⁺¹`

is built with one and the same identification `φ` of `H^d(X_k̄, Fₙ)` with `Ext^d(ℤ/ℓⁿ⁺¹, Fₙ|_Y)`
on both sides. Hence when the cup product of degree `d` classes is skew-symmetric, so is `εₙ`.
Passing to `⊗ ℚ_ℓ` with a skew-symmetric compactness argument gives a perfect, alternating
`ℚ_ℓ`-pairing on `H^d(X_k̄, F ⊗ ℚ_ℓ)` multiplied by `q^d` under the geometric Frobenius.

## Main results

* `Weil.LAdicSheaf.exists_skew_levelPairing`: skew-symmetric nondegenerate level pairings on
  `H^d(X_k̄, Fₙ)` with Frobenius factor `q^d`, from skew-symmetry of the cup product.
* `Weil.LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_skew_levelPairing`:
  skew-symmetric level pairings with Frobenius factor `c` give an alternating perfect
  `ℚ_ℓ`-pairing with factor `c`.
* `Weil.LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_rationalPoint`: the
  `q^d`-equivariant alternating perfect pairing on `H^d(X_k̄, F ⊗ ℚ_ℓ)` for `X` with a rational
  point.
* `Weil.LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_representationSheaf_one`:
  the same for the constant coefficients `ℱ_1` and `d` odd, with no further hypothesis, the cup
  product being anticommutative by `Weil.LAdicSheaf.cup_skew_representationSheaf_one`.

## Implementation notes

The skew-symmetry of the cup product `Ext^d(𝟙, Mₙ) × Ext^d(𝟙, Mₙ) → Ext^{2d}(𝟙, ℤ/ℓⁿ⁺¹)` is an
input (`hcup`); for odd `d` and constant coefficients it is the graded commutativity of the
Yoneda algebra of the unit. The statements consume objects defined in the standard model
`HasDerivedCategory.standard` of the derived category, which is therefore a local instance here.
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

section Main

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

set_option maxHeartbeats 400000 in
-- The nondegeneracy step unifies `Ext (𝟙_ _) (constantModuleSheaf _ _)` with
-- `Ext (unitSheaf _) (unitSheaf _)`, which needs more than the default heartbeats.
/-- **Skew-symmetric finite-level Poincaré pairings in the middle degree.** In the setting of
`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing` with `F' = F` and `i = d`, if the cup
product `Ext^d(ℤ/ℓⁿ⁺¹, Fₙ|_Y) × Ext^d(ℤ/ℓⁿ⁺¹, Fₙ|_Y) → Ext^{2d}(ℤ/ℓⁿ⁺¹, ℤ/ℓⁿ⁺¹)` along the pulled
back pairing `μₙ` is skew-symmetric, then there are pairings
`εₙ : H^d(X_k̄, Fₙ) × H^d(X_k̄, Fₙ) → ℤ/ℓⁿ⁺¹`, nondegenerate on both sides, scaled by `q^d` under
the canonical geometric Frobenius, and skew-symmetric. -/
theorem LAdicSheaf.exists_skew_levelPairing [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hℓ : IsUnit (ℓ : kbar))
    (hcore : IsUnit (ℓ : kbar) → LocalPurity ℓ kbar → PoincareDualityCore ℓ kbar)
    (hD1 : TopCohomologyPointClass ℓ kbar)
    (hA1 : ∀ m : ℕ, Nonempty (Ext (unitSheaf (X := fieldBaseChange (Over.mk f) kbar) (ℓ ^ (m + 1)))
      (unitSheaf (ℓ ^ (m + 1))) (2 * d) ≃+ ZMod (ℓ ^ (m + 1))))
    (hC : ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z)
    (F : LAdicSheaf B X ℓ)
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
    ∃ ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
          kbar d).obj (LAdicSheaf.padicLevel B X ℓ F n) →+
        (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
          d).obj (LAdicSheaf.padicLevel B X ℓ F n) →+ ZMod (ℓ ^ (n + 1)),
      (∀ n x, (∀ y, ε n x y = 0) → x = 0) ∧ (∀ n y, (∀ x, ε n x y = 0) → y = 0) ∧
      (∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
          (CompactificationOf.ofProper f) kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) d).hom x)
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
            d).hom y) = (((p ^ q) ^ d : ℕ) : ZMod (ℓ ^ (n + 1))) * ε n x y) ∧
      ∀ n x y, ε n x y = -ε n y x := by
  have hji : d + d = 2 * d := by omega
  choose Φ hΦ using fun n => LAdicSheaf.exists_addEquiv_level_frobenius B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard F d n
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) inferInstance
  have hExt : ∀ n : ℕ, HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar)) := fun n => etaleModules_hasExt _ (ZMod (ℓ ^ (n + 1)))
  let t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar)))
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d) →+ ZMod (ℓ ^ (n + 1)) :=
    fun n => (hA1 n).some.toAddMonoidHom
  let μY := fun n => inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
    (ℓ ^ (n + 1)) (μ n)
  let M := fun n => (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk f) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))
  have hT₁ : ∀ n, (MonoidalCategory.tensorRight (M n)).Additive := fun n =>
    (tensorRight_exact_of_flat (M n) (hflat n)).1
  have hT₂ : ∀ n, PreservesFiniteLimits (MonoidalCategory.tensorRight (M n)) := fun n =>
    (tensorRight_exact_of_flat (M n) (hflat n)).2.1
  have hT₃ : ∀ n, PreservesFiniteColimits (MonoidalCategory.tensorRight (M n)) := fun n =>
    (tensorRight_exact_of_flat (M n) (hflat n)).2.2
  let φ : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
        kbar d).obj (LAdicSheaf.padicLevel B X ℓ F n) ≃+ Ext.{u + 1}
      (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar))) (M n) d :=
    fun n => Φ n
  let ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
        kbar d).obj (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
        d).obj (LAdicSheaf.padicLevel B X ℓ F n) →+ ZMod (ℓ ^ (n + 1)) :=
    fun n => AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y =>
      t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ n y) hji)) (fun y y' => by
        rw [map_add (φ n) y y',
          Stacks.ExtCup.cup_add (μY n) hji (φ n x) (φ n y) (φ n y')]
        exact map_add (t n) _ _)) (fun x x' => by
        ext y
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          Stacks.ExtCup.add_cup])
  have hε : ∀ n x y, ε n x y = t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ n y) hji) :=
    fun _ _ _ => rfl
  have hnd : ∀ n,
      (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (M n) d,
        (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (M n) d,
            t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji) = 0) → a = 0) ∧
      (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (M n) d,
        (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (M n) d,
            t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji) = 0) → b = 0) := fun n => by
    exact Stacks.ExtCup.cup_nondegenerate.{u + 1, _, _} (μY n) (p := ℓ) (m := n + 1) (t n) hji
      (bijective_tensorPairingExt (M n) (M n) (hlisse n) (hflat n) (μY n) (hμ n) d)
      (isDualityPerfect_levelPow_of_isFiniteTypeLocallyConstant ℓ hℓ hcore hD1
        (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d hA1 n (t n)
        (hA1 n).some.injective (M n) (hlisse n))
  refine ⟨ε, fun n x hx => ?_, fun n y hy => ?_, fun n x y => ?_, fun n x y => ?_⟩
  · refine (φ n).injective ((((hnd n).1 (φ n x) fun b => ?_)).trans (map_zero _).symm)
    obtain ⟨y, rfl⟩ := (φ n).surjective b
    exact hx y
  · refine (φ n).injective ((((hnd n).2 (φ n y) fun a => ?_)).trans (map_zero _).symm)
    obtain ⟨x, rfl⟩ := (φ n).surjective a
    exact hy x
  · let πb := geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard
    let G' := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) πb).obj (M n)
    have hG' := tensorRight_exact_of_flat G'
      (flat_sheafFiber_inverseImage πb (M n) (hflat n))
    have := hG'.1
    have := hG'.2.1
    have := hG'.2.2
    have key := cup_adjunctionExtMap_frobeniusBaseChangeTwist (ℓ ^ (n + 1)) (Over.mk f) kbar p q
      hcard (μ n) hji (φ n x) (φ n y)
    have h₁ : ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
          (CompactificationOf.ofProper f) kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) d).hom x)
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
            d).hom y) =
        t n (constantExtRestriction (ZMod (ℓ ^ (n + 1))) πb (2 * d)
          (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ n y) hji)) := by
      change t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n _) (φ n _) hji) = _
      rw [← key]
      exact congrArg₂ (fun a b => t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji))
        (hΦ n x) (hΦ n y)
    refine h₁.trans ((congrArg (t n) (hC n _)).trans ?_)
    exact (map_nsmul (t n) _ _).trans (nsmul_eq_mul _ _)
  · rw [hε, hε, hcup n (φ n x) (φ n y) hji, map_neg]

end Main


section LevelPairing

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **An alternating perfect `ℚ_ℓ`-pairing from skew-symmetric finite level pairings.** If the
levels of `F` are flat with perfect `RΓ_c(X_k̄, -)`, and for every `n` a skew-symmetric pairing
`εₙ` of `Hⁱ_c(X_k̄, Fₙ)` with itself, with values in `ℤ/ℓⁿ⁺¹`, is nondegenerate and multiplied by
`c` under the geometric Frobenius, then there is a perfect `ℚ_ℓ`-bilinear pairing `β` of
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` with itself, with `β(π^* v, π^* w) = c β(v, w)` and `β(v, v) = 0`. -/
theorem LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_skew_levelPairing
    (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    (i : ℤ) (c : ℕ)
    (ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+ ZMod (ℓ ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → x = 0)
    (hε : ∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x)
      ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom y) =
        (c : ZMod (ℓ ^ (n + 1))) * ε n x y)
    (hskew : ∀ n x y, ε n x y = -ε n y x) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i →ₗ[ℚ_[ℓ]]
          ℚ_[ℓ],
      β.IsPerfPair ∧ (∀ v w,
        β ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom w) = (c : ℚ_[ℓ]) * β v w) ∧ ∀ v, β v v = 0 := by
  let e := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    Stacks.InverseSystem.finite_limit_of_iso _ i e
  obtain ⟨c₁, h₁⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _ i e
  exact LAdicPairing.exists_isPerfPair_extendScalars_of_levels_of_skew
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i) c c₁
    (fun n =>
      (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
          i).hom.toAddMonoidHom)
    (fun n a => congrArg (fun φ => φ.hom a)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F i n))
    (fun n => (h₁ n).1) (fun n => (h₁ n).2) ε hl hε hskew

end LevelPairing

section RationalPoint

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The `q^d`-equivariant alternating perfect Poincaré pairing on `H^d(X_k̄, F ⊗ ℚ_ℓ)` for `X`
smooth and proper with a rational point.** Let `X` be proper over the finite field `k` with
`p ^ q` elements and a `k`-rational point, `k̄` algebraically closed, `Y = X_k̄` connected and
smooth of relative dimension `d` over `k̄`, `ℓ` invertible in `k̄`, and `F` an ℓ-adic sheaf with
flat levels and perfect `RΓ(X_k̄, -)` at every level, with pairings `μₙ : Fₙ ⊗ Fₙ ⟶ ℤ/ℓⁿ⁺¹`
which are perfect on the geometric fibres of `Y`, `Fₙ|_Y` being lisse with flat fibres. If the
cup product along `μₙ` of degree `d` classes is skew-symmetric, then there is a perfect,
alternating `ℚ_ℓ`-bilinear pairing `β` of `H^d(Y, F ⊗ ℚ_ℓ)` with itself, with
`β(π^* v, π^* w) = q^d β(v, w)`, `q = p ^ q` the cardinality of `k` and `π^*` the geometric
Frobenius. -/
theorem LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_rationalPoint
    [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (F : LAdicSheaf B X ℓ)
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
    (constantExtRestriction_geometricFrobeniusBaseChange_top_of_topCohomologyPointClass B X ℓ f
      kbar p q hcard d hℓ hpt hTop)
    F μ hlisse hflat hμ hcup
  exact LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_skew_levelPairing B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard F hF hP d ((p ^ q) ^ d) ε hl hε hskew


/-- **The `q^d`-equivariant alternating perfect Poincaré pairing on `H^d(X_k̄, ℚ_ℓ)`, `d` odd.**
Let `X` be connected, proper and smooth of relative dimension `d` odd over the finite field `k`
with `p ^ q` elements, with a `k`-rational point and `X_k̄` connected, `k̄` an algebraic closure
of `k` and `ℓ ≠ p`. For `ℱ_1` the ℓ-adic sheaf of the trivial rank-one representation (the
constant sheaf `ℤ_ℓ`), there is a perfect alternating `ℚ_ℓ`-bilinear pairing `β` of
`H^d(X_k̄, ℱ_1 ⊗ ℚ_ℓ)` with itself, with `β(π^* v, π^* w) = q^d β(v, w)`, `π^*` the geometric
Frobenius. -/
theorem LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_representationSheaf_one
    [IsAlgClosure k kbar] (hℓ : ℓ ≠ p) [ConnectedSpace X.1] (d : ℕ) (hd : Odd d)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (x : GeometricPoint X.1)
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
  exact LAdicSheaf.exists_alternating_isPerfPair_rationalFrobenius_of_rationalPoint B X ℓ f kbar
    p q hcard d hℓu hpt _ hF
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

end RationalPoint

end Weil

end
