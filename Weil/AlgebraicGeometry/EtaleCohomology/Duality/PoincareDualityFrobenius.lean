module

public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobeniusOfCoprimeDegrees

/-!
# Poincaré duality with Frobenius on `H(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`, without a rational point

Let `X` be connected, proper and smooth of relative dimension `d` over a finite field `k` with
`q` elements, with `X_k̄` connected, and `ℱ_1` the ℓ-adic sheaf of the trivial representation.
For `0 ≤ i ≤ 2d` there is a `q^d`-duality (`LinearMap.IsFrobeniusDuality`) for the Frobenius on
`Hⁱ(X_k̄, ℱ_1 ⊗ ℚ_ℓ) × H^{2d-i}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`. No rational point is assumed: `X` has closed
points of degree dividing every large `N`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_closedPoint_residueDegree_dvd_of_frobeniusTrivialOnH0`),
in particular of degrees dividing two coprime integers, which makes the Frobenius act on
`H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` as `q^d`
(`Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_top_of_coprime`), the
input of finite level Poincaré duality.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isFrobeniusDuality_representationSheaf_one`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
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
  {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The Frobenius on `H^{2d}(X_k̄, ℤ/ℓⁿ⁺¹)` is `q^d`, without a rational point**, given that the
Frobenius is trivial on `H⁰` over the extensions of `k` where `X` acquires a rational point. -/
theorem constantExtRestriction_geometricFrobeniusBaseChange_top_of_frobeniusTrivialOnH0
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hH0 : LAdicSheaf.FrobeniusTrivialOnH0FieldExtension B ℓ kbar p X f) :
    ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z := by
  have : SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹_›
  obtain ⟨N₀, hN₀⟩ := LAdicSheaf.exists_closedPoint_residueDegree_dvd_of_frobeniusTrivialOnH0 B ℓ
    kbar p q hcard hℓ X f d hH0
  refine constantExtRestriction_geometricFrobeniusBaseChange_top_of_coprime B X ℓ f kbar p q hcard
    d hℓ N₀ (N₀ + 1) (Nat.coprime_self_add_right.2 (Nat.coprime_one_right N₀)) ?_
  intro m hm
  have hm' : N₀ ≤ m := by
    rcases hm with rfl | hm
    · exact le_rfl
    · rw [Set.mem_singleton_iff] at hm
      omega
  obtain ⟨y, hy⟩ := hN₀ m hm'
  exact ⟨y.1, y.2, hy⟩

/-- **Poincaré duality with Frobenius on `H(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`, without a rational point.** For `X`
connected, proper and smooth of relative dimension `d` over the finite field `k` with `p ^ q`
elements, with `X_k̄` connected, `ℓ ≠ p`, and `0 ≤ i ≤ 2d`, there is a `q^d`-duality for the
Frobenius on `Hⁱ(X_k̄, ℱ_1 ⊗ ℚ_ℓ) × H^{2d-i}(X_k̄, ℱ_1 ⊗ ℚ_ℓ)`, given that the Frobenius is
trivial on `H⁰` over the extensions of `k` where `X` acquires a rational point. -/
theorem LAdicSheaf.exists_isFrobeniusDuality_representationSheaf_one (hℓ : ℓ ≠ p) (X : B.Scheme)
    [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hH0 : LAdicSheaf.FrobeniusTrivialOnH0FieldExtension B ℓ kbar p X f)
    (x : GeometricPoint X.1) {r : ℕ}
    (h1 : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])) (i : ℕ)
    (hi : i ≤ 2 * d) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
          i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x 1 h1)
          (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      ∃ hc : (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) ≠ 0,
        β.IsFrobeniusDuality
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x 1 h1) i).hom
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard
            (LAdicSheaf.representationSheaf B X x 1 h1) (2 * d - i)).hom
          (Units.mk0 _ hc) := by
  have h := LAdicSheaf.exists_isPerfPair_rationalFrobenius_representationSheaf_of_topFrobenius B X
    ℓ f kbar p q hcard hℓ d
    (constantExtRestriction_geometricFrobeniusBaseChange_top_of_frobeniusTrivialOnH0 B ℓ kbar p q
      hcard hℓ X f d hH0) x 1 h1 i hi
  rw [Weil.LAdicSheaf.representationDualSheaf_one] at h
  obtain ⟨β, hperf, hβ⟩ := h
  have hc : (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  exact ⟨β, hc, LinearMap.IsFrobeniusDuality.of_isPerfPair_natCast hc hβ⟩

end Stacks.EtaleCohomology

end
