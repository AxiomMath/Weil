module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RationalPoincareDualityIsogeny
public import Weil.Attr

/-!
# Isomorphic ℓ-adic sheaves have conjugate Frobenius actions on cohomology

Let `X` be a scheme of finite type and separated over a finite field `k`, with a
compactification `j`, let `k̄` be a field over `k`, and let `u : F ≅ G` be an isomorphism of
ℓ-adic sheaves on `X`. The map induced by `u` on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` is a `ℚ_ℓ`-linear
isomorphism `h : Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, G ⊗ ℚ_ℓ)` with `h ∘ Fr_F = Fr_G ∘ h`, where
`Fr` is the geometric Frobenius. More generally this holds for an isogeny `φ : F ⟶ G`,
`ψ : G ⟶ F` (`φ ≫ ψ = ℓᴺ`, `ψ ≫ φ = ℓᴺ`); an isomorphism is the case `N = 0`.

For `X` proper over `k` one takes `j = CompactificationOf.ofProper f`, and `Hⁱ_c = Hⁱ`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.exists_linearEquiv_comp_frobenius_eq_of_isogeny`: the
  statement for an isogeny.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_linearEquiv_comp_frobenius_eq_of_iso`: the
  statement for an isomorphism of ℓ-adic sheaves.

## Implementation notes

The statement is made for an arbitrary compactification `j` and an arbitrary degree `i : ℤ`;
the proper case with `ν ≥ 0` is the specialisation `j = CompactificationOf.ofProper f`,
`i = ν`. The cohomology is the compactly supported ℓ-adic cohomology tensored with `ℚ_ℓ`, and the
Frobenius is the canonical geometric Frobenius of the Stacks project.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Isogenous ℓ-adic sheaves have conjugate Frobenius actions on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`**:
there is a `ℚ_ℓ`-linear isomorphism `h` with `h ∘ Fr_F = Fr_G ∘ h`. -/
theorem LAdicSheaf.exists_linearEquiv_comp_frobenius_eq_of_isogeny {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ) :
    ∃ h : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ≃ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i,
      h.toLinearMap ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom =
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G
            i).hom ∘ₗ h.toLinearMap :=
  ⟨(LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
      i).toLinearEquiv,
    LinearMap.ext fun v =>
      LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius B X ℓ f j
        kbar p q hcard φ ψ N h₁ h₂ i v⟩

/-- **Isomorphic ℓ-adic sheaves have conjugate Frobenius actions on cohomology**: an
isomorphism `u : F ≅ G` of ℓ-adic sheaves on `X` gives a `ℚ_ℓ`-linear isomorphism
`h : Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, G ⊗ ℚ_ℓ)` with `h ∘ Fr_F = Fr_G ∘ h`. For `X` proper over
`k` and `j = CompactificationOf.ofProper f` this is `Hⁱ(X_k̄, - ⊗ ℚ_ℓ)`. -/
@[weil "lem_fk404_frobenius_cohomology_conjugate_under_sheaf_iso"]
theorem LAdicSheaf.exists_linearEquiv_comp_frobenius_eq_of_iso {F G : LAdicSheaf B X ℓ}
    (e : F ≅ G) (i : ℤ) :
    ∃ h : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ≃ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i,
      h.toLinearMap ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom =
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G
            i).hom ∘ₗ h.toLinearMap :=
  LAdicSheaf.exists_linearEquiv_comp_frobenius_eq_of_isogeny B X ℓ f j kbar p q hcard e.hom e.inv 0
    (by simp) (by simp) i

end Stacks.EtaleCohomology

end
