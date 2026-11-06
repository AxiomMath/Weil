module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRestrictionIsogeny
public import WeilFrontier.LinearAlgebra.PerfectPairing.FrobeniusDuality

/-!
# Frobenius dualities on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` transport along isogenies

An isogeny `φ : F ⟶ G`, `ψ : G ⟶ F` of ℓ-adic sheaves (`φ ≫ ψ = ℓᴺ`, `ψ ≫ φ = ℓᴺ`) induces an
isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, G ⊗ ℚ_ℓ)`
(`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso`)
commuting with the geometric Frobenius. So a `c`-duality for the Frobenius of `(G, G')` gives one
for that of `(F, F')`.

## Main results

* `LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius`
  (the name is long): the isomorphism intertwines the Frobenius endomorphisms.
* `Stacks.EtaleCohomology.LAdicSheaf.isFrobeniusDuality_compl₁₂_isogenyIso`: transport of a
  `c`-duality along two isogenies.
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

/-- The isomorphism of `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` induced by an isogeny intertwines the geometric
Frobenius endomorphisms. -/
theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
        i).hom.hom ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
          hcard F i).hom v) =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G i).hom
        ((LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
          h₁ h₂ i).hom.hom v) := by
  have h := congrArg (fun g => g.hom v)
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B X ℓ f j kbar
      φ ψ N h₁ h₂ i (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- **Transport of a Frobenius duality along isogenies.** If `F ⇄ G` and `F' ⇄ G'` are isogenies
and `β` is a `c`-duality for the Frobenius on `Hⁱ_c(X_k̄, G ⊗ ℚ_ℓ) × Hʲ_c(X_k̄, G' ⊗ ℚ_ℓ)`, then
`β` read through the induced isomorphisms is a `c`-duality for the Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) × Hʲ_c(X_k̄, F' ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.isFrobeniusDuality_compl₁₂_isogenyIso {F G F' G' : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G)
    (φ' : F' ⟶ G') (ψ' : G' ⟶ F') (N' : ℕ) (h₁' : φ' ≫ ψ' = (ℓ ^ N') • 𝟙 F')
    (h₂' : ψ' ≫ φ' = (ℓ ^ N') • 𝟙 G') (i i' : ℤ)
    {β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G' i' →ₗ[ℚ_[ℓ]]
        ℚ_[ℓ]} {c : ℚ_[ℓ]ˣ}
    (h : β.IsFrobeniusDuality
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G i).hom
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G'
        i').hom c) :
    (β.compl₁₂
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
        i).toLinearEquiv.toLinearMap
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ' ψ' N'
        h₁' h₂' i').toLinearEquiv.toLinearMap).IsFrobeniusDuality
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F' i').hom
      c :=
  h.compl₁₂_linearEquiv _ _
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius B X ℓ f j kbar
      p q hcard φ ψ N h₁ h₂ i)
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius B X ℓ f j kbar
      p q hcard φ' ψ' N' h₁' h₂' i')

end Stacks.EtaleCohomology

end
