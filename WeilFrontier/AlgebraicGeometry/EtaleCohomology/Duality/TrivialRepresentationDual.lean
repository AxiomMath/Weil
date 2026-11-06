module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationDualCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRationalIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels

/-!
# The dual of the trivial representation

The integral model and the contragredient of the trivial representation
`1 : G → GL_r(ℚ_ℓ)` are trivial, so the dual coefficients `ℱ_{1₀^∨}` of the sheaf `ℱ_1` of the
trivial representation are `ℱ_1` itself.

## Main results

* `Weil.integralModel_one`: the integral model of `1` is `1`.
* `Weil.contragredient_one`: the contragredient of `1` is `1`.
* `Weil.LAdicSheaf.representationDualSheaf_one`: `ℱ_{1₀^∨} = ℱ_1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Weil

/-- **The integral model of the trivial representation is trivial.** -/
theorem integralModel_one {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} (h : Continuous (1 : H →* GL (Fin r) ℚ_[ℓ])) :
    integralModel (1 : H →* GL (Fin r) ℚ_[ℓ]) h = 1 := by
  ext g a b
  have hm := congrArg (fun M : GL (Fin r) ℚ_[ℓ] => (M : Matrix (Fin r) (Fin r) ℚ_[ℓ]) a b)
    (map_integralModel (1 : H →* GL (Fin r) ℚ_[ℓ]) h g)
  simp only [MonoidHom.one_apply, mul_one, inv_mul_cancel] at hm
  exact Subtype.ext (hm.trans (by simp [Matrix.one_apply]; split_ifs <;> simp))

/-- **The contragredient of the trivial representation is trivial.** -/
theorem contragredient_one {G : Type*} [Group G] {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] : contragredient (1 : G →* GL n R) = 1 := by
  ext g a b
  simp [contragredient_val, Matrix.one_apply, eq_comm]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1] [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **The dual coefficients of the constant representation are its sheaf**: for the trivial
representation `1 : π₁(X, x̄) → GL_r(ℚ_ℓ)`, `ℱ_{1₀^∨} = ℱ_1`. -/
theorem LAdicSheaf.representationDualSheaf_one {r : ℕ}
    (h : Continuous (1 : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])) :
    LAdicSheaf.representationDualSheaf B X x 1 h = LAdicSheaf.representationSheaf B X x 1 h := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  rw [LAdicSheaf.representationSheaf_eq_representationLAdicSheaf]
  unfold LAdicSheaf.representationDualSheaf
  have key : ∀ (σ τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hσ : Continuous σ)
      (hτ : Continuous τ), σ = τ →
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        σ hσ =
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        τ hτ := by
    rintro σ τ hσ hτ rfl
    rfl
  exact key _ _ _ _ (by rw [integralModel_one, contragredient_one])

end Weil

end
