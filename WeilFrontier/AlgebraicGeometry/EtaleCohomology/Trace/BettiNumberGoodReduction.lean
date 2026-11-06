module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.IntegralRank
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.LAdicRank
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.GoodReduction.FibreCohomologyTransfer
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCohomologyIso
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyDegree
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyLevels
public import WeilFrontier.AlgebraicGeometry.Morphisms.GoodReductionInvertPrime
public import Weil.Attr

/-!
# The degree of `P_ν` and the Betti numbers under good reduction

Let `S₀` be smooth and projective over a finite field `κ`, arising by good reduction of a smooth
projective scheme `Y` over `ℂ`, and let `ℓ ≠ char κ` be a prime. Then
`deg P_ν = dim_{ℚ_ℓ} H^ν(S₀ ⊗ κ̄, ℚ_ℓ)`, and `H^ν(S₀ ⊗ κ̄, ℚ_ℓ)` is `ℚ_ℓ ⊗ lim_m` of the étale
cohomology groups `H^ν(S₀ ⊗ κ̄, ℤ/ℓ^{m+1})`. The good reduction is through a smooth projective
family `X ⟶ Spec R` over a domain on which `ℓ` is a unit, with geometric fibres `Y` and
`S₀ ⊗ κ̄`; the dimension of `ℚ_ℓ ⊗ lim_m H^ν(-, ℤ/ℓ^{m+1})` only depends on the inverse system
of the torsion groups, so it can be computed on `Y`, where Artin's comparison theorem and the
finite generation of `H^ν(Y(ℂ), ℤ)` identify it with `rank_ℤ H^ν(Y(ℂ), ℤ)`.

## Main results

* `Nat.Prime.cast_ne_zero_of_ne_ringChar`: a prime `ℓ ≠ char κ` is nonzero in the field `κ`.
* `AlgebraicGeometry.Scheme.finrank_rationalLimit_etaleTorsionSystem_eq_of_addEquiv`: the
  dimension of `ℚ_ℓ ⊗ lim_m H^ν(Z, ℤ/ℓ^{m+1})` only depends on the inverse system of the groups
  `H^ν(Z, ℤ/ℓ^{m+1})`.
* `AlgebraicGeometry.Scheme.finrank_rationalLimit_etaleTorsionSystem_eq_of_iso`: it is invariant
  under isomorphisms of schemes.
* `Weil.finrank_rationalCohomology_eq_finrank_rationalLimit_etaleTorsionSystem`:
  `dim_{ℚ_ℓ} H^ν(X_κ̄, ℚ_ℓ) = dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m H^ν(X ×_κ κ̄, ℤ/ℓ^{m+1})`.
* `Weil.natDegree_rationalFrobeniusCharpolyReverse_eq_finrank_rationalLimit_etaleTorsionSystem`:
  `deg P_ν = dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m H^ν(X ×_κ κ̄, ℤ/ℓ^{m+1})`.
* `AlgebraicGeometry.Scheme.ArisesByGoodReduction.exists_geometricPoint_pullback_iso`: good
  reduction exhibits `Y` and `S₀ ×_κ κ̄` as the geometric fibres of one smooth projective family
  over a domain on which `ℓ` is a unit.

* `Weil.natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber_of_inputs`: `deg P_ν = b_ν(Y)`,
  given Artin's comparison theorem for `Y` and the finite generation of `H^*(Y(ℂ), ℤ)`.
* `Weil.natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber_of_artinComparison`: the same,
  from these two inputs for every smooth projective scheme over `ℂ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry Stacks.EtaleCohomology PadicInt

/-- A prime `ℓ` different from the characteristic of a field is nonzero in it. -/
theorem Nat.Prime.cast_ne_zero_of_ne_ringChar {κ : Type*} [Field κ] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ℓ ≠ ringChar κ) : (ℓ : κ) ≠ 0 := by
  intro h0
  rw [ringChar.spec] at h0
  rcases CharP.char_is_prime_or_zero κ (ringChar κ) with hp | hp
  · exact h ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h0).symm
  · rw [hp, zero_dvd_iff] at h0
    exact hℓ.ne_zero h0

namespace AlgebraicGeometry.Scheme

section Transfer

variable (ℓ : ℕ) [Fact ℓ.Prime] (ν : ℕ)

/-- **The `ℓ`-adic dimension only depends on the torsion groups.** Isomorphisms
`H^ν(Z, ℤ/ℓ^{m+1}) ≃ H^ν(Z', ℤ/ℓ^{m+1})` compatible with the reductions give
`dim ℚ_ℓ ⊗ lim_m H^ν(Z, ℤ/ℓ^{m+1}) = dim ℚ_ℓ ⊗ lim_m H^ν(Z', ℤ/ℓ^{m+1})`. -/
theorem finrank_rationalLimit_etaleTorsionSystem_eq_of_addEquiv {Z Z' : Scheme.{0}}
    (e : ∀ m : ℕ, etaleCohomologyConstant Z (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν ≃+
      etaleCohomologyConstant Z' (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν)
    (he : ∀ (m : ℕ) (x : etaleCohomologyConstant Z (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1 + 1)))) ν),
      e m (etaleCohomologyConstantMap Z (AddCommGrpCat.zmodPowReduction ℓ m) ν x) =
        etaleCohomologyConstantMap Z' (AddCommGrpCat.zmodPowReduction ℓ m) ν (e (m + 1) x)) :
    Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem Z ℓ ν)) =
      Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem Z' ℓ ν)) := by
  refine finrank_rationalLimit_eq_of_addEquiv _ _
    (fun m => ((etaleTorsionSystemObjAddEquiv Z ℓ ν m).trans (e m)).trans
      (etaleTorsionSystemObjAddEquiv Z' ℓ ν m).symm)
    (pow_smul_etaleTorsionSystem Z ℓ ν) (fun m x => ?_)
  apply (etaleTorsionSystemObjAddEquiv Z' ℓ ν m).injective
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [etaleTorsionSystemObjAddEquiv_map, etaleTorsionSystemObjAddEquiv_map,
    AddEquiv.apply_symm_apply, he]

/-- The dimension of `ℚ_ℓ ⊗ lim_m H^ν(Z, ℤ/ℓ^{m+1})` is invariant under isomorphisms of
schemes. -/
theorem finrank_rationalLimit_etaleTorsionSystem_eq_of_iso {Z Z' : Scheme.{0}} (e : Z ≅ Z') :
    Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem Z ℓ ν)) =
      Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem Z' ℓ ν)) :=
  finrank_rationalLimit_etaleTorsionSystem_eq_of_addEquiv ℓ ν
    (fun _ => etaleCohomologyConstantAddEquivOfIso e _ ν)
    (fun _ x => etaleCohomologyConstantAddEquivOfIso_map e _ ν x)

end Transfer

namespace ArisesByGoodReduction

variable {κ : Type} [Field κ] {S₀ : Scheme.{0}} {s₀ : S₀ ⟶ Spec (.of κ)}
  {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- **`Y` and `S₀ ⊗ κ̄` are geometric fibres of one smooth projective family.** If `S₀` over
`κ` arises by good reduction of `Y` over `ℂ` and `ℓ ≠ 0` in `κ`, there are a domain `R` of finite
type over `ℤ` in which `ℓ` is a unit, a smooth projective `f : X ⟶ Spec R` and geometric points
`s₁ s₂` of `Spec R` with `X ×_R s₁ ≅ Y` and `X ×_R s₂ ≅ S₀ ×_κ κ̄`, for any algebraically
closed extension `κ̄` of `κ`. -/
theorem exists_geometricPoint_pullback_iso (h : ArisesByGoodReduction s₀ y) (ℓ : ℕ)
    (hℓ : (ℓ : κ) ≠ 0) (kbar : Type) [Field kbar] [IsAlgClosed kbar] [Algebra κ kbar] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.FiniteType ℤ R),
      IsUnit (ℓ : R) ∧ ∃ (X : Scheme.{0}) (f : X ⟶ Spec (.of R)) (_ : Smooth f)
        (_ : IsProjective f) (s₁ s₂ : GeometricPoint (Spec (.of R))),
        Nonempty (pullback f s₁.hom ≅ Y) ∧
          Nonempty (pullback f s₂.hom ≅
            pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap κ kbar)))) := by
  obtain ⟨R, _, _, _, hu, X, f, hf, hp, φ, ψ, ⟨eY, -⟩, ⟨eS, heS⟩⟩ := h.exists_isUnit ℓ hℓ
  let ι := Spec.map (CommRingCat.ofHom (algebraMap κ kbar))
  let s₁ : GeometricPoint (Spec (.of R)) := ⟨ℂ, Spec.map (CommRingCat.ofHom φ)⟩
  let s₂ : GeometricPoint (Spec (.of R)) := ⟨kbar, ι ≫ Spec.map (CommRingCat.ofHom ψ)⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, hu, X, f, hf, hp, s₁, s₂, ⟨eY⟩, ⟨?_⟩⟩
  refine (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom ψ)) ι).symm ≪≫ ?_
  exact asIso (pullback.map _ _ s₀ ι eS.hom (𝟙 _) (𝟙 _) (by simp [heS]) (by simp))

end ArisesByGoodReduction

end AlgebraicGeometry.Scheme

namespace Weil

open AlgebraicGeometry.Scheme

section RationalCohomology

variable (B : BigEtaleSite.{0}) (X : B.Scheme) {k : Type} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

omit [Fintype k] in
/-- **`H^ν(X_k̄, ℚ_ℓ)` from the étale cohomology of the constant sheaves `ℤ/ℓ^{m+1}`**:
`dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ) = dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m H^ν(X ×_k k̄, ℤ/ℓ^{m+1})`, `k̄` the algebraic
closure of `k`. -/
theorem finrank_rationalCohomology_eq_finrank_rationalLimit_etaleTorsionSystem [Finite k]
    (ν : ℕ) :
    Module.finrank ℚ_[ℓ] (rationalCohomology B X f ℓ ν) =
      Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ℓ ν)) := by
  have hN : IsNoetherian X.1 := by
    have := LocallyOfFiniteType.isLocallyNoetherian f
    have : CompactSpace X.1 :=
      ⟨by simpa using (quasiCompact_iff f).mp inferInstance _ isOpen_univ isCompact_univ⟩
    exact ⟨⟩
  have : QuasiSeparatedSpace X.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace X.1 hN.toIsLocallyNoetherian
  let := isGrothendieckAbelian_sheaf_smallEtale.{0, 0}
    (Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k))
  let := IsGrothendieckAbelian.hasExt.{1}
    (Sheaf (Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k)).smallEtaleTopology
      AddCommGrpCat.{1})
  let Z := Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k)
  let A := LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
    (CompactificationOf.ofProper f) (AlgebraicClosure k) (LAdicSheaf.constantSystem B X ℓ) ν
  let L := geometricConstantLevelCohomologyAddEquiv B X ℓ f (AlgebraicClosure k) ν
  let e : ∀ m : ℕ, A.obj (op m) ≃+ (etaleTorsionSystem Z ℓ ν).obj (op m) := fun m =>
    (L m).trans ((sheafHConstantZModAddEquiv Z (ℓ ^ (m + 1)) ν).trans
      (etaleTorsionSystemObjAddEquiv Z ℓ ν m).symm)
  have hA : ∀ (m : ℕ) (x : A.obj (op m)), ℓ ^ (m + 1) • x = 0 := fun m x =>
    (e m).injective (by rw [map_nsmul, map_zero, pow_smul_etaleTorsionSystem])
  refine finrank_rationalLimit_eq_of_addEquiv A _ e hA (fun m x => ?_)
  change (etaleTorsionSystemObjAddEquiv Z ℓ ν m).symm (sheafHConstantZModAddEquiv Z (ℓ ^ (m + 1)) ν
      (L m (A.map (homOfLE (m.le_add_right 1)).op x))) =
    (etaleTorsionSystem Z ℓ ν).map (homOfLE (m.le_add_right 1)).op
      ((etaleTorsionSystemObjAddEquiv Z ℓ ν (m + 1)).symm
        (sheafHConstantZModAddEquiv Z (ℓ ^ (m + 1 + 1)) ν (L (m + 1) x)))
  have h₁ : L m (A.map (homOfLE (m.le_add_right 1)).op x) = (L (m + 1) x).comp
      (Ext.mk₀ ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).map
        (uliftZModPowReduction ℓ m))) (add_zero ν) :=
    geometricConstantLevelCohomologyAddEquiv_transition B X ℓ f (AlgebraicClosure k) ν m x
  have h₂ : sheafHConstantZModAddEquiv Z (ℓ ^ (m + 1)) ν ((L (m + 1) x).comp
      (Ext.mk₀ ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).map
        (uliftZModPowReduction ℓ m))) (add_zero ν)) =
      etaleCohomologyConstantMap Z (AddCommGrpCat.zmodPowReduction ℓ m) ν
        (sheafHConstantZModAddEquiv Z (ℓ ^ (m + 1 + 1)) ν (L (m + 1) x)) :=
    sheafHConstantZModAddEquiv_uliftZModPowReduction Z ℓ m ν _
  rw [h₁, h₂]
  apply (etaleTorsionSystemObjAddEquiv Z ℓ ν m).injective
  rw [AddEquiv.apply_symm_apply, etaleTorsionSystemObjAddEquiv_map, AddEquiv.apply_symm_apply]

/-- **`deg P_ν` from the étale cohomology of the constant sheaves `ℤ/ℓ^{m+1}`**: for `X` proper
over the finite field `k` and `ℓ ≠ char k`,
`deg P_ν = dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m H^ν(X ×_k k̄, ℤ/ℓ^{m+1})`. -/
theorem natDegree_rationalFrobeniusCharpolyReverse_eq_finrank_rationalLimit_etaleTorsionSystem
    [Fact (ℓ ≠ ringChar k)] (ν : ℕ) :
    (rationalFrobeniusCharpolyReverse B X f ℓ ν).natDegree =
      Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ℓ ν)) := by
  rw [natDegree_rationalFrobeniusCharpolyReverse,
    finrank_rationalCohomology_eq_finrank_rationalLimit_etaleTorsionSystem]

end RationalCohomology

section GoodReduction

set_option linter.unusedVariables false in
/-- **`deg P_ν = b_ν(Y)`, given the comparison inputs** (FK IV.1.7). Let `S₀` be smooth and
projective over the finite field `κ`, arising by good reduction of the smooth projective scheme
`Y` over `ℂ`, and `ℓ ≠ char κ` a prime. If Artin's comparison theorem holds for `Y` and the
integral cohomology of `Y(ℂ)` is finitely generated, then the degree of
`P_ν(t) = det(1 - t F_ν | H^ν(S₀ ⊗ κ̄, ℚ_ℓ))` is the `ν`-th Betti number of `Y`.

The hypotheses on `s₀` are FK's; the proof does not need them, the family given by the good
reduction being smooth and projective. -/
theorem natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber_of_inputs
    (B : BigEtaleSite.{0}) (S₀ : B.Scheme) {κ : Type} [Field κ] [Fintype κ]
    (s₀ : S₀.1 ⟶ Spec (.of κ)) [Smooth s₀] [IsProper s₀] (hs₀ : IsProjective s₀)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [Smooth y] (hy : IsProjective y)
    (h : Scheme.ArisesByGoodReduction s₀ y) (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar κ)]
    (ν : ℕ) (hA : Scheme.ArtinComparisonAt y) (hF : Scheme.IntegralCohomologyFG y) :
    (Weil.rationalFrobeniusCharpolyReverse B S₀ s₀ ℓ ν).natDegree = Scheme.bettiNumber y ν := by
  obtain ⟨R, _, _, _, hu, X, f, _, hp, s₁, s₂, ⟨eY⟩, ⟨eS⟩⟩ :=
    h.exists_geometricPoint_pullback_iso ℓ
      ((Fact.out : ℓ.Prime).cast_ne_zero_of_ne_ringChar Fact.out) (AlgebraicClosure κ)
  have : IsProper f := hp.isProper
  rw [natDegree_rationalFrobeniusCharpolyReverse_eq_finrank_rationalLimit_etaleTorsionSystem,
    ← finrank_rationalLimit_etaleTorsionSystem_eq_of_iso ℓ ν eS,
    finrank_rationalLimit_etaleTorsionSystem_eq_of_addEquiv ℓ ν
      (fun m => fibreEtaleCohomologyZModAddEquiv f ℓ hu s₂ s₁ m ν)
      (fun m x => fibreEtaleCohomologyZModAddEquiv_transition f ℓ hu s₂ s₁ m ν x),
    finrank_rationalLimit_etaleTorsionSystem_eq_of_iso ℓ ν eY,
    finrank_rationalLimit_etaleTorsionSystem y ℓ ν hA hF,
    bettiNumber_eq_finrank_analyticCohomologyConstant_int_of_isProjective y hy]

/-- **`deg P_ν = b_ν(Y)`** (FK IV.1.7), given Artin's comparison theorem and the finite
generation of the integral cohomology for every smooth projective scheme over `ℂ`. -/
theorem natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber_of_artinComparison
    (hA : Scheme.ArtinComparison) (hF : Scheme.IntegralCohomologyFGOfProjective)
    (B : BigEtaleSite.{0}) (S₀ : B.Scheme) {κ : Type} [Field κ] [Fintype κ]
    (s₀ : S₀.1 ⟶ Spec (.of κ)) [Smooth s₀] [IsProper s₀] (hs₀ : IsProjective s₀)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [Smooth y] (hy : IsProjective y)
    (h : Scheme.ArisesByGoodReduction s₀ y) (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar κ)]
    (ν : ℕ) :
    (Weil.rationalFrobeniusCharpolyReverse B S₀ s₀ ℓ ν).natDegree = Scheme.bettiNumber y ν :=
  natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber_of_inputs B S₀ s₀ hs₀ y hy h ℓ ν
    (hA Y y inferInstance hy) (hF Y y inferInstance hy)

end GoodReduction

end Weil
