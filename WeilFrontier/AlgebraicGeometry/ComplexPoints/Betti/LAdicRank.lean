module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilFrontier.Algebra.Module.LAdicRankOfInverseSystem
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Bockstein
public import Weil.Attr

/-!
# The `ℓ`-adic rank of the torsion cohomology of `Y(ℂ)`

Let `(C, J)` be a site, `ℓ` a prime and `ν` a natural number. The groups
`Hᵛ(J, ℤ/ℓ^{m+1})` of cohomology with coefficients in the constant sheaves `ℤ/ℓ^{m+1}`,
with the maps induced by the reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`, form an inverse system of
`ℤ_ℓ`-modules, the `m`-th level being killed by `ℓ^{m+1}`. When `Hᵛ(J, ℤ)` and `Hᵛ⁺¹(J, ℤ)`
are finitely generated, the Bockstein sequences
`0 → Hᵛ(ℤ)/ℓ^{m+1} → Hᵛ(ℤ/ℓ^{m+1}) → Hᵛ⁺¹(ℤ)[ℓ^{m+1}] → 0`
show that `ℚ_ℓ ⊗ lim_m Hᵛ(J, ℤ/ℓ^{m+1})` has dimension `rank_ℤ Hᵛ(J, ℤ)`.

For a scheme `Y` over `ℂ` this applies to the analytic cohomology of `Y(ℂ)`. The étale
cohomology groups `Hᵛ_et(Y, ℤ/ℓ^{m+1})` form a second inverse system, and Artin's comparison
theorem identifies the two rational limits.

## Main definitions

* `CategoryTheory.Sheaf.H.zmodPowSystem J ℓ ν`: the inverse system `m ↦ Hᵛ(J, ℤ/ℓ^{m+1})` of
  `ℤ_ℓ`-modules.
* `AlgebraicGeometry.Scheme.analyticTorsionSystem y ℓ ν`: the inverse system
  `m ↦ Hᵛ(Y(ℂ), ℤ/ℓ^{m+1})`.
* `AlgebraicGeometry.Scheme.etaleTorsionSystem Y ℓ ν`: the inverse system
  `m ↦ Hᵛ_et(Y, ℤ/ℓ^{m+1})`.

## Main results

* `CategoryTheory.Sheaf.H.intReduction_eq_zero_iff`,
  `CategoryTheory.Sheaf.H.intBockstein_eq_zero_iff`, `CategoryTheory.Sheaf.H.nsmul_intBockstein`:
  the Bockstein sequence `Hᵛ(ℤ) --n--> Hᵛ(ℤ) → Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ) --n--> Hᵛ⁺¹(ℤ)` for the
  constant sheaves `ℤ` and `ℤ/n`, and its compatibility with the reductions
  (`CategoryTheory.Sheaf.H.map_zmodPowReduction_intReduction`,
  `CategoryTheory.Sheaf.H.intBockstein_map_zmodReductionHom`).
* `CategoryTheory.Sheaf.H.finrank_rationalLimit_zmodPowSystem`: on any site,
  `dim ℚ_ℓ ⊗ lim_m Hᵛ(ℤ/ℓ^{m+1}) = rank Hᵛ(ℤ)` when `Hᵛ(ℤ)` and `Hᵛ⁺¹(ℤ)` are finitely
  generated.
* `AlgebraicGeometry.Scheme.finrank_rationalLimit_analyticTorsionSystem`: the same for `Y(ℂ)`.
* `AlgebraicGeometry.Scheme.rationalLimitEtaleTorsionSystemEquiv`: under Artin's comparison
  theorem, `ℚ_ℓ ⊗ lim_m Hᵛ_et(Y, ℤ/ℓ^{m+1}) ≃ ℚ_ℓ ⊗ lim_m Hᵛ(Y(ℂ), ℤ/ℓ^{m+1})`.
* `AlgebraicGeometry.Scheme.finrank_rationalLimit_etaleTorsionSystem`: hence, given also the
  finite generation of the integral cohomology of `Y(ℂ)`,
  `dim ℚ_ℓ ⊗ lim_m Hᵛ_et(Y, ℤ/ℓ^{m+1}) = rank Hᵛ(Y(ℂ), ℤ)`.

## Implementation notes

The coefficients are the constant sheaves on the abelian groups `ℤ` and `ZMod n` themselves,
as in `AlgebraicGeometry.Scheme.analyticCohomologyConstant`, while the Bockstein sequences
of `CategoryTheory.Sheaf.H` are stated for `ULift ℤ` and `ULift (ZMod n)`; the two are
identified through the isomorphisms `ULift M ≅ M`. The étale system lives in universe `1` and
the analytic one in universe `0`, so the comparison of their rational limits is a
`ℚ_ℓ`-linear equivalence rather than an isomorphism in one category of modules.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl], IV.1.7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe w' v u

namespace AddCommGrpCat

/-- The reduction `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
noncomputable def zmodPowReduction (ℓ m : ℕ) :
    of (ZMod (ℓ ^ (m + 1 + 1))) ⟶ of (ZMod (ℓ ^ (m + 1))) :=
  ofHom (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ _)) _).toAddMonoidHom

/-- The reduction `ℤ → ℤ/n`. -/
noncomputable def intCastHom (n : ℕ) : of ℤ ⟶ of (ZMod n) :=
  ofHom (Int.castAddHom (ZMod n))

lemma intCastHom_comp_zmodPowReduction (ℓ m : ℕ) :
    intCastHom (ℓ ^ (m + 1 + 1)) ≫ zmodPowReduction ℓ m = intCastHom (ℓ ^ (m + 1)) := by
  ext
  simp only [intCastHom, zmodPowReduction, hom_comp, hom_ofHom, AddMonoidHom.coe_comp,
    Function.comp_apply, Int.coe_castAddHom, Int.cast_one, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, map_one]

/-- The reduction `ℤ/nd → ℤ/n`. -/
noncomputable def zmodReductionHom (n d : ℕ) : of (ZMod (n * d)) ⟶ of (ZMod n) :=
  ofHom (ZMod.castHom (dvd_mul_right n d) _).toAddMonoidHom

lemma zmodPowReduction_eq (ℓ m : ℕ) : zmodPowReduction ℓ m = zmodReductionHom (ℓ ^ (m + 1)) ℓ :=
  rfl

lemma nsmul_id_zmod (n : ℕ) : n • 𝟙 (of (ZMod n)) = 0 := by
  ext x
  simp

end AddCommGrpCat

namespace CategoryTheory.Sheaf.H

/-- If `n` kills a sheaf, it kills its cohomology. -/
lemma nsmul_eq_zero_of_nsmul_id_eq_zero.{w} {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] {F : Sheaf J AddCommGrpCat.{w}} (n ν : ℕ)
    (hF : n • 𝟙 F = 0) (x : H.{w'} F ν) : n • x = 0 := by
  rw [← map_nsmul_id_apply, hF, H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{0}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{0})]

/-- Isomorphic sheaves have isomorphic cohomology. -/
noncomputable def mapIsoAddEquiv {F G : Sheaf J AddCommGrpCat.{0}} (e : F ≅ G) (ν : ℕ) :
    H.{w'} F ν ≃+ H.{w'} G ν where
  toFun := H.map e.hom ν
  invFun := H.map e.inv ν
  left_inv x := by rw [← H.map_comp_apply, e.hom_inv_id, H.map_id_apply]
  right_inv x := by rw [← H.map_comp_apply, e.inv_hom_id, H.map_id_apply]
  map_add' := map_add _

@[simp]
lemma mapIsoAddEquiv_apply {F G : Sheaf J AddCommGrpCat.{0}} (e : F ≅ G) (ν : ℕ)
    (x : H.{w'} F ν) :
    mapIsoAddEquiv J e ν x = H.map e.hom ν x := rfl

@[simp]
lemma mapIsoAddEquiv_symm_apply {F G : Sheaf J AddCommGrpCat.{0}} (e : F ≅ G) (ν : ℕ)
    (x : H.{w'} G ν) : (mapIsoAddEquiv J e ν).symm x = H.map e.inv ν x := rfl

variable {J} in
/-- Commutative squares of sheaves induce commutative squares in cohomology. -/
lemma map_map_of_comm {F F' G G' : Sheaf J AddCommGrpCat.{0}} (a : F ⟶ F') (b : G ⟶ G')
    (f : F ⟶ G) (f' : F' ⟶ G') (h : f ≫ b = a ≫ f') (ν : ℕ) (x : H.{w'} F ν) :
    H.map b ν (H.map f ν x) = H.map f' ν (H.map a ν x) := by
  rw [← H.map_comp_apply, ← H.map_comp_apply, h]

/-- The constant sheaf `ℤ/n` kills its cohomology: `n • x = 0` for `x ∈ Hᵛ(ℤ/n)`. -/
lemma nsmul_eq_zero_zmod (n ν : ℕ)
    (x : H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod n))) ν) :
    n • x = 0 :=
  nsmul_eq_zero_of_nsmul_id_eq_zero n ν (by
    rw [← Functor.map_id, ← Functor.map_nsmul, AddCommGrpCat.nsmul_id_zmod, Functor.map_zero]) x

/-- The inverse system of abelian groups `m ↦ Hᵛ(J, ℤ/ℓ^{m+1})`, the transition maps being
induced by the reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
noncomputable def zmodPowGroupSystem (ℓ ν : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  Functor.ofOpSequence
    (X := fun m => AddCommGrpCat.of
      (H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))))
        ν))
    (fun m => AddCommGrpCat.ofHom
      (H.map ((constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.zmodPowReduction ℓ m)) ν))

lemma zmodPowGroupSystem_obj (ℓ ν m : ℕ) :
    ((zmodPowGroupSystem.{w'} J ℓ ν).obj (op m) : Type w') =
      H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1))))) ν :=
  rfl

lemma zmodPowGroupSystem_map_succ_apply (ℓ ν m : ℕ)
    (x : (zmodPowGroupSystem.{w'} J ℓ ν).obj (op (m + 1))) :
    (zmodPowGroupSystem.{w'} J ℓ ν).map (homOfLE (m.le_add_right 1)).op x =
      H.map ((constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.zmodPowReduction ℓ m)) ν
        x := by
  simp only [zmodPowGroupSystem, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

lemma pow_smul_zmodPowGroupSystem (ℓ ν m : ℕ) (x : (zmodPowGroupSystem.{w'} J ℓ ν).obj (op m)) :
    ℓ ^ (m + 1) • x = 0 :=
  nsmul_eq_zero_zmod J _ ν x

/-- The isomorphism `ULift M ≅ M` of constant sheaves. -/
noncomputable abbrev uliftConstIso (M : Type) [AddCommGroup M] :
    (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} M)) ≅
      (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of M) :=
  (constantSheaf J AddCommGrpCat.{0}).mapIso AddEquiv.ulift.toAddCommGrpIso

/-! ### The Bockstein sequence for the coefficients `ℤ` and `ℤ/n` -/

section Bockstein

variable (n ν : ℕ)

set_option hygiene false in
/-- The constant sheaf `ℤ`, without `ULift`. -/
local notation "ℤ'[" J "]" => (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)

set_option hygiene false in
/-- The constant sheaf `ℤ/n`, without `ULift`. -/
local notation "ℤ'/[" J ", " n "]" =>
  (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod n))

/-- The reduction `Hᵛ(ℤ) → Hᵛ(ℤ/n)`, induced by `ℤ → ℤ/n`. -/
noncomputable def intReduction : H.{w'} ℤ'[J] ν →+ H.{w'} ℤ'/[J, n] ν :=
  H.map ((constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.intCastHom n)) ν

/-- The Bockstein map `Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)` of `0 → ℤ → ℤ → ℤ/n → 0`. -/
noncomputable def intBockstein [NeZero n] : H.{w'} ℤ'/[J, n] ν →+ H.{w'} ℤ'[J] (ν + 1) :=
  ((mapIsoAddEquiv.{w'} J (uliftConstIso J ℤ) (ν + 1)).toAddMonoidHom.comp
    (bockstein n ν)).comp (mapIsoAddEquiv.{w'} J (uliftConstIso J (ZMod n)) ν).symm.toAddMonoidHom

lemma intReduction_eq (x : H.{w'} ℤ'[J] ν) :
    intReduction J n ν x = mapIsoAddEquiv.{w'} J (uliftConstIso J (ZMod n)) ν
      (reduction n ν ((mapIsoAddEquiv.{w'} J (uliftConstIso J ℤ) ν).symm x)) := by
  have hsq : (zmodShortComplex J n).g ≫ (uliftConstIso J (ZMod n)).hom =
      (uliftConstIso J ℤ).hom ≫
        (constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.intCastHom n) := by
    change (constantSheaf J AddCommGrpCat.{0}).map _ ≫ (constantSheaf J AddCommGrpCat.{0}).map _ =
      (constantSheaf J AddCommGrpCat.{0}).map _ ≫ (constantSheaf J AddCommGrpCat.{0}).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  simp only [mapIsoAddEquiv_apply, mapIsoAddEquiv_symm_apply, reduction, intReduction]
  rw [map_map_of_comm _ _ _ _ hsq,
    ← H.map_comp_apply (uliftConstIso J ℤ).inv (uliftConstIso J ℤ).hom, Iso.inv_hom_id,
    H.map_id_apply]

/-- Exactness of `Hᵛ(ℤ) --n--> Hᵛ(ℤ) → Hᵛ(ℤ/n)`. -/
theorem intReduction_eq_zero_iff [NeZero n] (x : H.{w'} ℤ'[J] ν) :
    intReduction J n ν x = 0 ↔ ∃ y, x = n • y := by
  rw [intReduction_eq, AddEquiv.map_eq_zero_iff, (exact_nsmul_reduction n ν _)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨mapIsoAddEquiv.{w'} J (uliftConstIso J ℤ) ν y, ?_⟩
    rw [← map_nsmul]
    exact ((AddEquiv.symm_apply_eq _).1 hy.symm)
  · rintro ⟨y, rfl⟩
    exact ⟨(mapIsoAddEquiv.{w'} J (uliftConstIso J ℤ) ν).symm y, by simp only [map_nsmul]⟩

/-- Exactness of `Hᵛ(ℤ) → Hᵛ(ℤ/n) → Hᵛ⁺¹(ℤ)`. -/
theorem intBockstein_eq_zero_iff [NeZero n] (x : H.{w'} ℤ'/[J, n] ν) :
    intBockstein J n ν x = 0 ↔ ∃ h, intReduction J n ν h = x := by
  simp only [intBockstein, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff]
  rw [exact_reduction_bockstein n ν _]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨mapIsoAddEquiv.{w'} J (uliftConstIso J ℤ) ν z, ?_⟩
    rw [intReduction_eq, AddEquiv.symm_apply_apply, hz, AddEquiv.apply_symm_apply]
  · rintro ⟨h, rfl⟩
    exact ⟨(mapIsoAddEquiv.{w'} J (uliftConstIso J ℤ) ν).symm h, by
      rw [intReduction_eq, AddEquiv.symm_apply_apply]⟩

/-- The image of the Bockstein map is killed by `n`. -/
theorem nsmul_intBockstein [NeZero n] (x : H.{w'} ℤ'/[J, n] ν) :
    n • intBockstein J n ν x = 0 := by
  simp only [intBockstein, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [← map_nsmul, nsmul_bockstein, map_zero]

/-- The reductions `Hᵛ(ℤ) → Hᵛ(ℤ/n)` commute with the reduction `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
theorem map_zmodPowReduction_intReduction (ℓ m : ℕ) (x : H.{w'} ℤ'[J] ν) :
    H.map ((constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.zmodPowReduction ℓ m)) ν
      (intReduction J (ℓ ^ (m + 1 + 1)) ν x) = intReduction J (ℓ ^ (m + 1)) ν x := by
  rw [intReduction, intReduction, ← H.map_comp_apply, ← Functor.map_comp,
    AddCommGrpCat.intCastHom_comp_zmodPowReduction]

/-- The Bockstein maps commute with the reduction `ℤ/nd → ℤ/n` up to multiplication by `d`. -/
theorem intBockstein_map_zmodReductionHom (d : ℕ) [NeZero n] [NeZero d]
    (x : H.{w'} ℤ'/[J, n * d] ν) :
    intBockstein J n ν
        (H.map ((constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.zmodReductionHom n d)) ν x) =
      d • intBockstein J (n * d) ν x := by
  simp only [intBockstein, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [← map_nsmul, ← bockstein_zmodReduction]
  congr 2
  simp only [mapIsoAddEquiv_symm_apply, zmodReduction]
  refine (map_map_of_comm _ _ _ _ ?_ ν x).symm
  change (constantSheaf J AddCommGrpCat.{0}).map _ ≫ (constantSheaf J AddCommGrpCat.{0}).map _ =
    (constantSheaf J AddCommGrpCat.{0}).map _ ≫ (constantSheaf J AddCommGrpCat.{0}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end Bockstein

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inverse system of `ℤ_ℓ`-modules `m ↦ Hᵛ(J, ℤ/ℓ^{m+1})`, the transition maps being
induced by the reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
noncomputable def zmodPowSystem (ν : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{w'} ℤ_[ℓ] :=
  PadicInt.inverseSystemOfTorsion (zmodPowGroupSystem.{w'} J ℓ ν)
    (pow_smul_zmodPowGroupSystem J ℓ ν)

lemma pow_smul_zmodPowSystem (ν m : ℕ) (x : (zmodPowSystem.{w'} J ℓ ν).obj (op m)) :
    ℓ ^ (m + 1) • x = 0 :=
  nsmul_eq_zero_zmod J _ ν x

/-- The `m`-th level of `CategoryTheory.Sheaf.H.zmodPowSystem J ℓ ν` is `Hᵛ(J, ℤ/ℓ^{m+1})`. -/
noncomputable def zmodPowSystemObjAddEquiv (ν m : ℕ) :
    (zmodPowSystem.{w'} J ℓ ν).obj (op m) ≃+
      H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1))))) ν :=
  { Equiv.refl _ with map_add' := fun _ _ => rfl }

lemma zmodPowSystemObjAddEquiv_map (ν m : ℕ) (x : (zmodPowSystem.{w'} J ℓ ν).obj (op (m + 1))) :
    zmodPowSystemObjAddEquiv J ℓ ν m
        ((zmodPowSystem.{w'} J ℓ ν).map (homOfLE (m.le_add_right 1)).op x) =
      H.map ((constantSheaf J AddCommGrpCat.{0}).map (AddCommGrpCat.zmodPowReduction ℓ m)) ν
        (zmodPowSystemObjAddEquiv J ℓ ν (m + 1) x) := by
  exact (PadicInt.inverseSystemOfTorsion_map_succ_apply _ _ m x).trans
    (zmodPowGroupSystem_map_succ_apply J ℓ ν m x)


/-! ### The rank of the inverse limit -/

/-- **The `ℓ`-adic rank of the torsion cohomology.** If `Hᵛ(J, ℤ)` and `Hᵛ⁺¹(J, ℤ)` are
finitely generated, then `dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m Hᵛ(J, ℤ/ℓ^{m+1}) = rank_ℤ Hᵛ(J, ℤ)`. -/
theorem finrank_rationalLimit_zmodPowSystem (ν : ℕ)
    [Module.Finite ℤ (H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) ν)]
    [Module.Finite ℤ
      (H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) (ν + 1))] :
    Module.finrank ℚ_[ℓ] (PadicInt.rationalLimit (zmodPowSystem.{w'} J ℓ ν)) =
      Module.finrank ℤ
        (H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) ν) := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have (m : ℕ) : NeZero (ℓ ^ (m + 1)) := ⟨pow_ne_zero _ hℓ⟩
  have : NeZero ℓ := ⟨hℓ⟩
  let e := zmodPowSystemObjAddEquiv.{w'} J ℓ ν
  refine PadicInt.finrank_rationalLimit_eq_finrank_of_bockstein
    (H' := H.{w'} ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) (ν + 1)) _
    (fun m => (e m).symm.toAddMonoidHom.comp (intReduction J (ℓ ^ (m + 1)) ν))
    (fun m => (intBockstein J (ℓ ^ (m + 1)) ν).comp (e m).toAddMonoidHom) ?_ ?_ ?_ ?_ ?_
  · intro m h
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.map_eq_zero_iff]
    exact intReduction_eq_zero_iff J _ ν h
  · intro m x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [intBockstein_eq_zero_iff]
    exact exists_congr fun h => (AddEquiv.symm_apply_eq _).symm
  · intro m x
    exact nsmul_intBockstein J _ ν _
  · intro m h
    apply (e m).injective
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [zmodPowSystemObjAddEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      map_zmodPowReduction_intReduction]
  · intro m x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [zmodPowSystemObjAddEquiv_map, AddCommGrpCat.zmodPowReduction_eq]
    exact intBockstein_map_zmodReductionHom J (ℓ ^ (m + 1)) ν ℓ (e (m + 1) x)

end CategoryTheory.Sheaf.H

namespace PadicInt

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The rational limit does not change when the levels are lifted to a higher universe. -/
noncomputable def rationalLimitUliftLinearEquiv (A : ℕᵒᵖ ⥤ ModuleCat.{0} ℤ_[ℓ]) :
    rationalLimit (A ⋙ ModuleCat.uliftFunctor.{w'} ℤ_[ℓ]) ≃ₗ[ℚ_[ℓ]] rationalLimit A :=
  LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _
    ((preservesLimitIso (ModuleCat.uliftFunctor.{w'} ℤ_[ℓ]) A).symm.toLinearEquiv.trans
      ULift.moduleEquiv)

end PadicInt

namespace AlgebraicGeometry.Scheme

open TopologicalSpace PadicInt

section Analytic

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) (ℓ : ℕ) [Fact ℓ.Prime] (ν : ℕ)

/-- The inverse system of `ℤ_ℓ`-modules `m ↦ Hᵛ(Y(ℂ), ℤ/ℓ^{m+1})`, the transition maps being
induced by the reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
noncomputable def analyticTorsionSystem : ℕᵒᵖ ⥤ ModuleCat.{0} ℤ_[ℓ] :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  Sheaf.H.zmodPowSystem.{0} (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) ℓ ν

lemma analyticTorsionSystem_obj (m : ℕ) :
    ((analyticTorsionSystem y ℓ ν).obj (op m) : Type) =
      analyticCohomologyConstant y (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν :=
  rfl

/-- **The `ℓ`-adic rank of the torsion cohomology of `Y(ℂ)`.** If the integral cohomology of
`Y(ℂ)` is finitely generated, then
`dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m Hᵛ(Y(ℂ), ℤ/ℓ^{m+1}) = rank_ℤ Hᵛ(Y(ℂ), ℤ)`. -/
theorem finrank_rationalLimit_analyticTorsionSystem (hY : IntegralCohomologyFG y) :
    Module.finrank ℚ_[ℓ] (rationalLimit (analyticTorsionSystem y ℓ ν)) =
      Module.finrank ℤ (analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν) := by
  let := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  have h₀ : Module.Finite ℤ (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) ν) :=
    Module.Finite.iff_addGroup_fg.2 (hY ν)
  have h₁ : Module.Finite ℤ (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) (ν + 1)) :=
    Module.Finite.iff_addGroup_fg.2 (hY (ν + 1))
  exact Sheaf.H.finrank_rationalLimit_zmodPowSystem.{0} _ ℓ ν

/-- The `m`-th level of `AlgebraicGeometry.Scheme.analyticTorsionSystem y ℓ ν` is
`Hᵛ(Y(ℂ), ℤ/ℓ^{m+1})`. -/
noncomputable def analyticTorsionSystemObjAddEquiv (m : ℕ) :
    (analyticTorsionSystem y ℓ ν).obj (op m) ≃+
      analyticCohomologyConstant y (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν :=
  { Equiv.refl _ with map_add' := fun _ _ => rfl }

lemma analyticTorsionSystemObjAddEquiv_map (m : ℕ)
    (x : (analyticTorsionSystem y ℓ ν).obj (op (m + 1))) :
    analyticTorsionSystemObjAddEquiv y ℓ ν m
        ((analyticTorsionSystem y ℓ ν).map (homOfLE (m.le_add_right 1)).op x) =
      analyticCohomologyConstantMap y (AddCommGrpCat.zmodPowReduction ℓ m) ν
        (analyticTorsionSystemObjAddEquiv y ℓ ν (m + 1) x) :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  Sheaf.H.zmodPowSystemObjAddEquiv_map.{0} _ ℓ ν m x

end Analytic

section Etale

variable (Y : Scheme.{0})

/-- `n` kills the étale cohomology with coefficients in `ℤ/n`. -/
lemma nsmul_etaleCohomologyConstant_zmod (n ν : ℕ)
    (x : etaleCohomologyConstant Y (AddCommGrpCat.of (ZMod n)) ν) : n • x = 0 := by
  let := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Y
  let := IsGrothendieckAbelian.hasExt.{1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{1})
  have h0 : n • 𝟙 (AddCommGrpCat.uliftFunctor.{1, 0}.obj (AddCommGrpCat.of (ZMod n))) = 0 := by
    ext ⟨x⟩
    apply ULift.ext
    change n • x = 0
    simp [nsmul_eq_mul]
  exact Sheaf.H.nsmul_eq_zero_of_nsmul_id_eq_zero
    (F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.uliftFunctor.{1, 0}.obj (AddCommGrpCat.of (ZMod n)))) n ν
    (by rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h0, Functor.map_zero]) x

/-- The inverse system of abelian groups `m ↦ Hᵛ_et(Y, ℤ/ℓ^{m+1})`. -/
noncomputable def etaleTorsionGroupSystem (ℓ ν : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{1} :=
  Functor.ofOpSequence
    (X := fun m => AddCommGrpCat.of
      (etaleCohomologyConstant Y (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν))
    (fun m => AddCommGrpCat.ofHom
      (etaleCohomologyConstantMap Y (AddCommGrpCat.zmodPowReduction ℓ m) ν))

variable (ℓ : ℕ) [Fact ℓ.Prime] (ν : ℕ)

/-- The inverse system of `ℤ_ℓ`-modules `m ↦ Hᵛ_et(Y, ℤ/ℓ^{m+1})`, the transition maps being
induced by the reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
noncomputable def etaleTorsionSystem :
    ℕᵒᵖ ⥤ ModuleCat.{1} ℤ_[ℓ] :=
  inverseSystemOfTorsion (etaleTorsionGroupSystem Y ℓ ν)
    (fun _ x => nsmul_etaleCohomologyConstant_zmod Y _ ν x)

/-- The `m`-th level of `AlgebraicGeometry.Scheme.etaleTorsionSystem Y ℓ ν` is
`Hᵛ_et(Y, ℤ/ℓ^{m+1})`. -/
noncomputable def etaleTorsionSystemObjAddEquiv (m : ℕ) :
    (etaleTorsionSystem Y ℓ ν).obj (op m) ≃+
      etaleCohomologyConstant Y (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν :=
  { Equiv.refl _ with map_add' := fun _ _ => rfl }

lemma etaleTorsionSystemObjAddEquiv_map (m : ℕ)
    (x : (etaleTorsionSystem Y ℓ ν).obj (op (m + 1))) :
    etaleTorsionSystemObjAddEquiv Y ℓ ν m
        ((etaleTorsionSystem Y ℓ ν).map (homOfLE (m.le_add_right 1)).op x) =
      etaleCohomologyConstantMap Y (AddCommGrpCat.zmodPowReduction ℓ m) ν
        (etaleTorsionSystemObjAddEquiv Y ℓ ν (m + 1) x) := by
  refine (inverseSystemOfTorsion_map_succ_apply _ _ m x).trans ?_
  simp only [etaleTorsionGroupSystem, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

lemma pow_smul_etaleTorsionSystem (m : ℕ)
    (x : (etaleTorsionSystem Y ℓ ν).obj (op m)) : ℓ ^ (m + 1) • x = 0 :=
  nsmul_etaleCohomologyConstant_zmod Y _ ν x

end Etale

section Comparison

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) (ℓ : ℕ) [Fact ℓ.Prime] (ν : ℕ)

/-- **Artin's comparison for the `ℓ`-adic cohomology.** Under Artin's comparison theorem,
`ℚ_ℓ ⊗ lim_m Hᵛ_et(Y, ℤ/ℓ^{m+1})` and `ℚ_ℓ ⊗ lim_m Hᵛ(Y(ℂ), ℤ/ℓ^{m+1})` are isomorphic. -/
noncomputable def rationalLimitEtaleTorsionSystemEquiv (hA : ArtinComparisonAt y) :
    rationalLimit (etaleTorsionSystem Y ℓ ν) ≃ₗ[ℚ_[ℓ]]
      rationalLimit (analyticTorsionSystem y ℓ ν) :=
  have hℓ : ∀ m : ℕ, NeZero (ℓ ^ (m + 1)) := fun m => ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let e (m : ℕ) : (etaleTorsionSystem Y ℓ ν).obj (op m) ≃+
      (analyticTorsionSystem y ℓ ν ⋙ ModuleCat.uliftFunctor.{1} ℤ_[ℓ]).obj (op m) :=
    ((etaleTorsionSystemObjAddEquiv Y ℓ ν m).trans
      (((hA ν).choose (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) inferInstance).trans
        (analyticTorsionSystemObjAddEquiv y ℓ ν m).symm)).trans
      (AddEquiv.ulift.symm : _ ≃+ ULift.{1} ((analyticTorsionSystem y ℓ ν).obj (op m)))
  (rationalLimitIsoOfAddEquiv _ _ e (pow_smul_etaleTorsionSystem Y ℓ ν) (fun m x => by
    apply ULift.ext
    change (analyticTorsionSystemObjAddEquiv y ℓ ν m).symm
        ((hA ν).choose _ _ (etaleTorsionSystemObjAddEquiv Y ℓ ν m
          ((etaleTorsionSystem Y ℓ ν).map (homOfLE (m.le_add_right 1)).op x))) =
      (analyticTorsionSystem y ℓ ν).map (homOfLE (m.le_add_right 1)).op
        ((analyticTorsionSystemObjAddEquiv y ℓ ν (m + 1)).symm
          ((hA ν).choose _ _ (etaleTorsionSystemObjAddEquiv Y ℓ ν (m + 1) x)))
    apply (analyticTorsionSystemObjAddEquiv y ℓ ν m).injective
    rw [AddEquiv.apply_symm_apply, analyticTorsionSystemObjAddEquiv_map,
      AddEquiv.apply_symm_apply, etaleTorsionSystemObjAddEquiv_map]
    exact (hA ν).choose_spec _ _ _ _ _ _)).toLinearEquiv.trans
    (rationalLimitUliftLinearEquiv _)

/-- Under Artin's comparison theorem, the `ℓ`-adic étale and analytic cohomology of `Y` have the
same dimension. -/
theorem finrank_rationalLimit_etaleTorsionSystem_eq (hA : ArtinComparisonAt y) :
    Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem Y ℓ ν)) =
      Module.finrank ℚ_[ℓ] (rationalLimit (analyticTorsionSystem y ℓ ν)) :=
  (rationalLimitEtaleTorsionSystemEquiv y ℓ ν hA).finrank_eq

/-- **The `ℓ`-adic Betti number.** Under Artin's comparison theorem and the finite generation
of the integral cohomology of `Y(ℂ)`,
`dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim_m Hᵛ_et(Y, ℤ/ℓ^{m+1}) = rank_ℤ Hᵛ(Y(ℂ), ℤ)`. -/
theorem finrank_rationalLimit_etaleTorsionSystem (hA : ArtinComparisonAt y)
    (hY : IntegralCohomologyFG y) :
    Module.finrank ℚ_[ℓ] (rationalLimit (etaleTorsionSystem Y ℓ ν)) =
      Module.finrank ℤ (analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν) := by
  rw [finrank_rationalLimit_etaleTorsionSystem_eq y ℓ ν hA,
    finrank_rationalLimit_analyticTorsionSystem y ℓ ν hY]

end Comparison

end AlgebraicGeometry.Scheme
