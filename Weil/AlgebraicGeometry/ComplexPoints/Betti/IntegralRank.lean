module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Weil.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import Weil.AlgebraicGeometry.ComplexPoints.Compact
public import Weil.CategoryTheory.Sites.Cohomology.ModuleExtForget
public import Weil.Topology.Sheaves.Cohomology.CompactHausdorffColimits
public import Weil.Attr

/-!
# Betti numbers as ranks of integral cohomology

Let `X` be a compact Hausdorff space. The complex cohomology `H^ν(X, ℂ)`, computed as
`Ext^ν(ℂ_X, ℂ_X)` among sheaves of `ℂ`-vector spaces on `X`, has dimension
`dim_ℂ H^ν(X, ℂ) = rank_ℤ H^ν(X, ℤ)`, the rank of the cohomology of the constant abelian sheaf
`ℤ`. The proof is the chain
`Ext^ν(ℂ_X, ℂ_X) ≃ₗ[ℂ] H^ν(X, ℂ) ≃ₗ[ℂ] ℂ ⊗_ℤ H^ν(X, ℤ)`: the first identification computes
`Ext` out of the constant sheaf `ℂ` as the cohomology of the underlying abelian sheaf, which is
the constant abelian sheaf `ℂ`; the second is the universal coefficient isomorphism for the
torsion-free group `ℂ` on a compact Hausdorff space, which is natural in the coefficients and
so `ℂ`-linear. Finally `dim_ℂ (ℂ ⊗_ℤ N) = rank_ℤ N` for every abelian group `N`.

Applied to `X = Y(ℂ)` for `Y` projective over `ℂ`, this gives
`b_ν(Y) = rank_ℤ H^ν(Y(ℂ), ℤ)`.

## Main results

* `CompactHausdorffCohomology.extConstantSheafComplexLinearEquiv`:
  `Ext^ν(ℂ_X, ℂ_X) ≃ₗ[ℂ] ℂ ⊗_ℤ H^ν(X, ℤ)` for `X` compact Hausdorff.
* `CompactHausdorffCohomology.finrank_ext_constantSheaf_complex_eq_finrank_H_int`:
  `dim_ℂ Ext^ν(ℂ_X, ℂ_X) = rank_ℤ H^ν(X, ℤ)` for `X` compact Hausdorff.
* `AlgebraicGeometry.Scheme.bettiNumber_eq_finrank_analyticCohomologyConstant_int`:
  `b_ν(Y) = rank_ℤ H^ν(Y(ℂ), ℤ)` when `Y(ℂ)` is compact Hausdorff, in particular
  (`bettiNumber_eq_finrank_analyticCohomologyConstant_int_of_isProjective`) for `Y` projective
  over `ℂ`.

## Implementation notes

The rank `rank_ℤ` is `Module.finrank ℤ`, which is `0` for a group of infinite rank, and so is
`dim_ℂ`; the identity `dim_ℂ (ℂ ⊗_ℤ N) = rank_ℤ N` holds for every abelian group `N`, so no
finiteness hypothesis on `H^ν(X, ℤ)` is needed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, 1.7.
* [Bredon] G. E. Bredon, *Sheaf Theory*, II.15.
-/

@[expose] public section

universe w w'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct Module

namespace Module

/-- The rank of an abelian group `N` is the dimension of `ℚ ⊗_ℤ N` over `ℚ`. -/
theorem finrank_rat_tensorProduct_int (N : Type*) [AddCommGroup N] :
    finrank ℚ (ℚ ⊗[ℤ] N) = finrank ℤ N := by
  have : IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ N 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).mpr
      (TensorProduct.isBaseChange ℤ N ℚ)
  rw [IsFractionRing.finrank_right_eq ℤ ℚ]
  convert IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ N 1) le_rfl
  exact Subsingleton.elim _ _

/-- For a field `K` of characteristic zero, the rank of an abelian group `N` is the dimension of
`K ⊗_ℤ N` over `K`. -/
theorem finrank_tensorProduct_int (K : Type*) [Field K] [CharZero K] (N : Type*)
    [AddCommGroup N] : finrank K (K ⊗[ℤ] N) = finrank ℤ N := by
  rw [← LinearEquiv.finrank_eq (AlgebraTensorModule.cancelBaseChange ℤ ℚ K K N),
    Module.finrank_baseChange, finrank_rat_tensorProduct_int]

end Module

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {T : C}
  {R : Type*} [CommRing R]

/-- The constant sheaf functor of sheaves of `R`-modules sends `c • 𝟙 M` to `c • 𝟙`. -/
lemma constantSheaf_map_smul_id [HasWeakSheafify J (ModuleCat R)] (hT : IsTerminal T)
    (M : ModuleCat R) (c : R) :
    (constantSheaf J (ModuleCat R)).map (c • 𝟙 M) = c • 𝟙 _ := by
  apply ((constantSheafAdj J (ModuleCat R) hT).homEquiv _ _).injective
  have h : ((sheafSections J (ModuleCat R)).obj (op T)).map
      (c • 𝟙 ((constantSheaf J (ModuleCat R)).obj M)) = c • 𝟙 _ := rfl
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality, h,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  simp

/-- An isomorphism of abelian sheaves induces an isomorphism on cohomology. -/
noncomputable def Sheaf.H.addEquivOfIso [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ) :
    Sheaf.H.{w'} F n ≃+ Sheaf.H.{w'} G n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv x := by rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv x := by rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' := map_add _

end CategoryTheory

namespace CompactHausdorffCohomology

section

variable {X : TopCat.{0}}

/-- The abelian sheaf underlying the constant sheaf `ℂ` of `ℂ`-vector spaces is the constant
abelian sheaf `ℂ`. -/
noncomputable def sheafForget₂ConstantComplexIso :
    (sheafForget₂ (Opens.grothendieckTopology X) ℂ).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
          (ModuleCat.of ℂ ℂ)) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℂ) :=
  have : (Opens.grothendieckTopology X).PreservesSheafification
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂IntAdj ℂ)
  (constantCommuteCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).app (ModuleCat.of ℂ ℂ)

/-- Multiplication by `c` on the abelian group `ℂ`. -/
noncomputable abbrev complexMulHom (c : ℂ) : AddCommGrpCat.of ℂ ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c)

lemma sheafForget₂ConstantComplexIso_hom_naturality (c : ℂ) :
    (sheafForget₂ (Opens.grothendieckTopology X) ℂ).map (c • 𝟙 _) ≫
        (sheafForget₂ConstantComplexIso (X := X)).hom =
      (sheafForget₂ConstantComplexIso (X := X)).hom ≫
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
          (complexMulHom c) := by
  have : (Opens.grothendieckTopology X).PreservesSheafification
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂IntAdj ℂ)
  have h := (constantCommuteCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).hom.naturality (c • 𝟙 (ModuleCat.of ℂ ℂ))
  rw [Functor.comp_map, Functor.comp_map,
    constantSheaf_map_smul_id _ isTerminalTop] at h
  exact h

lemma smul_eq_tensorProduct_map_complexMulHom {N : Type*} [AddCommGroup N] (c : ℂ)
    (z : ℂ ⊗[ℤ] N) :
    c • z = TensorProduct.map (complexMulHom c).hom.toIntLinearMap LinearMap.id z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [TensorProduct.smul_tmul', TensorProduct.map_tmul]; rfl
  | add z z' hz hz' => rw [smul_add, map_add, hz, hz']

variable [HasExt.{0} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
  [CompactSpace X] [T2Space X]

/-- The cohomology of the abelian sheaf underlying the constant sheaf `ℂ` of `ℂ`-vector spaces on
a compact Hausdorff space is `ℂ ⊗_ℤ H^ν(X, ℤ)`. -/
noncomputable def hSheafForget₂ConstantComplexAddEquiv (ν : ℕ) :
    Sheaf.H ((sheafForget₂ (Opens.grothendieckTopology X) ℂ).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
          (ModuleCat.of ℂ ℂ))) ν ≃+
      ℂ ⊗[ℤ] Sheaf.H ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift.{0} ℤ))) ν :=
  (Sheaf.H.addEquivOfIso _ sheafForget₂ConstantComplexIso ν).trans
    (tensorCohomologyAddEquiv ν ℂ).symm

/-- The identification `hSheafForget₂ConstantComplexAddEquiv` sends the action of `c` by
functoriality to the scalar multiplication by `c` on `ℂ ⊗_ℤ H^ν(X, ℤ)`. -/
lemma hSheafForget₂ConstantComplexAddEquiv_map_smul (ν : ℕ) (c : ℂ)
    (x : Sheaf.H ((sheafForget₂ (Opens.grothendieckTopology X) ℂ).obj
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
          (ModuleCat.of ℂ ℂ))) ν) :
    hSheafForget₂ConstantComplexAddEquiv ν
        (Sheaf.H.map ((sheafForget₂ (Opens.grothendieckTopology X) ℂ).map (c • 𝟙 _)) ν x) =
      c • hSheafForget₂ConstantComplexAddEquiv ν x := by
  apply (tensorCohomologyAddEquiv ν ℂ).injective
  rw [smul_eq_tensorProduct_map_complexMulHom, tensorCohomologyAddEquiv_apply ν ℂ
    (TensorProduct.map (complexMulHom c).hom.toIntLinearMap LinearMap.id _),
    tensorCohomologyMap_naturality, ← tensorCohomologyAddEquiv_apply]
  simp only [hSheafForget₂ConstantComplexAddEquiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply]
  change Sheaf.H.map sheafForget₂ConstantComplexIso.hom ν _ =
    Sheaf.H.map _ ν (Sheaf.H.map sheafForget₂ConstantComplexIso.hom ν x)
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    sheafForget₂ConstantComplexIso_hom_naturality]

variable [HasExt.{0} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))]

/-- **Complex cohomology of a compact Hausdorff space from integral cohomology**:
`Ext^ν(ℂ_X, ℂ_X) ≃ₗ[ℂ] ℂ ⊗_ℤ H^ν(X, ℤ)`, the `Ext` taken among sheaves of `ℂ`-vector spaces. -/
noncomputable def extConstantSheafComplexLinearEquiv (ν : ℕ) :
    Abelian.Ext ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ ℂ))
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
          (ModuleCat.of ℂ ℂ)) ν ≃ₗ[ℂ]
      ℂ ⊗[ℤ] Sheaf.H ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift.{0} ℤ))) ν :=
  letI := sheafForget₂HModule (Opens.grothendieckTopology X) ℂ
    ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)) ν
  (extConstantSheafLinearEquivH _ ℂ _ ν).trans
    { hSheafForget₂ConstantComplexAddEquiv ν with
      map_smul' := hSheafForget₂ConstantComplexAddEquiv_map_smul ν }

/-- **The dimension of `H^ν(X, ℂ)` is the rank of `H^ν(X, ℤ)`** for a compact Hausdorff space
`X`: `dim_ℂ Ext^ν(ℂ_X, ℂ_X) = rank_ℤ H^ν(X, ℤ)`. -/
theorem finrank_ext_constantSheaf_complex_eq_finrank_H_int (ν : ℕ) :
    finrank ℂ (Abelian.Ext ((constantSheaf (Opens.grothendieckTopology X)
        (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ))
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
          (ModuleCat.of ℂ ℂ)) ν) =
      finrank ℤ (Sheaf.H ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℤ)) ν) := by
  rw [(extConstantSheafComplexLinearEquiv ν).finrank_eq, finrank_tensorProduct_int]
  exact (Sheaf.H.addEquivOfIso _ ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).mapIso (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddCommGrpIso)
      ν).toIntLinearEquiv.finrank_eq

end

end CompactHausdorffCohomology

namespace AlgebraicGeometry.Scheme

open CompactHausdorffCohomology

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ))

/-- **The Betti number `b_ν(Y)` is the rank of `H^ν(Y(ℂ), ℤ)`** when `Y(ℂ)` is compact
Hausdorff. -/
theorem bettiNumber_eq_finrank_analyticCohomologyConstant_int [CompactSpace (ComplexPoints y)]
    [T2Space (ComplexPoints y)] (ν : ℕ) :
    bettiNumber y ν = finrank ℤ (analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν) :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ))
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  finrank_ext_constantSheaf_complex_eq_finrank_H_int (X := TopCat.of (ComplexPoints y)) ν

/-- **The Betti number `b_ν(Y)` of a projective scheme `Y` over `ℂ` is the rank of
`H^ν(Y(ℂ), ℤ)`.** -/
theorem bettiNumber_eq_finrank_analyticCohomologyConstant_int_of_isProjective
    (hy : IsProjective y) (ν : ℕ) :
    bettiNumber y ν = finrank ℤ (analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν) :=
  have := ComplexPoints.compactSpace_of_isProjective hy
  have := ComplexPoints.t2Space_of_isProjective hy
  bettiNumber_eq_finrank_analyticCohomologyConstant_int y ν

end AlgebraicGeometry.Scheme
