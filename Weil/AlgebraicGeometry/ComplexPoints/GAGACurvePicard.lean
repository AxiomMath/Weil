/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.AlgebraicGeometry.ComplexPoints.DivisorSequenceGlobalSections
public import Weil.AlgebraicGeometry.ComplexPoints.ComparisonMap
public import Weil.AlgebraicGeometry.ComplexPoints.Compact
public import Weil.Attr

/-!
# GAGA for the Picard group of a smooth complex curve

Let `Y` be a smooth curve over `ℂ` whose complex points `Y(ℂ)` form a compact Hausdorff space
(for instance a smooth projective curve), and let `μ : ε^* 𝐆_m ⟶ 𝒪^×` be the units comparison: an
invertible regular function on an étale `U → Y` goes to the holomorphic units it defines along the
local sections of `U(ℂ) → Y(ℂ)`. The degree-one comparison map

`u¹ : H¹_et(Y, 𝐆_m) → H¹(Y(ℂ), 𝒪^×)`,

the comparison map `H¹_et(Y, 𝐆_m) → H¹(Y(ℂ), ε^* 𝐆_m)` followed by `μ`, is bijective.
This is the form in which GAGA for line bundles on curves enters Artin's comparison theorem.

The proof compares the two divisor sequences
`0 → 𝐆_m → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0` (étale) and `0 → 𝒪^× → 𝓜^× → 𝒟iv → 0` (analytic).
The morphism between them makes the connecting maps `Γ(⨁_x i_{x,*} ℤ) → H¹(𝐆_m)` and
`Γ(𝒟iv) → H¹(𝒪^×)` compatible with `u¹` and with the comparison of divisors on global sections.
Both connecting maps are onto (`H¹(j_* 𝐆_{m,K}) = 0` and `H¹(Y(ℂ), 𝓜^×) = 0`), the comparison of
divisors is bijective on global sections, and every global meromorphic unit of `Y(ℂ)` comes from a
rational function. A diagram chase then gives bijectivity.

The degree-zero part of the argument rests on a formula for the comparison map in degree zero
(`equiv₀_comparisonMapAlong`): for `τ : F ⟶ ε_* G` and its adjoint `τ♭ : ε^* F ⟶ G`, the map
`H⁰(Y, F) → H⁰(Y(ℂ), G)` given by the comparison map followed by `τ♭` is, on global sections,
`τ` followed by the identification `Γ(Y, ε_* G) = Γ(Y(ℂ), G)`.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMapAlong`: for `τ : F ⟶ ε_* G`, the comparison
  map `H^n_et(Y, F) → H^n(Y(ℂ), ε^* F)` followed by the adjoint `ε^* F ⟶ G` of `τ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.unitsComparisonH`: the map
  `H^n_et(Y, 𝐆_m) → H^n(Y(ℂ), 𝒪^×)` induced by the units comparison.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticDivisorBoundaryAn`: the connecting map
  `Γ(Y(ℂ), 𝒟iv) → H¹(Y(ℂ), 𝒪^×)` of the analytic divisor sequence.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.equiv₀_comparisonMapAlong`: the comparison map in degree
  zero, on global sections.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMapAlong_comp_extClass`: compatibility with
  the connecting maps of a morphism of short exact sequences `S ⟶ ε_* T`.
* `AlgebraicGeometry.Scheme.ComplexPoints.unitsComparisonH_divisorBoundary`: `u¹` carries the
  étale connecting map of the divisor sequence to the analytic one.
* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_unitsComparisonH_one`: `u¹` is bijective.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11,
  proof of Theorem 11.6, p. 117 (the comparison of `H¹` of the units).
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
* [serre1956] J.-P. Serre, *Géométrie algébrique et géométrie analytique*.
-/

@[expose] public section

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### The comparison map in degree zero -/

section DegreeZero

theorem _root_.CategoryTheory.Abelian.Ext.addEquiv₀_mk₀ {C : Type*} [Category C] [Abelian C]
    [HasExt C] {X Y : C} (f : X ⟶ Y) : Ext.addEquiv₀ (Ext.mk₀ f) = f := by
  rw [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]

theorem _root_.AddCommGrpCat.uliftZMultiplesAddEquiv_comp {A B : AddCommGrpCat.{1}}
    (f : AddCommGrpCat.of (ULift ℤ) ⟶ A) (g : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (f ≫ g) =
      g (AddCommGrpCat.uliftZMultiplesAddEquiv A f) := rfl

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

/-- Under the constant-sheaf adjunctions, `ε^*(constant A) ≅ constant A` followed by the adjoint of
`ψ : constant A ⟶ ε_* G` corresponds to the adjoint of `ψ` followed by
`Γ(Y, ε_* G) = Γ(Y(ℂ), G)`. -/
theorem constantSheafAdj_homEquiv_constantSheafIso_inv {A : AddCommGrpCat.{1}} {G : AnSheaf y}
    (ψ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj A ⟶
      (analyticDirectImage y).obj G) :
    (constantSheafAdj _ AddCommGrpCat.{1} isTerminalTop).homEquiv A G
        ((constantSheafIso y).inv.app A ≫ ((analyticAdjunction y).homEquiv _ _).symm ψ) =
      (constantSheafAdj _ _ (isTerminal_etaleTop Y).some).homEquiv A _ ψ ≫
        (globalSectionsIso y).hom.app G := by
  set adj1 := (constantSheafAdj _ _ (isTerminal_etaleTop Y).some).comp (analyticAdjunction y)
  set adj2 := (constantSheafAdj (Opens.grothendieckTopology (analyticSpace y)) AddCommGrpCat.{1}
    isTerminalTop).ofNatIsoRight (globalSectionsIso y).symm
  have h := adj2.homEquiv_naturality_right ((constantSheafIso y).inv.app A)
    (((analyticAdjunction y).homEquiv _ _).symm ψ)
  rw [constantSheafIso, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have h2 : adj1.homEquiv A G (((analyticAdjunction y).homEquiv _ _).symm ψ) =
      (constantSheafAdj _ _ (isTerminal_etaleTop Y).some).homEquiv A _ ψ := by
    simp [adj1, Adjunction.comp_homEquiv]
  rw [h2] at h
  rw [← h, Category.assoc]
  simp only [Iso.symm_hom, Iso.inv_hom_id_app, Category.comp_id]
  rw [constantSheafIso, Adjunction.leftAdjointUniq_inv_app]

/-- The comparison map along `τ : F ⟶ ε_* G`: the comparison map
`H^n_et(Y, F) → H^n(Y(ℂ), ε^* F)` followed by the adjoint `ε^* F ⟶ G` of `τ`. -/
noncomputable def comparisonMapAlong {F : EtSheaf Y} {G : AnSheaf y}
    (τ : F ⟶ (analyticDirectImage y).obj G) (n : ℕ) :
    Sheaf.H.{1} F n →+ Sheaf.H.{1} G n :=
  (Sheaf.H.map (((analyticAdjunction y).homEquiv _ _).symm τ) n).comp (comparisonMap y F n)

theorem comparisonMapAlong_apply {F : EtSheaf Y} {G : AnSheaf y}
    (τ : F ⟶ (analyticDirectImage y).obj G) (n : ℕ) (x : Sheaf.H.{1} F n) :
    comparisonMapAlong y τ n x =
      Sheaf.H.map (((analyticAdjunction y).homEquiv _ _).symm τ) n (comparisonMap y F n x) :=
  rfl

theorem equiv₀_comparisonMapAlong_mk₀ {F : EtSheaf Y} {G : AnSheaf y}
    (τ : F ⟶ (analyticDirectImage y).obj G)
    (φ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    Sheaf.H.equiv₀ G isTerminalTop (comparisonMapAlong y τ 0 (Ext.mk₀ φ)) =
      (globalSectionsIso y).hom.app G (τ.hom.app (op (etaleTop Y))
        (Sheaf.H.equiv₀ F (isTerminal_etaleTop Y).some (Ext.mk₀ φ))) := by
  rw [comparisonMapAlong_apply, comparisonMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    Sheaf.H.map_apply, Ext.mk₀_comp_mk₀, Category.assoc,
    ← Adjunction.homEquiv_naturality_left_symm]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, Ext.addEquiv₀_mk₀, Adjunction.homAddEquiv_apply]
  rw [Iso.app_inv]
  erw [constantSheafAdj_homEquiv_constantSheafIso_inv]
  rw [Adjunction.homEquiv_naturality_right, AddCommGrpCat.uliftZMultiplesAddEquiv_comp,
    AddCommGrpCat.uliftZMultiplesAddEquiv_comp]
  rfl

/-- **The comparison map in degree zero**: on global sections, the comparison map along
`τ : F ⟶ ε_* G` is `τ` followed by `Γ(Y, ε_* G) = Γ(Y(ℂ), G)`. -/
theorem equiv₀_comparisonMapAlong {F : EtSheaf Y} {G : AnSheaf y}
    (τ : F ⟶ (analyticDirectImage y).obj G)
    (s : ToType (F.obj.obj (op (etaleTop Y)))) :
    Sheaf.H.equiv₀ G isTerminalTop
        (comparisonMapAlong y τ 0 ((Sheaf.H.equiv₀ F (isTerminal_etaleTop Y).some).symm s)) =
      (globalSectionsIso y).hom.app G (τ.hom.app (op (etaleTop Y)) s) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Ext.mk₀ φ = (Sheaf.H.equiv₀ F (isTerminal_etaleTop Y).some).symm s :=
    ⟨_, Ext.mk₀_addEquiv₀_apply _⟩
  rw [← hφ, equiv₀_comparisonMapAlong_mk₀, hφ, AddEquiv.apply_symm_apply]

end DegreeZero

/-! ### Connecting maps -/

section Boundary

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

/-- The morphism of short complexes `ε^* S ⟶ T` adjoint to a morphism `S ⟶ ε_* T`. -/
noncomputable def adjointShortComplexHom {S : ShortComplex (EtSheaf Y)}
    {T : ShortComplex (AnSheaf y)} (ψ : S ⟶ T.map (analyticDirectImage y)) :
    S.map (analyticInverseImage y) ⟶ T where
  τ₁ := ((analyticAdjunction y).homEquiv _ _).symm ψ.τ₁
  τ₂ := ((analyticAdjunction y).homEquiv _ _).symm ψ.τ₂
  τ₃ := ((analyticAdjunction y).homEquiv _ _).symm ψ.τ₃
  comm₁₂ := by
    rw [ShortComplex.map_f, ← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    exact congrArg _ ψ.comm₁₂
  comm₂₃ := by
    rw [ShortComplex.map_g, ← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    exact congrArg _ ψ.comm₂₃

/-- **The comparison map along a morphism of short exact sequences commutes with the connecting
maps**: for `ψ : S ⟶ ε_* T` with `S` and `T` short exact, the comparison map along `ψ.τ₁` in degree
`n + 1` of the connecting map of `S` is the connecting map of `T` of the comparison map along
`ψ.τ₃` in degree `n`. -/
theorem comparisonMapAlong_comp_extClass {S : ShortComplex (EtSheaf Y)}
    {T : ShortComplex (AnSheaf y)} (hS : S.ShortExact) (hT : T.ShortExact)
    (ψ : S ⟶ T.map (analyticDirectImage y)) (n : ℕ) (x : Sheaf.H.{1} S.X₃ n) :
    comparisonMapAlong y ψ.τ₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparisonMapAlong y ψ.τ₃ n x).comp hT.extClass rfl := by
  rw [comparisonMapAlong_apply, comparisonMap_comp_extClass, Sheaf.H.map_apply,
    comparisonMapAlong_apply, Sheaf.H.map_apply]
  have h := (hS.map_of_exact (analyticInverseImage y)).extClass_naturality hT
    (adjointShortComplexHom y ψ)
  refine (Ext.comp_assoc _ _ _ _ (add_zero 1) (by lia)).trans ?_
  erw [h]
  exact (Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by lia)).symm

end Boundary

/-! ### The comparison of `H¹` of the units on a curve -/

section Curve

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one
  smooth_of_smoothOfRelativeDimension_one

attribute [local instance 10000] Stacks.EtaleCohomology.hasCoproduct_closedPointSkyscraper

omit [IsCurve ℂ y] in
/-- **The comparison map of the units** `u^n : H^n_et(Y, 𝐆_m) → H^n(Y(ℂ), 𝒪^×)`: the comparison
map `H^n_et(Y, 𝐆_m) → H^n(Y(ℂ), ε^* 𝐆_m)` followed by the units comparison `μ : ε^* 𝐆_m ⟶ 𝒪^×`. -/
noncomputable def unitsComparisonH (n : ℕ) :
    Sheaf.H.{1} (Stacks.Kummer.multiplicativeSheaf.{0, 1} Y) n →+
      Sheaf.H.{1} (analyticUnitsSheaf y) n :=
  comparisonMapAlong y (unitsComparisonToDirectImage y) n

omit [IsCurve ℂ y] in
theorem unitsComparisonH_apply (n : ℕ)
    (x : Sheaf.H.{1} (Stacks.Kummer.multiplicativeSheaf.{0, 1} Y) n) :
    unitsComparisonH y n x =
      Sheaf.H.map (unitsComparison y) n (comparisonMap y _ n x) :=
  rfl

omit [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] in
/-- The analytic divisor sequence `0 → 𝒪^× → 𝓜^× → 𝒟iv → 0` on the analytic site of `Y`. -/
noncomputable abbrev analyticDivisorSequence : ShortComplex (AnSheaf y) :=
  (RiemannSurface.divisorSequence (ComplexPoints y)).map (liftToAnalytic y)

omit [IsCurve ℂ y] in
theorem shortExact_analyticDivisorSequence [T2Space (ComplexPoints y)] :
    (analyticDivisorSequence y).ShortExact :=
  (RiemannSurface.shortExact_divisorSequence _).map_of_exact _

omit [IsCurve ℂ y] in
/-- The connecting map `Γ(Y(ℂ), 𝒟iv) → H¹(Y(ℂ), 𝒪^×)` of the analytic divisor sequence, on the
analytic site of `Y`. -/
noncomputable def analyticDivisorBoundaryAn [T2Space (ComplexPoints y)] :
    ToType ((analyticDivisorSheaf y).obj.obj (op ⊤)) →+ Sheaf.H.{1} (analyticUnitsSheaf y) 1 :=
  ((shortExact_analyticDivisorSequence y).extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (analyticDivisorSheaf y) isTerminalTop).symm.toAddMonoidHom

/-- **`u¹` and the connecting maps of the divisor sequences**: the comparison of the units carries
the étale class of a global divisor to the analytic class of the corresponding divisor of
`Y(ℂ)`. -/
theorem unitsComparisonH_divisorBoundary [T2Space (ComplexPoints y)]
    (s : ToType ((Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y).obj.obj
      (op (etaleTop Y)))) :
    unitsComparisonH y 1 (Stacks.EtaleCohomology.divisorBoundary y s) =
      analyticDivisorBoundaryAn y ((globalSectionsIso y).hom.app (analyticDivisorSheaf y)
        ((divisorComparisonToDirectImage y).hom.app (op (etaleTop Y)) s)) := by
  have hterm : Stacks.EtaleCohomology.isTerminalEtaleMkId Y = (isTerminal_etaleTop Y).some :=
    Subsingleton.elim _ _
  let ψ : Stacks.EtaleCohomology.divisorSequence y ⟶
      (analyticDivisorSequence y).map (analyticDirectImage y) := divisorSequenceComparison y
  have h := comparisonMapAlong_comp_extClass y
    (Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve y)
    (shortExact_analyticDivisorSequence y) ψ 0
    ((Sheaf.H.equiv₀ _ (isTerminal_etaleTop Y).some).symm s)
  have h0 := equiv₀_comparisonMapAlong y ψ.τ₃ s
  change comparisonMapAlong y ψ.τ₁ 1
      (((Sheaf.H.equiv₀ _ (Stacks.EtaleCohomology.isTerminalEtaleMkId Y)).symm s).comp
        (Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve y).extClass (zero_add 1)) =
    ((Sheaf.H.equiv₀ (analyticDivisorSheaf y) isTerminalTop).symm
      ((globalSectionsIso y).hom.app (analyticDivisorSheaf y)
        (ψ.τ₃.hom.app (op (etaleTop Y)) s))).comp
      (shortExact_analyticDivisorSequence y).extClass (zero_add 1)
  rw [hterm]
  erw [← h0, AddEquiv.symm_apply_apply]
  exact h

omit [IsCurve ℂ y] in
/-- `H¹(Y(ℂ), 𝓜^×) = 0` on the analytic site of `Y`, for `Y(ℂ)` compact. -/
theorem subsingleton_sheafH_analyticMeromorphicUnitsSheaf_one [T2Space (ComplexPoints y)]
    [CompactSpace (ComplexPoints y)] :
    Subsingleton (Sheaf.H.{1} (analyticMeromorphicUnitsSheaf y) 1) := by
  let := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  have := RiemannSurface.subsingleton_sheafH_meromorphicUnitsSheaf_one.{0} (M := ComplexPoints y)
  exact (liftToAnalyticHAddEquiv y _ 1).symm.injective.subsingleton

omit [IsCurve ℂ y] in
/-- **Every class of `H¹(Y(ℂ), 𝒪^×)` is the class of a divisor**, for `Y(ℂ)` compact. -/
theorem surjective_analyticDivisorBoundaryAn [T2Space (ComplexPoints y)]
    [CompactSpace (ComplexPoints y)] : Function.Surjective (analyticDivisorBoundaryAn y) := by
  have h1 := subsingleton_sheafH_analyticMeromorphicUnitsSheaf_one y
  intro z
  obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₁ _ (shortExact_analyticDivisorSequence y) z
    (@Subsingleton.elim _ h1 _ _) (zero_add 1)
  refine ⟨Sheaf.H.equiv₀ _ isTerminalTop w, ?_⟩
  change ((Sheaf.H.equiv₀ _ isTerminalTop).symm (Sheaf.H.equiv₀ _ isTerminalTop w)).comp
    (shortExact_analyticDivisorSequence y).extClass (zero_add 1) = z
  rw [AddEquiv.symm_apply_apply]
  exact hw

open Stacks.EtaleCohomology in
/-- **GAGA for `H¹` of the units on a curve** (FK I.11, proof of Theorem 11.6): for a smooth
curve `Y` over `ℂ` with `Y(ℂ)` compact Hausdorff, the comparison map
`u¹ : H¹_et(Y, 𝐆_m) → H¹(Y(ℂ), 𝒪^×)` is bijective. -/
theorem bijective_unitsComparisonH_one [T2Space (ComplexPoints y)]
    [CompactSpace (ComplexPoints y)] : Function.Bijective (unitsComparisonH y 1) := by
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve y
  have hT := shortExact_analyticDivisorSequence y
  refine ⟨?_, fun z => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨s, rfl⟩ := Stacks.EtaleCohomology.surjective_divisorBoundary y x
    rw [unitsComparisonH_divisorBoundary] at hx
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1) hx
    obtain ⟨a, ha⟩ := exists_globalSectionsIso_rationalComparison y
      (Sheaf.H.equiv₀ _ isTerminalTop x₂)
    rw [Stacks.EtaleCohomology.divisorBoundary_eq_zero_iff]
    refine ⟨a, (bijective_globalSectionsIso_divisorComparison y).1 ?_⟩
    have hsq := congrArg (fun φ => φ.hom.app (op (etaleTop Y)) a)
      (divisorSequenceSecondMapOfCurve_comp_divisorComparison y)
    have hnat := ConcreteCategory.congr_hom ((globalSectionsIso y).hom.naturality
      ((liftToAnalytic y).map (RiemannSurface.meromorphicUnitsToDivisor (ComplexPoints y))))
      ((rationalComparisonToDirectImage y).hom.app (op (etaleTop Y)) a)
    have h0 := Sheaf.H.equiv₀_naturality isTerminalTop
      ((liftToAnalytic y).map (RiemannSurface.meromorphicUnitsToDivisor (ComplexPoints y))) x₂
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at hsq hnat
    dsimp only
    erw [hsq]
    erw [hnat, ha, h0, Sheaf.H.map_apply]
    erw [hx₂]
    exact AddEquiv.apply_symm_apply _ _
  · obtain ⟨t, rfl⟩ := surjective_analyticDivisorBoundaryAn y z
    obtain ⟨s, rfl⟩ := (bijective_globalSectionsIso_divisorComparison y).2 t
    exact ⟨_, unitsComparisonH_divisorBoundary y s⟩

/-- **GAGA for `H¹` of the units on a smooth projective curve** (FK I.11, proof of
Theorem 11.6): for a smooth projective curve `Y` over `ℂ`, `u¹ : H¹_et(Y, 𝐆_m) → H¹(Y(ℂ), 𝒪^×)` is
bijective. -/
@[weil "lem_fk111_comparison_units_degree_one"]
theorem bijective_unitsComparisonH_one_of_isProjective (hy : IsProjective y) :
    Function.Bijective (unitsComparisonH y 1) :=
  have := t2Space_of_isProjective hy
  have := compactSpace_of_isProjective hy
  bijective_unitsComparisonH_one y

end Curve

end AlgebraicGeometry.Scheme.ComplexPoints
