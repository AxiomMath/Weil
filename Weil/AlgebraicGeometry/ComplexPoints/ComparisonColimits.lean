module

public import Weil.AlgebraicGeometry.ComplexPoints.ComparisonMap
public import Weil.AlgebraicGeometry.ComplexPoints.Compact
public import Weil.Topology.Sheaves.Cohomology.CompactHausdorffColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TorsionConstructibleSubsheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients

/-!
# The comparison map commutes with filtered colimits

Let `X` be a scheme locally of finite type over `ℂ` and `c^ν(X, F) : H^ν_et(X, F) → H^ν(X(ℂ), F_an)`
the comparison map. Suppose `X` is quasi-compact and quasi-separated and `X(ℂ)` is compact
Hausdorff. Étale cohomology of `X` commutes with filtered colimits of abelian sheaves (Stacks,
Tag 03Q5), the analytic inverse image `F ↦ F_an` commutes with all colimits (it is a left adjoint),
and cohomology of a compact Hausdorff space commutes with filtered colimits of sheaves. Since
`c^ν` is natural in `F`, a filtered colimit of sheaves on which every `c^ν` is bijective again has
`c^ν` bijective.

Two consequences reduce the property `PC(X)` (bijectivity of `c^ν` on all torsion sheaves) to
smaller classes of sheaves: a torsion sheaf is the filtered colimit of constructible sheaves
(Stacks, Tag 03SA), and it is the union of its `n!`-torsion subsheaves, each killed by a positive
integer.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_bijective_of_isColimit_of_compactSpace`:
  `c^ν` is bijective on the colimit of a filtered diagram on whose terms it is bijective.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_of_constructible_of_compactSpace`: `PC(X)` follows
  from bijectivity of `c^ν` on constructible sheaves.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_of_boundedTorsion_of_compactSpace`: `PC(X)` follows
  from bijectivity of `c^ν` on sheaves killed by a positive integer.
* `comparisonMap_bijective_of_isColimit`, `pc_of_constructible`, `pc_of_boundedTorsion`: the same
  for `X` proper over `ℂ` with `X(ℂ)` compact, and the `_of_isProjective` forms for `X` projective
  over `ℂ`, where `X(ℂ)` is compact.

## Implementation notes

For a proper `X` the compactness of `X(ℂ)` is a hypothesis: it is proved here only through
projectivity (`compactSpace_of_isProjective`). The étale side uses Mathlib's small étale site; the
constructible exhaustion is proved on the size-bounded small étale site of
`BigEtaleSite.containing X` and transported along `SmallEtale.sheafEquiv`, under which
constructibility on Mathlib's site is defined. Filtered diagrams are indexed by a category in
`Type 1`, the universe of the coefficient groups.

## References

* [Stacks Project, Tags 03Q5, 03SA]
* [SGA 4, Exposé XVI, §4]
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.ComplexPoints

section Etale

variable {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
  {I : Type 1} [SmallCategory I] [IsFiltered I] {D : I ⥤ EtSheaf X} {c : Cocone D}

/-- **Étale cohomology commutes with filtered colimits** (Stacks, Tag 03Q5) on a quasi-compact
quasi-separated scheme: `H^q(X, -)` carries a filtered colimit cocone to a colimit cocone. -/
theorem nonempty_isColimit_mapCocone_functorH_smallEtale (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit ((Sheaf.functorH.{1, 1, 0, 1} X.smallEtaleTopology q).mapCocone c)) := by
  have := Stacks.Cohomology.GlobalSections.additive_Γ.{1, 0, 1} X.smallEtaleTopology
  have h1 : IsIso (colimit.post D
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{1}).rightDerived q)) :=
    Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale.{1, 0} X q D
  have : IsIso (colimit.post D (Sheaf.functorH.{1, 1, 0, 1} X.smallEtaleTopology q)) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso D _ _
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{1, 0, 1}
        X.smallEtaleTopology q)
  have := preservesColimit_of_isIso_post
    (Sheaf.functorH.{1, 1, 0, 1} X.smallEtaleTopology q) D
  exact ⟨isColimitOfPreserves _ hc⟩

/-- Every étale cohomology class of a filtered colimit comes from a term of the diagram. -/
theorem exists_sheafH_map_eq_of_isColimit_smallEtale (hc : IsColimit c) (q : ℕ)
    (a : Sheaf.H.{1} c.pt q) :
    ∃ (i : I) (b : Sheaf.H.{1} (D.obj i) q), Sheaf.H.map (c.ι.app i) q b = a := by
  obtain ⟨h⟩ := nonempty_isColimit_mapCocone_functorH_smallEtale hc q
  obtain ⟨i, b, hb⟩ := Concrete.isColimit_exists_rep _ h a
  exact ⟨i, b, hb⟩

end Etale

section Main

/-- An object with a monomorphism `ι` into another, such that `k • ι = 0`, is killed by `k`. -/
private theorem zsmul_id_eq_zero_of_mono {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (ι : A ⟶ B) [Mono ι] (k : ℕ) (hk : k • ι = 0) : (k : ℤ) • 𝟙 A = 0 := by
  rw [← cancel_mono ι, Preadditive.zsmul_comp, Category.id_comp, Limits.zero_comp,
    natCast_zsmul, hk]

variable {X : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType x]

/-- **The comparison map commutes with filtered colimits.** For `X` quasi-compact and
quasi-separated with `X(ℂ)` compact Hausdorff, if `c^ν(X, D_i)` is bijective for every term of a
filtered diagram `D` and every `ν`, then `c^ν(X, colim D)` is bijective. -/
theorem comparisonMap_bijective_of_isColimit_of_compactSpace [CompactSpace X]
    [QuasiSeparatedSpace X]
    [CompactSpace (ComplexPoints x)] [T2Space (ComplexPoints x)]
    {I : Type 1} [SmallCategory I]
    [IsFiltered I] {D : I ⥤ EtSheaf X} {c : Cocone D} (hc : IsColimit c)
    (h : ∀ i n, Function.Bijective (comparisonMap x (D.obj i) n)) (n : ℕ) :
    Function.Bijective (comparisonMap x c.pt n) := by
  have hc' : IsColimit ((analyticInverseImage x).mapCocone c) := isColimitOfPreserves _ hc
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun b => ?_⟩
  · obtain ⟨i, w, rfl⟩ := exists_sheafH_map_eq_of_isColimit_smallEtale hc n a
    rw [comparisonMap_naturality] at ha
    obtain ⟨j, f, hf⟩ := CompactHausdorffCohomology.exists_H_map_eq_zero_of_isColimit
      (X := analyticSpace x) hc' n i _ ha
    have : Sheaf.H.map (D.map f) n w = 0 := by
      apply (h j n).1
      rw [comparisonMap_naturality, map_zero]
      exact hf
    rw [← c.w f, Sheaf.H.map_comp_apply, this, map_zero]
  · obtain ⟨i, z, rfl⟩ := CompactHausdorffCohomology.exists_H_map_eq_of_isColimit
      (X := analyticSpace x) hc' n b
    obtain ⟨w, rfl⟩ := (h i n).2 z
    exact ⟨_, comparisonMap_naturality x (c.ι.app i) n w⟩

/-- `PC(X)` from sheaves killed by a positive integer: a torsion sheaf is the filtered union of
its `n!`-torsion subsheaves. -/
theorem pc_of_boundedTorsion_of_compactSpace [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace (ComplexPoints x)] [T2Space (ComplexPoints x)]
    (h : ComparisonBijectiveOn x (fun F => ∃ n : ℕ, 0 < n ∧ (n : ℤ) • 𝟙 F = 0)) : PC x := by
  intro F hF n
  let K := Stacks.Torsion.torsionFiltration X.smallEtaleTopology F
  have := Stacks.Torsion.isIso_torsionFiltrationDesc X.smallEtaleTopology F hF
  have hc : IsColimit (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F)) :=
    have : IsIso ((colimit.isColimit K).desc
      (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F))) := this
    IsColimit.ofPointIso (colimit.isColimit K)
  refine comparisonMap_bijective_of_isColimit_of_compactSpace x hc
    (fun i m => h _ ⟨(i.down).factorial, Nat.factorial_pos _, ?_⟩ m) n
  have hk := kernel.condition ((i.down.factorial) • 𝟙 F)
  rw [Preadditive.comp_nsmul, Category.comp_id] at hk
  exact zsmul_id_eq_zero_of_mono (kernel.ι ((i.down.factorial) • 𝟙 F)) _ hk

/-- `PC(X)` from constructible sheaves: a torsion sheaf is a filtered colimit of constructible
sheaves (Stacks, Tag 03SA). -/
theorem pc_of_constructible_of_compactSpace [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace (ComplexPoints x)] [T2Space (ComplexPoints x)]
    (h : ComparisonBijectiveOn x
      (fun F => Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{0, 0} F)) :
    PC x := by
  intro F hF n
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{1}
  have : CompactSpace (B.obj X hX).obj := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (B.obj X hX).obj := inferInstanceAs (QuasiSeparatedSpace X)
  obtain ⟨I, hI, hfilt, D', ι', ⟨hc'⟩, hD'⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B (B.obj X hX) (e.inverse.obj F)
      (Stacks.EtaleCohomology.torsionSheafProperty_sheafEquiv_inverse B X hX F hF)
  let c₂ : Cocone (D' ⋙ e.functor) :=
    { pt := F
      ι := (e.functor.mapCocone (Cocone.mk _ ι')).ι ≫ (Functor.const I).map (e.counit.app F) }
  have hc₂ : IsColimit c₂ := (isColimitOfPreserves e.functor hc').ofIsoColimit
    (Cocone.ext (e.counitIso.app F) (fun _ ↦ rfl))
  exact comparisonMap_bijective_of_isColimit_of_compactSpace x hc₂ (fun j m => h _
    (isConstructibleAbelianSheaf_congr B (B.obj X hX) (e.unitIso.app (D'.obj j)) (hD' j)) m) n

end Main

section Proper

variable {X : Scheme.{0}} (x : X ⟶ Spec (.of ℂ))

/-- `c^ν` commutes with filtered colimits for `X` proper over `ℂ` with `X(ℂ)` compact. -/
theorem comparisonMap_bijective_of_isColimit [IsProper x] [CompactSpace (ComplexPoints x)]
    {I : Type 1} [SmallCategory I] [IsFiltered I] {D : I ⥤ EtSheaf X} {c : Cocone D}
    (hc : IsColimit c) (h : ∀ i n, Function.Bijective (comparisonMap x (D.obj i) n)) (n : ℕ) :
    Function.Bijective (comparisonMap x c.pt n) :=
  have := QuasiCompact.compactSpace_of_compactSpace x
  have := quasiSeparatedSpace_of_quasiSeparated x
  comparisonMap_bijective_of_isColimit_of_compactSpace x hc h n

/-- `PC(X)` from constructible sheaves, for `X` proper over `ℂ` with `X(ℂ)` compact. -/
theorem pc_of_constructible [IsProper x] [CompactSpace (ComplexPoints x)]
    (h : ComparisonBijectiveOn x
      (fun F => Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{0, 0} F)) :
    PC x :=
  have := QuasiCompact.compactSpace_of_compactSpace x
  have := quasiSeparatedSpace_of_quasiSeparated x
  pc_of_constructible_of_compactSpace x h

/-- `PC(X)` from sheaves killed by a positive integer, for `X` proper over `ℂ` with `X(ℂ)`
compact. -/
theorem pc_of_boundedTorsion [IsProper x] [CompactSpace (ComplexPoints x)]
    (h : ComparisonBijectiveOn x (fun F => ∃ n : ℕ, 0 < n ∧ (n : ℤ) • 𝟙 F = 0)) : PC x :=
  have := QuasiCompact.compactSpace_of_compactSpace x
  have := quasiSeparatedSpace_of_quasiSeparated x
  pc_of_boundedTorsion_of_compactSpace x h

/-- A projective scheme over `ℂ` is proper over `ℂ`. -/
theorem isProper_of_isProjective (hx : IsProjective x) : IsProper x :=
  isProper_of_isProjectiveMorphism x (isProjectiveMorphism_of_isProjective_of_isAffine x hx)

variable [LocallyOfFiniteType x]

/-- `c^ν` commutes with filtered colimits for `X` projective over `ℂ`. -/
theorem comparisonMap_bijective_of_isColimit_of_isProjective (hx : IsProjective x)
    {I : Type 1} [SmallCategory I] [IsFiltered I] {D : I ⥤ EtSheaf X} {c : Cocone D}
    (hc : IsColimit c) (h : ∀ i n, Function.Bijective (comparisonMap x (D.obj i) n)) (n : ℕ) :
    Function.Bijective (comparisonMap x c.pt n) :=
  have := isProper_of_isProjective x hx
  have := compactSpace_of_isProjective hx
  comparisonMap_bijective_of_isColimit x hc h n

/-- `PC(X)` from constructible sheaves, for `X` projective over `ℂ`. -/
theorem pc_of_constructible_of_isProjective (hx : IsProjective x)
    (h : ComparisonBijectiveOn x
      (fun F => Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{0, 0} F)) :
    PC x :=
  have := isProper_of_isProjective x hx
  have := compactSpace_of_isProjective hx
  pc_of_constructible x h

/-- `PC(X)` from sheaves killed by a positive integer, for `X` projective over `ℂ`. -/
theorem pc_of_boundedTorsion_of_isProjective (hx : IsProjective x)
    (h : ComparisonBijectiveOn x (fun F => ∃ n : ℕ, 0 < n ∧ (n : ℤ) • 𝟙 F = 0)) : PC x :=
  have := isProper_of_isProjective x hx
  have := compactSpace_of_isProjective hx
  pc_of_boundedTorsion x h

end Proper

end AlgebraicGeometry.Scheme.ComplexPoints
