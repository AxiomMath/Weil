/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.RiemannSurface
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.AnalyticInverseImage
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.AnalyticSpace
public import WeilFrontier.Geometry.Manifold.Sheaf.MeromorphicDivisorSequence
public import WeilFrontier.Geometry.Manifold.Sheaf.HolomorphicCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.RationalFunctions
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.GAGACurveFunctions

/-!
# Comparison of the algebraic and analytic divisor sequences

Let `Y` be a smooth curve over `ℂ`, so that `Y(ℂ)` is a Riemann surface, and let
`ε_* : Sh(Y(ℂ)) → Sh(Y_et)` be the analytic direct image, `(ε_* G)(U) = Hom(ℤ[Φ U], G)`, where
`Φ U` is the sheaf of continuous sections of the local homeomorphism `U(ℂ) → Y(ℂ)`.

For `U` étale over `Y`, every regular function `g` on `U` is holomorphic along every continuous
section `σ` of `U(ℂ) → Y(ℂ)`: near a point, `g` is a holomorphic function of the coordinates of
an affine open of `Y` (the local structure of étale morphisms on complex points), and those
coordinates are holomorphic on `Y(ℂ)`. Consequently a chart of the atlas of `Y(ℂ)` composed with
a local inverse of `U(ℂ) → Y(ℂ)` is a chart of the atlas of `U(ℂ)`, so composition with `σ`
preserves meromorphy and orders of functions on `U(ℂ)`.

In particular an invertible function `a` on `U` gives the nowhere vanishing holomorphic functions
`a ∘ σ`, which defines the **units comparison** `𝐆_m ⟶ ε_* 𝒪^×` from the multiplicative group of
the small étale site to the direct image of the sheaf of nowhere vanishing holomorphic functions,
and by adjunction `μ : ε^* 𝐆_m ⟶ 𝒪^×`, the first component of the comparison of the divisor
sequence `0 → 𝐆_m → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0` of Stacks 03RI with the analytic divisor
sequence `0 → 𝒪^× → 𝓜^× → 𝒟iv → 0`.

An invertible rational function `a` on an affine integral étale `U` (a curve over `ℂ`) is
analytified on `U(ℂ)` and composed with the local sections; analytification commutes with pullback
along étale morphisms off a discrete set, which gives the comparison `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^×` on
the subsite of affine integral étale schemes, cover dense since `Y` is normal. The left square
commutes because a regular function is its own analytification; the comparison
`⨁_x i_{x,*} ℤ ⟶ ε_* 𝒟iv` is induced on cokernels. The result is a morphism of short complexes
`divisorSequenceComparison` from the étale divisor sequence to `ε_*` of the analytic one.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.evalSection`, `mkSection`, `homToDirectImage`:
  sections of `ε_* G` as families of sections of `G` indexed by continuous sections of
  `U(ℂ) → Y(ℂ)`, and morphisms into `ε_* G` from such families.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticUnitsSheaf`: `𝒪^×` on the analytic site.
* `AlgebraicGeometry.Scheme.ComplexPoints.unitsComparisonToDirectImage`: `𝐆_m ⟶ ε_* 𝒪^×`.
* `AlgebraicGeometry.Scheme.ComplexPoints.unitsComparison`: its adjoint `ε^* 𝐆_m ⟶ 𝒪^×`.
* `AlgebraicGeometry.Scheme.ComplexPoints.rationalComparisonToDirectImage`: `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^×`.
* `AlgebraicGeometry.Scheme.ComplexPoints.divisorComparisonToDirectImage`:
  `⨁_x i_{x,*} ℤ ⟶ ε_* 𝒟iv`.
* `AlgebraicGeometry.Scheme.ComplexPoints.divisorSequenceComparison`: the morphism of short
  complexes.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.mdifferentiableAt_evalOrZero_comp`: regular functions
  are holomorphic along local sections of étale morphisms.
* `AlgebraicGeometry.Scheme.ComplexPoints.trans_mem_atlas`: atlas charts transported along an
  étale morphism.
* `AlgebraicGeometry.Scheme.ComplexPoints.orderAt_comp_of_etale`,
  `orderAt_comp_extendSection`: composition with a local section preserves orders and meromorphy.
* `AlgebraicGeometry.Scheme.ComplexPoints.evalSection_unitsComparisonToDirectImage`: the units
  comparison on sections, `a ↦ a ∘ σ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analytifyRat_dominantFunctionFieldMap_eventuallyEq`:
  analytification commutes with pullback along étale morphisms of curves.
* `AlgebraicGeometry.Scheme.ComplexPoints.evalSection_rationalComparisonToDirectImage`,
  `orderAt_alongSection_generic`, `evalSection_divisorComparison_secondMap`: the comparisons on
  sections over affine integral étale schemes, and the orders of `a_an ∘ σ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Filter Manifold

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### Regular functions along local sections of an étale morphism are holomorphic -/

section LocalSections

variable {Y Y' : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} {y' : Y' ⟶ Spec (.of ℂ)}
  [SmoothOfRelativeDimension 1 y] (f : Y' ⟶ Y) [Etale f] (hf : f ≫ y = y')

/-- **Regular functions are holomorphic along local sections of an étale morphism.** Let
`f : Y' ⟶ Y` be étale over `ℂ`, with `Y` a smooth curve, and `τ : Y(ℂ) → Y'(ℂ)` continuous at
`p` with `f ∘ τ = id` near `p`. Then for every regular function `g` on an open `V' ∋ τ p` of `Y'`,
the function `x ↦ g(τ x)` is holomorphic at `p`. -/
theorem mdifferentiableAt_evalOrZero_comp {V' : Y'.Opens} (g : Γ(Y', V'))
    {τ : ComplexPoints y → ComplexPoints y'} {p : ComplexPoints y}
    (hτ : ContinuousAt τ p) (hfτ : ∀ᶠ x in 𝓝 p, map f hf (τ x) = x) (hp : (τ p).Mem V') :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x => evalOrZero V' g (τ x)) p := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have hfq : map f hf (τ p) = p := hfτ.self_of_nhds
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
    (show p.hom.base pt ∈ (⊤ : Y.Opens) from trivial)
  have hpU : p.Mem U := (mem_iff pt).2 hxU
  have hqU : (τ p).Mem (f ⁻¹ᵁ U) := (map_mem_iff f hf (τ p) U).1 (by rw [hfq]; exact hpU)
  have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  obtain ⟨U'', hU'', hzU'', hU''le⟩ := (Opens.isBasis_iff_nbhd.1 Y'.isBasis_affineOpens)
    (show (τ p).hom.base pt ∈ V' ⊓ f ⁻¹ᵁ U from ⟨(mem_iff pt).1 hp, (mem_iff pt).1 hqU⟩)
  obtain ⟨n, s, hs⟩ := exists_surjective_presentationHom (z := y) hU
  obtain ⟨φ, W, hqφ, hφ, hW, hsrc, htgt, hol⟩ :=
    exists_openPartialHomeomorph_of_etale f hf hU hs hU'' (hU''le.trans inf_le_right) (τ p)
      ((mem_iff pt).2 hzU'')
  obtain ⟨G, hG, hGeq⟩ := hol (Y'.presheaf.map (homOfLE (hU''le.trans inf_le_left)).op g)
  -- near `p`, `τ` lands in the source of `φ`
  have hτsrc : ∀ᶠ x in 𝓝 p, τ x ∈ φ.source := hτ.preimage_mem_nhds (φ.open_source.mem_nhds hqφ)
  have hpt : p ∈ φ.target := by
    have := φ.map_source hqφ
    rwa [hφ, hfq] at this
  -- the function is `G` of the coordinates near `p`
  have hev : (fun x => evalOrZero V' g (τ x)) =ᶠ[𝓝 p] fun x => G (coordsOrZero s x) := by
    filter_upwards [hτsrc, hfτ] with x hx hfx
    have hxU'' : (τ x).Mem U'' := hsrc _ hx
    have hxU : (map f hf (τ x)).Mem U := (map_mem_iff f hf (τ x) U).2 (hxU''.mono
      (hU''le.trans inf_le_right))
    have hxU' : x.Mem U := hfx ▸ hxU
    rw [evalOrZero_of_mem g (hxU''.mono (hU''le.trans inf_le_left)),
      ← eval_map (hU''le.trans inf_le_left) g (τ x) hxU'', hGeq _ hx hxU'' hxU,
      coordsOrZero_of_mem s hxU']
    congr 2
    exact Subtype.ext hfx
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hev
  -- holomorphy of `G ∘ coords` in the chart at `p`
  have hcW : coordsOrZero s p ∈ W := by
    rw [htgt] at hpt
    obtain ⟨ha, hW'⟩ := hpt
    rwa [coordsOrZero_of_mem s ha]
  rw [mdifferentiableAt_iff]
  refine ⟨?_, ?_⟩
  · refine ((hG.differentiableAt (hW.mem_nhds hcW)).continuousAt).comp ?_
    exact (continuousOn_coordsOrZero s).continuousAt ((isOpen_setOf_mem U).mem_nhds hpU)
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, Set.range_id, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv]
  simp only [mfld_simps]
  refine DifferentiableAt.differentiableWithinAt ?_
  have hco : DifferentiableAt ℂ (fun z => coordsOrZero s ((chartAt ℂ p).symm z))
      (chartAt ℂ p p) :=
    differentiableAt_pi.2 fun i => differentiableAt_evalOrZero_comp_chartAt_symm (s i) hpU
  have hG' : DifferentiableAt ℂ G (coordsOrZero s ((chartAt ℂ p).symm (chartAt ℂ p p))) := by
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact hG.differentiableAt (hW.mem_nhds hcW)
  exact hG'.comp (f := fun z => coordsOrZero s ((chartAt ℂ p).symm z)) _ hco


section Charts

variable [SmoothOfRelativeDimension 1 y']

/-- **Atlas charts transported along an étale morphism.** If `φ` is a local homeomorphism
restricting `f : Y'(ℂ) → Y(ℂ)` and `e` is a chart of the atlas of `Y(ℂ)`, then `φ ≫ e` is a chart
of the atlas of `Y'(ℂ)`. -/
theorem trans_mem_atlas {φ : OpenPartialHomeomorph (ComplexPoints y') (ComplexPoints y)}
    (hφ : ⇑φ = map f hf) {e : OpenPartialHomeomorph (ComplexPoints y) ℂ}
    (he : e ∈ atlas ℂ (ComplexPoints y)) : φ.trans e ∈ atlas ℂ (ComplexPoints y') := by
  obtain ⟨⟨V, t, hV, heq⟩, -⟩ := isCurveChart_of_mem_atlas he
  refine ⟨⟨f ⁻¹ᵁ V, f.app V t, fun q hq => ?_, fun q hq => ?_⟩, fun V'' g => ?_⟩
  · have h1 : φ q ∈ e.source := hq.2
    have h2 := hV _ h1
    rw [hφ] at h2
    exact (map_mem_iff f hf q V).1 h2
  · have h1 : φ q ∈ e.source := hq.2
    have h2 := hV _ h1
    rw [hφ] at h1 h2
    have h3 : q.Mem (f ⁻¹ᵁ V) := (map_mem_iff f hf q V).1 h2
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hφ, heq h1,
      evalOrZero_of_mem _ h2, evalOrZero_of_mem _ h3, eval_map_point]
  · rintro z ⟨hz, hzV⟩
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at hz
    obtain ⟨hze, hzφ⟩ := hz
    set x := e.symm z
    have hxe : x ∈ e.source := e.map_target hze
    have hsymm : ∀ z', (φ.trans e).symm z' = φ.symm (e.symm z') := fun _ => rfl
    have hxV : (φ.symm x).Mem V'' := by
      have := hzV
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsymm] at this
      exact this
    have hA := mdifferentiableAt_evalOrZero_comp f hf g (τ := φ.symm) (p := x)
      (φ.continuousAt_symm hzφ)
      (Filter.eventually_of_mem (φ.open_target.mem_nhds hzφ) fun x' hx' => by
        rw [← hφ]; exact φ.right_inv hx') hxV
    have hD := (RiemannSurface.mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hxe).1 hA
    rw [e.right_inv hze] at hD
    exact hD.differentiableWithinAt

/-- Along a local section `τ` of an étale morphism, composition with `τ` preserves the order of a
function at a point. -/
theorem orderAt_comp_of_etale [LocallyOfFiniteType y] {τ : ComplexPoints y → ComplexPoints y'}
    {x : ComplexPoints y} (hτ : ContinuousAt τ x) (hfτ : ∀ᶠ x' in 𝓝 x, map f hf (τ x') = x')
    (h : ComplexPoints y' → ℂ) :
    RiemannSurface.orderAt (h ∘ τ) x = RiemannSurface.orderAt h (τ x) ∧
      (RiemannSurface.MeromorphicAt (h ∘ τ) x ↔ RiemannSurface.MeromorphicAt h (τ x)) := by
  obtain ⟨φ, hqφ, hφ⟩ := isLocalHomeomorph_map_of_etale f hf (τ x)
  have hfq : φ (τ x) = x := by rw [← hφ]; exact hfτ.self_of_nhds
  set e := chartAt ℂ x
  have he' := trans_mem_atlas f hf hφ.symm (chart_mem_atlas ℂ x)
  have hq' : τ x ∈ (φ.trans e).source := by
    refine ⟨hqφ, ?_⟩
    change φ (τ x) ∈ e.source
    rw [hfq]; exact mem_chart_source ℂ x
  have hτφ : τ =ᶠ[𝓝 x] φ.symm := by
    filter_upwards [hτ.preimage_mem_nhds (φ.open_source.mem_nhds hqφ), hfτ] with x' h1 h2
    rw [← φ.left_inv h1]
    congr 1
    rw [← hφ]; exact h2
  have hev : h ∘ τ ∘ e.symm =ᶠ[𝓝 (e x)] h ∘ (φ.trans e).symm := by
    have hc : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have := e.continuousAt_symm (e.map_source (mem_chart_source ℂ x))
      rwa [ContinuousAt, e.left_inv (mem_chart_source ℂ x)] at this
    filter_upwards [hc.eventually hτφ] with z hz
    simp only [Function.comp_apply]
    rw [hz]
    rfl
  have hex : (φ.trans e) (τ x) = e x := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hfq]
  refine ⟨?_, ?_⟩
  · rw [RiemannSurface.orderAt_eq_of_mem_atlas he' hq', hex,
      RiemannSurface.orderAt_eq_of_mem_atlas (chart_mem_atlas ℂ x) (mem_chart_source ℂ x)]
    exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)
  · rw [RiemannSurface.meromorphicAt_iff_of_mem_atlas he' hq', hex,
      RiemannSurface.meromorphicAt_iff_of_mem_atlas (chart_mem_atlas ℂ x) (mem_chart_source ℂ x)]
    exact _root_.MeromorphicAt.meromorphicAt_congr (hev.filter_mono nhdsWithin_le_nhds)

end Charts

end LocalSections

end AlgebraicGeometry.Scheme.ComplexPoints

namespace AlgebraicGeometry.Scheme.ComplexPoints

open Opposite
open scoped ContDiff

/-! ### Sections of the analytic direct image -/

section DirectImageSections

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

set_option hygiene false in
local notation "𝔍" => _root_.Opens.grothendieckTopology 𝔛

/-- A section of `ε_* G` over an étale `U` is a morphism from the sheaf of continuous sections of
`U(ℂ) → Y(ℂ)` to the underlying sheaf of sets of `G` (free–forgetful adjunction). -/
noncomputable def directImageSectionsEquiv (G : AnSheaf y) (U : Y.Etale) :
    ToType (((analyticDirectImage y).obj G).obj.obj (op U)) ≃
      ((sectionsFunctor y).obj U ⟶
        (sheafCompose (𝔍) (CategoryTheory.forget AddCommGrpCat.{1})).obj G) :=
  (Sheaf.adjunction (𝔍) AddCommGrpCat.adj.{1}).homEquiv _ _

/-- The value of a section `a` of `ε_* G` over `U` on a continuous section `σ` of
`U(ℂ) → Y(ℂ)` over an open `W`: a section of `G` over `W`. -/
noncomputable def evalSection {G : AnSheaf y} {U : Y.Etale}
    (a : ToType (((analyticDirectImage y).obj G).obj.obj (op U)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    ToType (G.obj.obj W) :=
  (directImageSectionsEquiv y G U a).hom.app W σ

theorem evalSection_add {G : AnSheaf y} {U : Y.Etale}
    (a b : ToType (((analyticDirectImage y).obj G).obj.obj (op U)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (a + b) σ = evalSection y a σ + evalSection y b σ := by
  simp only [evalSection, directImageSectionsEquiv]
  rfl

theorem evalSection_injective {G : AnSheaf y} {U : Y.Etale}
    {a b : ToType (((analyticDirectImage y).obj G).obj.obj (op U))}
    (h : ∀ (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : ((sectionsFunctor y).obj U).obj.obj W),
      evalSection y a σ = evalSection y b σ) : a = b := by
  apply (directImageSectionsEquiv y G U).injective
  ext W σ
  exact h W σ

theorem evalSection_map {G : AnSheaf y} {U V : Y.Etale} (φ : U ⟶ V)
    (a : ToType (((analyticDirectImage y).obj G).obj.obj (op V)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (((analyticDirectImage y).obj G).obj.map φ.op a) σ =
      evalSection y a (((sectionsFunctor y).map φ).hom.app W σ) := by
  have key := Adjunction.homEquiv_naturality_left (Sheaf.adjunction (𝔍) AddCommGrpCat.adj.{1})
    ((sectionsFunctor y).map φ) a
  exact congrArg (fun h => (h.hom.app W) σ) key

/-- A section of `ε_* G` over `U` from its values on continuous sections of `U(ℂ) → Y(ℂ)`. -/
noncomputable def mkSection {G : AnSheaf y} {U : Y.Etale}
    (t : ∀ W : (TopologicalSpace.Opens 𝔛)ᵒᵖ, ((sectionsFunctor y).obj U).obj.obj W →
      ToType (G.obj.obj W))
    (ht : ∀ {W W' : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (i : W ⟶ W')
      (σ : ((sectionsFunctor y).obj U).obj.obj W),
      t W' (((sectionsFunctor y).obj U).obj.map i σ) = G.obj.map i (t W σ)) :
    ToType (((analyticDirectImage y).obj G).obj.obj (op U)) :=
  (directImageSectionsEquiv y G U).symm
    (ObjectProperty.homMk
      { app := fun W => TypeCat.ofHom (t W)
        naturality := fun _ _ i => by
          ext σ
          exact ht i σ })

@[simp]
theorem evalSection_mkSection {G : AnSheaf y} {U : Y.Etale}
    (t : ∀ W : (TopologicalSpace.Opens 𝔛)ᵒᵖ, ((sectionsFunctor y).obj U).obj.obj W →
      ToType (G.obj.obj W))
    (ht : ∀ {W W' : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (i : W ⟶ W')
      (σ : ((sectionsFunctor y).obj U).obj.obj W),
      t W' (((sectionsFunctor y).obj U).obj.map i σ) = G.obj.map i (t W σ))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (mkSection y t ht) σ = t W σ := by
  simp only [evalSection, mkSection, Equiv.apply_symm_apply]
  rfl

/-- A morphism of étale sheaves `F ⟶ ε_* G` from a family of values, additive and natural. -/
noncomputable def homToDirectImage {F : EtSheaf Y} {G : AnSheaf y}
    (t : ∀ (U : Y.Etale) (_ : ToType (F.obj.obj (op U))) (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ),
      ((sectionsFunctor y).obj U).obj.obj W → ToType (G.obj.obj W))
    (ht : ∀ (U : Y.Etale) (a : ToType (F.obj.obj (op U))) {W W' : (TopologicalSpace.Opens 𝔛)ᵒᵖ}
      (i : W ⟶ W') (σ : ((sectionsFunctor y).obj U).obj.obj W),
      t U a W' (((sectionsFunctor y).obj U).obj.map i σ) = G.obj.map i (t U a W σ))
    (hadd : ∀ (U : Y.Etale) (a b : ToType (F.obj.obj (op U))) (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ)
      (σ : ((sectionsFunctor y).obj U).obj.obj W), t U (a + b) W σ = t U a W σ + t U b W σ)
    (hnat : ∀ {U V : Y.Etale} (φ : U ⟶ V) (a : ToType (F.obj.obj (op V)))
      (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : ((sectionsFunctor y).obj U).obj.obj W),
      t U (F.obj.map φ.op a) W σ = t V a W (((sectionsFunctor y).map φ).hom.app W σ)) :
    F ⟶ (analyticDirectImage y).obj G :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun a => mkSection y (t U.unop a) (ht U.unop a)
          map_zero' := evalSection_injective y fun W σ => by
            rw [evalSection_mkSection]
            have h0 := evalSection_add y (0 : ToType
              (((analyticDirectImage y).obj G).obj.obj U)) 0 σ
            rw [add_zero] at h0
            have h1 := hadd U.unop 0 0 W σ
            rw [add_zero] at h1
            have e1 : t U.unop 0 W σ = 0 := by
              have := congrArg (· - t U.unop 0 W σ) h1
              simpa using this.symm
            have e2 : evalSection y (0 : ToType
                (((analyticDirectImage y).obj G).obj.obj U)) σ = 0 := by
              have := congrArg (· - evalSection y (0 : ToType
                (((analyticDirectImage y).obj G).obj.obj U)) σ) h0
              simpa using this.symm
            rw [e1]
            exact e2.symm
          map_add' := fun a b => evalSection_injective y fun W σ => by
            refine (evalSection_mkSection y _ _ σ).trans ((hadd _ a b W σ).trans ?_)
            refine Eq.trans ?_ (evalSection_add y _ _ σ).symm
            rw [evalSection_mkSection, evalSection_mkSection] }
      naturality := fun U V φ => by
        ext a
        refine evalSection_injective y fun W σ => ?_
        change evalSection y (mkSection y (t V.unop _) (ht V.unop _)) σ =
          evalSection y (((analyticDirectImage y).obj G).obj.map φ.unop.op
            (mkSection y (t U.unop a) (ht U.unop a))) σ
        rw [evalSection_map, evalSection_mkSection, evalSection_mkSection]
        exact hnat φ.unop a W σ }

@[simp]
theorem evalSection_homToDirectImage {F : EtSheaf Y} {G : AnSheaf y}
    (t : ∀ (U : Y.Etale) (_ : ToType (F.obj.obj (op U))) (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ),
      ((sectionsFunctor y).obj U).obj.obj W → ToType (G.obj.obj W))
    (ht : ∀ (U : Y.Etale) (a : ToType (F.obj.obj (op U))) {W W' : (TopologicalSpace.Opens 𝔛)ᵒᵖ}
      (i : W ⟶ W') (σ : ((sectionsFunctor y).obj U).obj.obj W),
      t U a W' (((sectionsFunctor y).obj U).obj.map i σ) = G.obj.map i (t U a W σ))
    (hadd : ∀ (U : Y.Etale) (a b : ToType (F.obj.obj (op U))) (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ)
      (σ : ((sectionsFunctor y).obj U).obj.obj W), t U (a + b) W σ = t U a W σ + t U b W σ)
    (hnat : ∀ {U V : Y.Etale} (φ : U ⟶ V) (a : ToType (F.obj.obj (op V)))
      (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : ((sectionsFunctor y).obj U).obj.obj W),
      t U (F.obj.map φ.op a) W σ = t V a W (((sectionsFunctor y).map φ).hom.app W σ))
    (U : Y.Etale) (a : ToType (F.obj.obj (op U)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y ((homToDirectImage y t ht hadd hnat).hom.app (op U) a) σ = t U a W σ :=
  evalSection_mkSection y (t U a) (ht U a) σ

theorem evalSection_analyticDirectImage_map {G G' : AnSheaf y} (φ : G ⟶ G') {U : Y.Etale}
    (a : ToType (((analyticDirectImage y).obj G).obj.obj (op U)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (((analyticDirectImage y).map φ).hom.app (op U) a) σ =
      φ.hom.app W (evalSection y a σ) := by
  have key := Adjunction.homEquiv_naturality_right (Sheaf.adjunction (𝔍) AddCommGrpCat.adj.{1})
    (show (freeSectionsFunctor y).obj U ⟶ G from a) φ
  exact congrArg (fun h => (h.hom.app W) σ) key

end DirectImageSections

/-! ### Local sections, extended to all of `Y(ℂ)` -/

section Extend

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

/-- The open subset of `Y(ℂ)` underlying an open subset of `ULift Y(ℂ)`. -/
abbrev downOpens (W : TopologicalSpace.Opens 𝔛) : TopologicalSpace.Opens (ComplexPoints y) :=
  (TopCat.opensULiftEquivalence (ComplexPoints y)).functor.obj W

theorem mem_downOpens {W : TopologicalSpace.Opens 𝔛} {x : ComplexPoints y} :
    x ∈ downOpens W ↔ ULift.up x ∈ W := Iff.rfl

/-- A continuous section `σ` of `U(ℂ) → Y(ℂ)` over `W`, as a map on all of `Y(ℂ)`, equal to `d`
off `W`. -/
noncomputable def extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y)) :
    ComplexPoints y → ComplexPoints (U.hom ≫ y) :=
  open Classical in fun x => if h : ULift.up x ∈ W then (σ.1 ⟨ULift.up x, h⟩).down else d

theorem extendSection_of_mem {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y))
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) :
    extendSection σ d x = (σ.1 ⟨ULift.up x, hx⟩).down := by
  simp [extendSection, hx]

theorem map_extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y))
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) :
    map U.hom rfl (extendSection σ d x) = x := by
  rw [extendSection_of_mem σ d hx]
  exact σ.2.2 ⟨ULift.up x, hx⟩

theorem isOpen_downOpens (W : TopologicalSpace.Opens 𝔛) :
    IsOpen {x : ComplexPoints y | ULift.up x ∈ W} :=
  (downOpens W).isOpen

theorem continuousOn_extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y)) :
    ContinuousOn (extendSection σ d) {x : ComplexPoints y | ULift.up x ∈ W} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hσ : Continuous fun x : {x : ComplexPoints y | ULift.up x ∈ W} =>
      (σ.1 ⟨ULift.up x.1, x.2⟩).down :=
    continuous_uliftDown.comp (σ.2.1.comp (Continuous.subtype_mk
      (continuous_uliftUp.comp continuous_subtype_val) _))
  refine hσ.congr fun x => ?_
  simp only [Set.domRestrict_apply]
  rw [extendSection_of_mem σ d x.2]

theorem eventually_map_extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y))
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) :
    ∀ᶠ x' in 𝓝 x, map U.hom rfl (extendSection σ d x') = x' :=
  Filter.eventually_of_mem ((isOpen_downOpens W).mem_nhds hx) fun _ h => map_extendSection σ d h

end Extend

/-! ### Units along local sections -/

section Units

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 1 y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

/-- Regular functions along a local section of `U(ℂ) → Y(ℂ)` are holomorphic on its domain. -/
theorem mdifferentiableAt_evalOrZero_extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y))
    {V' : U.left.Opens} (g : Γ(U.left, V')) {x : ComplexPoints y} (hx : ULift.up x ∈ W)
    (hxV : (extendSection σ d x).Mem V') :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x' => evalOrZero V' g (extendSection σ d x')) x := by
  have : Etale U.hom := U.prop
  exact mdifferentiableAt_evalOrZero_comp U.hom rfl g
    ((continuousOn_extendSection σ d).continuousAt ((isOpen_downOpens W).mem_nhds hx))
    (eventually_map_extendSection σ d hx) hxV

/-- The invertible function `v ↦ a(σ v)` on the domain of a local section `σ`. -/
noncomputable def unitsAlong {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (a : (Γ(U.left, ⊤))ˣ) (σ : (sectionsPresheaf y U).obj (op W)) :
    downOpens W → ℂˣ :=
  fun v => Units.map (evalHom (σ.1 ⟨ULift.up v.1, v.2⟩).down (mem_top _)).toMonoidHom a

omit [SmoothOfRelativeDimension 1 y] in
theorem coe_unitsAlong {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (a : (Γ(U.left, ⊤))ˣ) (σ : (sectionsPresheaf y U).obj (op W)) (v : downOpens W) :
    ((unitsAlong a σ v : ℂˣ) : ℂ) = eval (a : Γ(U.left, ⊤)) (σ.1 ⟨ULift.up v.1, v.2⟩).down
      (mem_top _) := rfl

theorem contMDiff_unitsAlong {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (a : (Γ(U.left, ⊤))ˣ) (σ : (sectionsPresheaf y U).obj (op W)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (unitsAlong a σ) := by
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  intro v
  let d := (σ.1 ⟨ULift.up v.1, v.2⟩).down
  let g : ComplexPoints y → ℂ := fun x => evalOrZero ⊤ (a : Γ(U.left, ⊤)) (extendSection σ d x)
  have hfg : (Units.val ∘ unitsAlong a σ) = fun x : downOpens W => g x := by
    funext x
    simp only [Function.comp_apply, g, coe_unitsAlong, evalOrZero_of_mem _ (mem_top _)]
    congr 1
    rw [extendSection_of_mem σ d x.2]
  rw [hfg]
  refine contMDiffAt_subtype_iff.2 ?_
  refine RiemannSurface.contMDiffAt_of_eventually_mdifferentiableAt ?_
  filter_upwards [(isOpen_downOpens W).mem_nhds v.2] with x hx
  exact mdifferentiableAt_evalOrZero_extendSection σ d _ hx (mem_top _)

/-- An étale scheme over a smooth curve over `ℂ` is a smooth curve over `ℂ`. -/
theorem smoothOfRelativeDimension_etale_comp (U : Y.Etale) :
    SmoothOfRelativeDimension 1 (U.hom ≫ y) := by
  have : SmoothOfRelativeDimension 0 U.hom :=
    (Etale.iff_smoothOfRelativeDimension_zero U.hom).1 U.prop
  exact (inferInstance : SmoothOfRelativeDimension (0 + 1) (U.hom ≫ y))

/-- **Orders along local sections.** For a continuous section `σ` of `U(ℂ) → Y(ℂ)` over `W`,
`U` étale over the smooth curve `Y`, and a function `h` on `U(ℂ)`, the order of `h ∘ σ` at a point
`x` of `W` is the order of `h` at `σ x`, and `h ∘ σ` is meromorphic at `x` iff `h` is meromorphic
at `σ x`. -/
theorem orderAt_comp_extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y))
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) (h : ComplexPoints (U.hom ≫ y) → ℂ) :
    letI := smoothOfRelativeDimension_etale_comp (y := y) U
    RiemannSurface.orderAt (h ∘ extendSection σ d) x =
        RiemannSurface.orderAt h (extendSection σ d x) ∧
      (RiemannSurface.MeromorphicAt (h ∘ extendSection σ d) x ↔
        RiemannSurface.MeromorphicAt h (extendSection σ d x)) := by
  have := smoothOfRelativeDimension_etale_comp (y := y) U
  have : Etale U.hom := U.prop
  have : LocallyOfFiniteType y := by
    have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
    infer_instance
  exact orderAt_comp_of_etale U.hom rfl
    ((continuousOn_extendSection σ d).continuousAt ((isOpen_downOpens W).mem_nhds hx))
    (eventually_map_extendSection σ d hx) h

end Units

/-! ### The units comparison `𝐆_m ⟶ ε_* 𝒪^×` -/

section UnitsComparison

/-- A scheme smooth over `ℂ` of some relative dimension is locally of finite type over `ℂ`. -/
theorem smooth_of_smoothOfRelativeDimension_one {Y : Scheme.{0}}
    (y : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 y] : Smooth y :=
  SmoothOfRelativeDimension.smooth 1 y

theorem locallyOfFiniteType_of_smoothOfRelativeDimension_one {Y : Scheme.{0}}
    (y : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 y] : LocallyOfFiniteType y := by
  have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  infer_instance

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 y]

attribute [local instance] locallyOfFiniteType_of_smoothOfRelativeDimension_one

omit [SmoothOfRelativeDimension 1 y] in
theorem unitsAlong_map {U V : Y.Etale} (φ : U ⟶ V) (a : (Γ(V.left, ⊤))ˣ)
    {W : TopologicalSpace.Opens (TopCat.of (ULift.{1} (ComplexPoints y)))}
    (σ : (sectionsPresheaf y U).obj (op W)) :
    unitsAlong (Units.map φ.left.appTop.hom.toMonoidHom a) σ =
      unitsAlong a ((sectionsPresheafMap y φ).app (op W) σ) := by
  funext v
  refine Units.ext ?_
  rw [coe_unitsAlong, coe_unitsAlong]
  exact (eval_map_point φ.left (by rw [← Category.assoc, MorphismProperty.Over.w φ])
    (a : Γ(V.left, ⊤)) (σ.1 ⟨ULift.up v.1, v.2⟩).down (mem_top _)).symm


/-- The sheaf `𝒪^×` of nowhere vanishing holomorphic functions on the Riemann surface `Y(ℂ)`, on
the analytic site of `Y`. -/
noncomputable abbrev analyticUnitsSheaf : AnSheaf y :=
  (liftToAnalytic y).obj (ComplexManifold.holomorphicUnitsSheaf 𝓘(ℂ) (ComplexPoints y))

/-- The section `a ∘ σ` of `𝒪^×` over `W`, for an invertible function `a` on `U` and a continuous
section `σ` of `U(ℂ) → Y(ℂ)` over `W`. -/
noncomputable def unitsSection {U : Y.Etale} (a : ToType
    ((Stacks.Kummer.multiplicativeSheaf.{0, 1} Y).obj.obj (op U)))
    (W : (TopologicalSpace.Opens (TopCat.of (ULift.{1} (ComplexPoints y))))ᵒᵖ)
    (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    ToType ((analyticUnitsSheaf y).obj.obj W) :=
  ULift.up (Additive.ofMul ⟨unitsAlong (Additive.toMul a.down) σ,
    contMDiff_unitsAlong (Additive.toMul a.down) σ⟩)

/-- **The units comparison** `𝐆_m ⟶ ε_* 𝒪^×`: an invertible function `a` on an étale `U` goes to
the holomorphic units `a ∘ σ` along the continuous sections `σ` of `U(ℂ) → Y(ℂ)`. -/
noncomputable def unitsComparisonToDirectImage :
    Stacks.Kummer.multiplicativeSheaf.{0, 1} Y ⟶
      (analyticDirectImage y).obj (analyticUnitsSheaf y) :=
  homToDirectImage y (fun U a W σ => unitsSection y a W σ)
    (fun U a W W' i σ => rfl)
    (fun U a b W σ => by
      refine ULift.ext _ _ ?_
      apply Additive.toMul.injective
      refine ContMDiffMap.ext fun v => ?_
      exact map_mul (Units.map (evalHom (σ.1 ⟨ULift.up v.1, v.2⟩).down (mem_top _)).toMonoidHom)
        (show (Γ(U.left, ⊤))ˣ from Additive.toMul a.down)
        (show (Γ(U.left, ⊤))ˣ from Additive.toMul b.down))
    (fun {U V} φ a W σ => by
      refine ULift.ext _ _ ?_
      apply Additive.toMul.injective
      refine ContMDiffMap.ext fun v => ?_
      exact congrFun (unitsAlong_map y φ (Additive.toMul a.down) σ) v)

theorem evalSection_unitsComparisonToDirectImage {U : Y.Etale}
    (a : ToType ((Stacks.Kummer.multiplicativeSheaf.{0, 1} Y).obj.obj (op U)))
    {W : (TopologicalSpace.Opens (TopCat.of (ULift.{1} (ComplexPoints y))))ᵒᵖ}
    (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y ((unitsComparisonToDirectImage y).hom.app (op U) a) σ =
      unitsSection y a W σ :=
  evalSection_homToDirectImage y _ _ _ _ U a σ

/-- **The units comparison** `ε^* 𝐆_m ⟶ 𝒪^×` (FK's `μ`), adjoint to
`unitsComparisonToDirectImage`. -/
noncomputable def unitsComparison :
    (analyticInverseImage y).obj (Stacks.Kummer.multiplicativeSheaf.{0, 1} Y) ⟶
      analyticUnitsSheaf y :=
  ((analyticAdjunction y).homEquiv _ _).symm (unitsComparisonToDirectImage y)

end UnitsComparison

/-! ### The subsite of affine integral étale schemes -/

section Subsite

variable {Y : Scheme.{0}}

/-- An étale `Y`-scheme is *affine integral* if its underlying scheme is affine and integral. -/
def IsAffineIntegralEtale : ObjectProperty Y.Etale := fun U => IsAffine U.left ∧ IsIntegral U.left

set_option backward.isDefEq.respectTransparency false in
/-- Over an integral normal scheme, every étale scheme is covered by affine integral ones. -/
instance isCoverDense_isAffineIntegralEtale [IsIntegral Y] [IsNormal Y] :
    (IsAffineIntegralEtale (Y := Y)).ι.IsCoverDense Y.smallEtaleTopology where
  is_cover U := by
    have : Etale U.hom := U.prop
    refine (Scheme.mem_smallGrothendieckTopology (P := @Etale) (S := Y) U _).2 ?_
    have key : ∀ u : U.left, ∃ (W : Scheme.{0}) (g : W ⟶ U.left), IsOpenImmersion g ∧
        IsAffine W ∧ IsIntegral W ∧ u ∈ Set.range g.base := by
      intro u
      obtain ⟨Z, g, hg, hZ, z, hz⟩ :=
        Stacks.EtaleCohomology.exists_isIntegral_open_of_etale (X := Y) (Y := U.left) U.hom u
      obtain ⟨W, hW, hzW, -⟩ := (Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
        (show z ∈ (⊤ : Z.Opens) from trivial)
      have : Nonempty W := ⟨⟨z, hzW⟩⟩
      exact ⟨W, Scheme.Opens.ι (X := Z) W ≫ g, inferInstance, hW, inferInstance,
        ⟨⟨z, hzW⟩, by simp [hz]⟩⟩
    choose W g hg hWa hWi hu using key
    let 𝒰 : Cover.{0} (precoverage @Etale) U.left :=
      Cover.mkOfCovers U.left W g (fun x => by
        obtain ⟨w, hw⟩ := hu x
        exact ⟨x, w, hw⟩) (fun j => IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over Y := ⟨𝒰.f i ≫ U.hom⟩
    let _ : Cover.Over Y 𝒰 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance, fun i => MorphismProperty.comp_mem _ _ _ (𝒰.map_prop i) U.prop,
      fun X f ⟨i⟩ => ?_⟩
    have hi : IsAffineIntegralEtale (MorphismProperty.Over.mk ⊤ (𝒰.f i ≫ U.hom)
        (MorphismProperty.comp_mem _ _ _ (𝒰.map_prop i) U.prop)) := ⟨hWa i, hWi i⟩
    exact ⟨⟨⟨_, hi⟩, 𝟙 _, MorphismProperty.Over.homMk (𝒰.f i) rfl trivial, by cat_disch⟩⟩

/-- An affine integral scheme étale over a smooth curve over `ℂ` is a curve over `ℂ`. -/
theorem isCurve_of_etale {y : Y ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 1 y] {X : Scheme.{0}}
    (g : X ⟶ Y) [Etale g] [IsAffine X] [IsIntegral X] : IsCurve ℂ (g ≫ y) := by
  have : SmoothOfRelativeDimension 0 g :=
    (Etale.iff_smoothOfRelativeDimension_zero g).1 inferInstance
  have h1 : SmoothOfRelativeDimension 1 (g ≫ y) :=
    (inferInstance : SmoothOfRelativeDimension (0 + 1) (g ≫ y))
  have : Smooth (g ≫ y) := SmoothOfRelativeDimension.smooth 1 _
  have : IsAffineHom (g ≫ y) := isAffineHom_of_isAffine _
  have hqc : QuasiCompact (g ≫ y) := instQuasiCompactOfIsAffineHom _
  have hsep : IsSeparated (g ≫ y) := Scheme.instIsSeparatedOfIsSeparated _
  have hlft : LocallyOfFiniteType (g ≫ y) := inferInstance
  refine (isCurve_iff ℂ _).2 ⟨⟨⟩, ?_⟩
  exact AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 (g ≫ y)

theorem isCurve_of_isAffineIntegralEtale {y : Y ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 1 y]
    {U : Y.Etale} (hU : IsAffineIntegralEtale U) : IsCurve ℂ (U.hom ≫ y) := by
  have : IsAffine U.left := hU.1
  have : IsIntegral U.left := hU.2
  have : Etale U.hom := U.prop
  exact isCurve_of_etale (y := y) (X := U.left) U.hom

end Subsite

/-! ### Pulling rational functions back along étale morphisms -/

section Pullback

theorem germ_eqToHom_apply {X : Scheme.{0}} {U : X.Opens} {x x' : X} (e : x = x') (hx : x ∈ U)
    (hx' : x' ∈ U) (s : Γ(X, U)) :
    (eqToHom (congrArg X.presheaf.stalk e.symm)).hom (X.presheaf.germ U x' hx' s) =
      X.presheaf.germ U x hx s := by
  subst e
  rfl

/-- A flat morphism of integral schemes is dominant. -/
theorem isDominant_of_flat {X S : Scheme.{0}} [IsIntegral X] [IsIntegral S] (h : X ⟶ S)
    [AlgebraicGeometry.Flat h] :
    IsDominant h :=
  ((tfae_isDominant_of_isIntegral h).out 1 2).mpr
    (Stacks.EtaleCohomology.base_genericPoint_eq_genericPoint_of_flat h)

/-- The map on function fields of a dominant morphism sends the rational function of a regular
function to the rational function of its pullback. -/
theorem dominantFunctionFieldMap_germToFunctionField {X S : Scheme.{0}} [IsIntegral X]
    [IsIntegral S] (h : X ⟶ S) [IsDominant h] {V : S.Opens} [Nonempty V] [Nonempty (h ⁻¹ᵁ V)]
    (s : Γ(S, V)) :
    dominantFunctionFieldMap h (S.germToFunctionField V s) =
      X.germToFunctionField (h ⁻¹ᵁ V) (h.app V s) := by
  have hgen : h.base (genericPoint X) = genericPoint S :=
    ((tfae_isDominant_of_isIntegral h).out 1 2).mp ‹IsDominant h›
  change (hgen ▸ h.stalkMap (genericPoint X)).hom
    (S.presheaf.germ V (genericPoint S) _ s) = X.presheaf.germ (h ⁻¹ᵁ V) (genericPoint X) _ _
  have hmem : genericPoint X ∈ h ⁻¹ᵁ V :=
    ((genericPoint_spec X).mem_open_set_iff (h ⁻¹ᵁ V).isOpen).mpr
      (by simpa using ‹Nonempty (h ⁻¹ᵁ V)›)
  rw [← Stacks.Chow.stalkMap_eqToHom_eq_cast h _ _ hgen, CommRingCat.comp_apply,
    germ_eqToHom_apply hgen hmem _ s]
  exact Scheme.Hom.germ_stalkMap_apply h V _ _ s

/-- A local homeomorphism maps punctured neighbourhoods into punctured neighbourhoods. -/
theorem tendsto_nhdsNE_of_isLocalHomeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : IsLocalHomeomorph f) (x : A) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) := by
  obtain ⟨O, hO, hxO, hinj⟩ := hf.isLocallyInjective x
  refine tendsto_nhdsWithin_iff.2 ⟨(hf.continuous.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hxO), self_mem_nhdsWithin]
    with x' hx' hne heq
  exact hne (hinj hx' hxO heq)

/-- Codiscrete equality pulls back along a map sending punctured neighbourhoods of the points of
`S` into punctured neighbourhoods. -/
theorem eventuallyEq_codiscreteWithin_comp {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} {S : Set A}
    (hf : ∀ x ∈ S, Tendsto f (𝓝[≠] x) (𝓝[≠] (f x))) {g₁ g₂ : B → ℂ}
    (h : g₁ =ᶠ[Filter.codiscrete B] g₂) : g₁ ∘ f =ᶠ[codiscreteWithin S] g₂ ∘ f :=
  eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun x hx =>
    ((hf x hx).eventually ((eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 h)
      (f x))).mono fun _ hy _ => hy

variable {C D : Scheme.{0}} {c : C ⟶ Spec (.of ℂ)} {d : D ⟶ Spec (.of ℂ)}
  [IsIntegral C] [IsIntegral D]
  (h : C ⟶ D) (hd : h ≫ d = c) [IsDominant h]

/-- The analytification of the pullback of a rational function `g` is `g ∘ h` at every point where
`g` is regular. -/
theorem analytifyRat_dominantFunctionFieldMap {g : D.functionField} {q : ComplexPoints c}
    (hg : IsRegularAt g (map h hd q)) :
    analytifyRat (dominantFunctionFieldMap h g) q = analytifyRat g (map h hd q) := by
  obtain ⟨V, hp, s, rfl⟩ := hg
  have : Nonempty V := ⟨⟨(map h hd q).toPoint, mem_iff_toPoint_mem.1 hp⟩⟩
  have hq : q.Mem (h ⁻¹ᵁ V) := (map_mem_iff h hd q V).1 hp
  have : Nonempty (h ⁻¹ᵁ V) := ⟨⟨q.toPoint, mem_iff_toPoint_mem.1 hq⟩⟩
  rw [ratGerm_eq_germToFunctionField, dominantFunctionFieldMap_germToFunctionField,
    analytifyRat_germToFunctionField _ hq, analytifyRat_germToFunctionField _ hp, eval_map_point]

set_option linter.overlappingInstances false in
/-- **Analytification commutes with pullback along étale morphisms of curves**, off a discrete
set. -/
theorem analytifyRat_dominantFunctionFieldMap_eventuallyEq [IsCurve ℂ d]
    [SmoothOfRelativeDimension 1 d] [IsLocallyNoetherian D]
    (hloc : IsLocalHomeomorph (map h hd)) (g : D.functionField) :
    analytifyRat (dominantFunctionFieldMap h g) =ᶠ[Filter.codiscrete (ComplexPoints c)]
      analytifyRat g ∘ map h hd := by
  refine eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.2 fun q => ?_
  filter_upwards [(tendsto_nhdsNE_of_isLocalHomeomorph hloc q).eventually
    (eventually_isRegularAt g (map h hd q))] with q' hq'
  exact analytifyRat_dominantFunctionFieldMap h hd hq'

end Pullback

/-! ### Functions along local sections -/

section Along

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

/-- The function `x ↦ h(σ x)` on the domain of a continuous section `σ` of `U(ℂ) → Y(ℂ)` over
`W`, extended by `0`. -/
noncomputable def alongSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (h : ComplexPoints (U.hom ≫ y) → ℂ) :
    ComplexPoints y → ℂ :=
  open Classical in fun x => if hx : ULift.up x ∈ W then h (σ.1 ⟨ULift.up x, hx⟩).down else 0

theorem alongSection_of_mem {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (h : ComplexPoints (U.hom ≫ y) → ℂ)
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) :
    alongSection σ h x = h (σ.1 ⟨ULift.up x, hx⟩).down := by
  simp [alongSection, hx]

theorem alongSection_mul {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (h₁ h₂ : ComplexPoints (U.hom ≫ y) → ℂ) :
    alongSection σ (h₁ * h₂) = alongSection σ h₁ * alongSection σ h₂ := by
  funext x
  by_cases hx : ULift.up x ∈ W
  · simp [alongSection, hx]
  · simp [alongSection, hx]

theorem eqOn_alongSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (h : ComplexPoints (U.hom ≫ y) → ℂ)
    (d : ComplexPoints (U.hom ≫ y)) :
    Set.EqOn (alongSection σ h) (h ∘ extendSection σ d) {x | ULift.up x ∈ W} := fun x hx => by
  simp only [Function.comp_apply]
  rw [alongSection_of_mem σ h hx, extendSection_of_mem σ d hx]

theorem tendsto_extendSection {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) (d : ComplexPoints (U.hom ≫ y))
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) :
    Tendsto (extendSection σ d) (𝓝[≠] x) (𝓝[≠] (extendSection σ d x)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨((continuousOn_extendSection σ d).continuousAt
    ((isOpen_downOpens W).mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_downOpens W).mem_nhds hx),
    self_mem_nhdsWithin] with x' hx' hne heq
  apply hne
  have := congrArg (map U.hom rfl) heq
  rwa [map_extendSection σ d hx', map_extendSection σ d hx] at this

theorem alongSection_eventuallyEq {U : Y.Etale} {W : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op W)) {h₁ h₂ : ComplexPoints (U.hom ≫ y) → ℂ}
    (H : h₁ =ᶠ[Filter.codiscrete _] h₂) :
    alongSection σ h₁ =ᶠ[codiscreteWithin {x | ULift.up x ∈ W}] alongSection σ h₂ := by
  refine eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun x hx => ?_
  let d := (σ.1 ⟨ULift.up x, hx⟩).down
  filter_upwards [(tendsto_extendSection σ d hx).eventually
      ((eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 H) _),
    mem_nhdsWithin_of_mem_nhds ((isOpen_downOpens W).mem_nhds hx)] with x' h1 h2 _
  rw [eqOn_alongSection σ h₁ d h2, eqOn_alongSection σ h₂ d h2]
  exact h1

theorem isIntegral_id_obj (U : Y.Etale) [h : IsIntegral U.left] :
    IsIntegral ((𝟭 Scheme).obj U.left) := h

theorem isAffine_id_obj (U : Y.Etale) [h : IsAffine U.left] :
    IsAffine ((𝟭 Scheme).obj U.left) := h

attribute [local instance] isIntegral_id_obj isAffine_id_obj

variable [SmoothOfRelativeDimension 1 y]

/-- The analytic data of an affine integral étale `U` over the smooth curve `Y`. -/
theorem isCurve_etale_left (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left] :
    IsCurve ℂ (U.hom ≫ y) :=
  isCurve_of_isAffineIntegralEtale (y := y) ⟨inferInstance, inferInstance⟩

/-- Along a local section, the analytification of a nonzero rational function on an affine
integral étale `U` is a meromorphic unit. -/
theorem isMeromorphicUnitOn_alongSection {U : Y.Etale} [IsAffine U.left] [IsIntegral U.left]
    {W : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op W))
    {g : U.left.functionField} (hg : g ≠ 0) :
    RiemannSurface.IsMeromorphicUnitOn (alongSection σ (analytifyRat (y := U.hom ≫ y) g))
      {x | ULift.up x ∈ W} := by
  have := isCurve_etale_left (y := y) U
  have := smoothOfRelativeDimension_etale_comp (y := y) U
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve (U.hom ≫ y)
  have : IsLocallyNoetherian U.left := this
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · let d := (σ.1 ⟨ULift.up x, hx⟩).down
    have hev : alongSection σ (analytifyRat (y := U.hom ≫ y) g) =ᶠ[𝓝[≠] x]
        analytifyRat (y := U.hom ≫ y) g ∘ extendSection σ d :=
      Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds ((isOpen_downOpens W).mem_nhds hx))
        fun _ h => eqOn_alongSection σ _ d h
    refine RiemannSurface.MeromorphicAt.congr ?_ hev.symm
    exact (orderAt_comp_extendSection σ d hx _).2.2 (meromorphicAt_analytifyRat g _)
  · let d := (σ.1 ⟨ULift.up x, hx⟩).down
    have hev : alongSection σ (analytifyRat (y := U.hom ≫ y) g) =ᶠ[𝓝[≠] x]
        analytifyRat (y := U.hom ≫ y) g ∘ extendSection σ d :=
      Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds ((isOpen_downOpens W).mem_nhds hx))
        fun _ h => eqOn_alongSection σ _ d h
    rw [RiemannSurface.orderAt_congr hev, (orderAt_comp_extendSection σ d hx _).1]
    exact orderAt_analytifyRat_ne_top hg _

end Along

/-! ### The comparison of rational functions `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^×` on the subsite -/

section RationalComparison

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

attribute [local instance] isIntegral_id_obj isAffine_id_obj
  locallyOfFiniteType_of_smoothOfRelativeDimension_one smooth_of_smoothOfRelativeDimension_one

/-- The sheaf `j_* 𝐆_{m,K}` of invertible rational functions on the small étale site of `Y`. -/
noncomputable abbrev etaleRationalUnits : EtSheaf Y :=
  (Stacks.EtaleCohomology.genericPointDirectImage.{0, 1} Y).obj
    (Stacks.Kummer.multiplicativeSheaf.{0, 1} (Spec Y.functionField))

/-- The sheaf `𝓜^×` of meromorphic units of the Riemann surface `Y(ℂ)`, on the analytic site. -/
noncomputable abbrev analyticMeromorphicUnitsSheaf : AnSheaf y :=
  (liftToAnalytic y).obj (RiemannSurface.meromorphicUnitsSheaf (ComplexPoints y))

theorem flat_etale_hom (U : Y.Etale) : AlgebraicGeometry.Flat U.hom := by
  have : Etale U.hom := U.prop
  infer_instance

attribute [local instance] flat_etale_hom

/-- An invertible function on the generic fibre of an integral étale `U`, as a rational function
on `U`. -/
noncomputable def generic (U : Y.Etale) [IsIntegral U.left]
    (a : ToType ((etaleRationalUnits y).obj.obj (op U))) : U.left.functionField :=
  Stacks.EtaleCohomology.genericFibreToFunctionField U.hom
    ((Additive.toMul a.down : (Γ(Limits.pullback U.hom
      (Stacks.EtaleCohomology.genericPointInclusion Y), ⊤))ˣ) : Γ(Limits.pullback U.hom
        (Stacks.EtaleCohomology.genericPointInclusion Y), ⊤))

omit [SmoothOfRelativeDimension 1 y] in
theorem generic_ne_zero (U : Y.Etale) [IsIntegral U.left]
    (a : ToType ((etaleRationalUnits y).obj.obj (op U))) : generic y U a ≠ 0 :=
  ((Additive.toMul a.down : (Γ(Limits.pullback U.hom
      (Stacks.EtaleCohomology.genericPointInclusion Y), ⊤))ˣ).isUnit.map
    (Stacks.EtaleCohomology.genericFibreToFunctionField U.hom).hom).ne_zero

/-- The meromorphic unit `v ↦ a_an(σ v)` attached to an invertible rational function `a` on an
affine integral étale `U` and a continuous section `σ` of `U(ℂ) → Y(ℂ)`. -/
noncomputable def meromorphicSection (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left]
    (a : ToType ((etaleRationalUnits y).obj.obj (op U)))
    (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    ToType ((analyticMeromorphicUnitsSheaf y).obj.obj W) :=
  ULift.up (Additive.ofMul (RiemannSurface.meromorphicUnitsMk
    (isMeromorphicUnitOn_alongSection (y := y) σ (generic_ne_zero y U a))))

theorem meromorphicSection_map_opens (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left]
    (a : ToType ((etaleRationalUnits y).obj.obj (op U)))
    {W W' : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (i : W ⟶ W') (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    meromorphicSection y U a W' (((sectionsFunctor y).obj U).obj.map i σ) =
      (analyticMeromorphicUnitsSheaf y).obj.map i (meromorphicSection y U a W σ) := by
  refine ULift.ext _ _ ?_
  change Additive.ofMul (RiemannSurface.meromorphicUnitsMk _) =
    (RiemannSurface.meromorphicUnitsPresheaf (ComplexPoints y)).map
      ((TopCat.opensULiftEquivalence (ComplexPoints y)).functor.op.map i)
      (Additive.ofMul (RiemannSurface.meromorphicUnitsMk _))
  refine Eq.trans ?_ (RiemannSurface.meromorphicUnitsPresheaf_map_ofMul_mk _ _).symm
  refine congrArg Additive.ofMul ((RiemannSurface.meromorphicUnitsMk_eq_iff _ _).2
    (RiemannSurface.eventuallyEq_codiscreteWithin_of_eqOn fun x hx => ?_))
  have hx' : ULift.up x ∈ W.unop := i.unop.le hx
  exact (alongSection_of_mem _ _ hx).trans (alongSection_of_mem σ _ hx').symm

omit [SmoothOfRelativeDimension 1 y] in
theorem generic_add (U : Y.Etale) [IsIntegral U.left]
    (a b : ToType ((etaleRationalUnits y).obj.obj (op U))) :
    generic y U (a + b) = generic y U a * generic y U b :=
  map_mul (Stacks.EtaleCohomology.genericFibreToFunctionField U.hom).hom _ _

theorem meromorphicSection_add (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left]
    (a b : ToType ((etaleRationalUnits y).obj.obj (op U)))
    (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    meromorphicSection y U (a + b) W σ =
      meromorphicSection y U a W σ + meromorphicSection y U b W σ := by
  have := isCurve_etale_left (y := y) U
  have := smoothOfRelativeDimension_etale_comp (y := y) U
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve (U.hom ≫ y)
  refine ULift.ext _ _ ?_
  change Additive.ofMul (RiemannSurface.meromorphicUnitsMk _) =
    Additive.ofMul (RiemannSurface.meromorphicUnitsMk _ * RiemannSurface.meromorphicUnitsMk _)
  have h₁ := isMeromorphicUnitOn_alongSection (y := y) σ (generic_ne_zero y U a)
  have h₂ := isMeromorphicUnitOn_alongSection (y := y) σ (generic_ne_zero y U b)
  refine congrArg Additive.ofMul (((RiemannSurface.meromorphicUnitsMk_eq_iff _ (h₁.mul h₂)).2
    ?_).trans (RiemannSurface.meromorphicUnitsMk_mul h₁ h₂))
  refine (alongSection_eventuallyEq σ ?_).trans (Filter.EventuallyEq.of_eq (alongSection_mul σ _ _))
  rw [generic_add]
  exact analytifyRat_mul_eventuallyEq _ _

omit [SmoothOfRelativeDimension 1 y] in
theorem generic_map {U V : Y.Etale} [IsIntegral U.left] [IsIntegral V.left] (φ : U ⟶ V)
    (a : ToType ((etaleRationalUnits y).obj.obj (op V))) :
    have : Etale U.hom := U.prop
    have : Etale V.hom := V.prop
    have : Etale φ.left := etale_of_etale_over φ.left (MorphismProperty.Over.w φ)
    have := isDominant_of_flat φ.left
    generic y U ((etaleRationalUnits y).obj.map φ.op a) =
      dominantFunctionFieldMap φ.left (generic y V a) := by
  intro _ _ _ _
  exact Stacks.EtaleCohomology.genericFibreToFunctionField_appTop U.hom V.hom φ.left
    ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (Stacks.EtaleCohomology.genericPointInclusion Y)).map φ).left
    (Limits.pullback.lift_fst _ _ _) _

omit [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] in
theorem alongSection_sectionsPresheafMap {U V : Y.Etale} (φ : U ⟶ V)
    {W : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op W))
    (h : ComplexPoints (V.hom ≫ y) → ℂ) :
    alongSection ((sectionsPresheafMap y φ).app (op W) σ) h =
      alongSection σ (h ∘ etaleHomMap y φ) := by
  funext x
  by_cases hx : ULift.up x ∈ W
  · rw [alongSection_of_mem _ _ hx, alongSection_of_mem _ _ hx]
    rfl
  · simp [alongSection, hx]

theorem meromorphicSection_map_etale {U V : Y.Etale} [IsAffine U.left] [IsIntegral U.left]
    [IsAffine V.left] [IsIntegral V.left] (φ : U ⟶ V)
    (a : ToType ((etaleRationalUnits y).obj.obj (op V)))
    (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    meromorphicSection y U ((etaleRationalUnits y).obj.map φ.op a) W σ =
      meromorphicSection y V a W (((sectionsFunctor y).map φ).hom.app W σ) := by
  have : Etale U.hom := U.prop
  have : Etale V.hom := V.prop
  have : Etale φ.left := etale_of_etale_over φ.left (MorphismProperty.Over.w φ)
  have := isDominant_of_flat φ.left
  have := isCurve_etale_left (y := y) V
  have := smoothOfRelativeDimension_etale_comp (y := y) V
  have : IsLocallyNoetherian ((𝟭 Scheme).obj V.left) :=
    Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve (V.hom ≫ y)
  have : IsLocallyNoetherian V.left := this
  refine ULift.ext _ _
    (congrArg Additive.ofMul ((RiemannSurface.meromorphicUnitsMk_eq_iff _ _).2 ?_))
  refine (alongSection_eventuallyEq σ ?_).trans
    (Filter.EventuallyEq.of_eq (alongSection_sectionsPresheafMap y φ σ _).symm)
  rw [generic_map]
  exact analytifyRat_dominantFunctionFieldMap_eventuallyEq φ.left
    (by rw [← Category.assoc, MorphismProperty.Over.w φ]) (isLocalHomeomorph_etaleHomMap y φ) _

/-- The component of the comparison of rational functions at an affine integral étale `U`. -/
noncomputable def rationalComparisonApp (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left] :
    (etaleRationalUnits y).obj.obj (op U) ⟶
      ((analyticDirectImage y).obj (analyticMeromorphicUnitsSheaf y)).obj.obj (op U) :=
  AddCommGrpCat.ofHom
    { toFun := fun a => mkSection y (meromorphicSection y U a) (meromorphicSection_map_opens y U a)
      map_zero' := evalSection_injective y fun W σ => by
        rw [evalSection_mkSection]
        have h0 := evalSection_add y (0 : ToType (((analyticDirectImage y).obj
          (analyticMeromorphicUnitsSheaf y)).obj.obj (op U))) 0 σ
        rw [add_zero] at h0
        have h1 := meromorphicSection_add y U 0 0 W σ
        rw [add_zero] at h1
        have e1 : meromorphicSection y U 0 W σ = 0 := by
          have := congrArg (· - meromorphicSection y U 0 W σ) h1
          simpa using this.symm
        have e2 : evalSection y (0 : ToType (((analyticDirectImage y).obj
            (analyticMeromorphicUnitsSheaf y)).obj.obj (op U))) σ = 0 := by
          have := congrArg (· - evalSection y (0 : ToType (((analyticDirectImage y).obj
            (analyticMeromorphicUnitsSheaf y)).obj.obj (op U))) σ) h0
          simpa using this.symm
        exact e1.trans e2.symm
      map_add' := fun a b => evalSection_injective y fun W σ => by
        refine (evalSection_mkSection y _ _ σ).trans
          ((meromorphicSection_add y U a b W σ).trans ?_)
        refine Eq.trans ?_ (evalSection_add y _ _ σ).symm
        rw [evalSection_mkSection, evalSection_mkSection] }

theorem evalSection_rationalComparisonApp (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left]
    (a : ToType ((etaleRationalUnits y).obj.obj (op U))) {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ}
    (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y (rationalComparisonApp y U a) σ = meromorphicSection y U a W σ :=
  evalSection_mkSection y (meromorphicSection y U a) (meromorphicSection_map_opens y U a) σ

theorem rationalComparisonApp_naturality {U V : Y.Etale} [IsAffine U.left] [IsIntegral U.left]
    [IsAffine V.left] [IsIntegral V.left] (φ : U ⟶ V) :
    (etaleRationalUnits y).obj.map φ.op ≫ rationalComparisonApp y U =
      rationalComparisonApp y V ≫
        ((analyticDirectImage y).obj (analyticMeromorphicUnitsSheaf y)).obj.map φ.op := by
  ext a
  refine evalSection_injective y fun W σ => ?_
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, evalSection_map,
    evalSection_rationalComparisonApp, evalSection_rationalComparisonApp]
  exact meromorphicSection_map_etale y φ a W σ

/-- The comparison `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^×` on the subsite of affine integral étale schemes. -/
noncomputable def rationalComparisonRestricted :
    (IsAffineIntegralEtale (Y := Y)).ι.op ⋙ (etaleRationalUnits y).obj ⟶
      (IsAffineIntegralEtale (Y := Y)).ι.op ⋙
        ((analyticDirectImage y).obj (analyticMeromorphicUnitsSheaf y)).obj where
  app X :=
    letI : IsAffine X.unop.obj.left := X.unop.property.1
    letI : IsIntegral X.unop.obj.left := X.unop.property.2
    rationalComparisonApp y X.unop.obj
  naturality X X' φ :=
    letI : IsAffine X.unop.obj.left := X.unop.property.1
    letI : IsIntegral X.unop.obj.left := X.unop.property.2
    letI : IsAffine X'.unop.obj.left := X'.unop.property.1
    letI : IsIntegral X'.unop.obj.left := X'.unop.property.2
    letI : IsAffine ((IsAffineIntegralEtale (Y := Y)).ι.obj X.unop).left := X.unop.property.1
    letI : IsIntegral ((IsAffineIntegralEtale (Y := Y)).ι.obj X.unop).left := X.unop.property.2
    letI : IsAffine ((IsAffineIntegralEtale (Y := Y)).ι.obj X'.unop).left := X'.unop.property.1
    letI : IsIntegral ((IsAffineIntegralEtale (Y := Y)).ι.obj X'.unop).left := X'.unop.property.2
    rationalComparisonApp_naturality y ((IsAffineIntegralEtale (Y := Y)).ι.map φ.unop)

/-- **The comparison of invertible rational functions** `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^×`: an invertible
rational function `a` on an étale `U` goes to the meromorphic units `a_an ∘ σ` along the continuous
sections `σ` of `U(ℂ) → Y(ℂ)`. It is built on the affine integral étale schemes, which are cover
dense. -/
noncomputable def rationalComparisonToDirectImage :
    etaleRationalUnits y ⟶ (analyticDirectImage y).obj (analyticMeromorphicUnitsSheaf y) :=
  have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  have : IsNormal Y := Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth y
  ⟨Functor.IsCoverDense.restrictHomEquivHom (G := (IsAffineIntegralEtale (Y := Y)).ι)
    (K := Y.smallEtaleTopology) (rationalComparisonRestricted y)⟩

theorem rationalComparisonToDirectImage_app (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left] :
    (rationalComparisonToDirectImage y).hom.app (op U) = rationalComparisonApp y U := by
  have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  have : IsNormal Y := Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth y
  exact NatTrans.congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (G := (IsAffineIntegralEtale (Y := Y)).ι) (K := Y.smallEtaleTopology)
    (rationalComparisonRestricted y)) (op ⟨U, inferInstance, inferInstance⟩)

theorem evalSection_rationalComparisonToDirectImage (U : Y.Etale) [IsAffine U.left]
    [IsIntegral U.left] (a : ToType ((etaleRationalUnits y).obj.obj (op U)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y ((rationalComparisonToDirectImage y).hom.app (op U) a) σ =
      meromorphicSection y U a W σ := by
  rw [rationalComparisonToDirectImage_app]
  exact evalSection_rationalComparisonApp y U a σ

omit [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] in
/-- Morphisms of étale sheaves on an integral normal scheme agree as soon as they agree on the
affine integral étale schemes. -/
theorem hom_ext_of_isAffineIntegralEtale [IsIntegral Y] [IsNormal Y] {F G : EtSheaf Y}
    {f g : F ⟶ G}
    (h : ∀ (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left],
      f.hom.app (op U) = g.hom.app (op U)) :
    f = g :=
  Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom (G := (IsAffineIntegralEtale (Y := Y)).ι)
    (K := Y.smallEtaleTopology)).symm.injective (NatTrans.ext (funext fun X =>
      letI : IsAffine X.unop.obj.left := X.unop.property.1
      letI : IsIntegral X.unop.obj.left := X.unop.property.2
      h X.unop.obj)))

/-- **The left square of the divisor comparison**: on invertible regular functions, the units
comparison followed by `𝒪^× ⟶ 𝓜^×` is the restriction to the generic fibre followed by the
comparison of rational functions. -/
theorem multiplicativeDirectImageComparison_comp_rationalComparison :
    Stacks.EtaleCohomology.multiplicativeDirectImageComparison.{0, 1}
        (Stacks.EtaleCohomology.genericPointInclusion Y) ≫ rationalComparisonToDirectImage y =
      unitsComparisonToDirectImage y ≫ (analyticDirectImage y).map ((liftToAnalytic y).map
        (RiemannSurface.holomorphicUnitsToMeromorphicUnits (ComplexPoints y))) := by
  have : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  have : IsNormal Y := Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth y
  refine hom_ext_of_isAffineIntegralEtale fun U _ _ => ?_
  ext a
  obtain ⟨u, rfl⟩ := Stacks.Kummer.ofUnit_surjective a
  refine evalSection_injective y fun W σ => ?_
  change evalSection y ((rationalComparisonToDirectImage y).hom.app (op U)
      ((Stacks.EtaleCohomology.multiplicativeDirectImageComparison.{0, 1}
        (Stacks.EtaleCohomology.genericPointInclusion Y)).hom.app (op U)
          (Stacks.Kummer.ofUnit u))) σ =
    evalSection y (((analyticDirectImage y).map ((liftToAnalytic y).map
        (RiemannSurface.holomorphicUnitsToMeromorphicUnits (ComplexPoints y)))).hom.app (op U)
      ((unitsComparisonToDirectImage y).hom.app (op U) (Stacks.Kummer.ofUnit u))) σ
  rw [Stacks.EtaleCohomology.multiplicativeDirectImageComparison_app_ofUnit]
  refine (evalSection_rationalComparisonToDirectImage y U _ σ).trans ?_
  refine Eq.trans ?_ ((evalSection_analyticDirectImage_map y _ _ σ).trans
    (congrArg _ (evalSection_unitsComparisonToDirectImage y _ σ))).symm
  refine ULift.ext _ _ (congrArg Additive.ofMul ((RiemannSurface.meromorphicUnitsMk_eq_iff _ _).2
    (RiemannSurface.eventuallyEq_codiscreteWithin_of_eqOn fun x hx => ?_)))
  have : Nonempty (⊤ : U.left.Opens) := ⟨⟨(σ.1 ⟨ULift.up x, hx⟩).down.toPoint, trivial⟩⟩
  have hgen : generic y U (Stacks.Kummer.ofUnit.{0, 1}
      (U := (Stacks.EtaleCohomology.smallEtaleBaseChange
      (Stacks.EtaleCohomology.genericPointInclusion Y)).obj U)
      (Units.map (Limits.pullback.fst U.hom
        (Stacks.EtaleCohomology.genericPointInclusion Y)).appTop.hom.toMonoidHom u)) =
      U.left.germToFunctionField ⊤ (u : Γ(U.left, ⊤)) :=
    congrArg (fun φ => CommRingCat.Hom.hom φ (u : Γ(U.left, ⊤)))
      (Stacks.EtaleCohomology.appTop_genericFibreToFunctionField U.hom)
  refine (alongSection_of_mem σ _ hx).trans ?_
  erw [hgen]
  refine (analytifyRat_germToFunctionField _ (mem_top _)).trans ?_
  refine Eq.trans ?_ (RiemannSurface.unitsExtend_of_mem _ hx).symm
  rfl

/-- The sheaf `𝒟iv` of divisors of the Riemann surface `Y(ℂ)`, on the analytic site. -/
noncomputable abbrev analyticDivisorSheaf : AnSheaf y :=
  (liftToAnalytic y).obj (RiemannSurface.divisorSheaf (ComplexPoints y))

/-- The composite `j_* 𝐆_{m,K} ⟶ ε_* 𝓜^× ⟶ ε_* 𝒟iv`: an invertible rational function goes to
the divisors of its analytifications along local sections. -/
noncomputable abbrev rationalToAnalyticDivisor :
    etaleRationalUnits y ⟶ (analyticDirectImage y).obj (analyticDivisorSheaf y) :=
  rationalComparisonToDirectImage y ≫ (analyticDirectImage y).map ((liftToAnalytic y).map
    (RiemannSurface.meromorphicUnitsToDivisor (ComplexPoints y)))

theorem multiplicativeDirectImageComparison_comp_rationalToAnalyticDivisor :
    Stacks.EtaleCohomology.multiplicativeDirectImageComparison.{0, 1}
        (Stacks.EtaleCohomology.genericPointInclusion Y) ≫ rationalToAnalyticDivisor y = 0 := by
  rw [rationalToAnalyticDivisor, ← Category.assoc,
    multiplicativeDirectImageComparison_comp_rationalComparison, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  have : RiemannSurface.holomorphicUnitsToMeromorphicUnits (ComplexPoints y) ≫
      RiemannSurface.meromorphicUnitsToDivisor (ComplexPoints y) = 0 :=
    (RiemannSurface.divisorSequence (ComplexPoints y)).zero
  rw [this, Functor.map_zero, Functor.map_zero, Limits.comp_zero]

/-- **The comparison of divisors** `⨁_x i_{x,*} ℤ ⟶ ε_* 𝒟iv`, induced on the cokernel of
`𝐆_m ⟶ j_* 𝐆_{m,K}` by the comparison of rational functions. -/
noncomputable def divisorComparisonToDirectImage :
    Stacks.EtaleCohomology.closedPointDivisorSheaf.{0, 1} Y ⟶
      (analyticDirectImage y).obj (analyticDivisorSheaf y) :=
  haveI : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  (Limits.CokernelCofork.IsColimit.desc'
    (Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve y).gIsCokernel
    (rationalToAnalyticDivisor y)
    (multiplicativeDirectImageComparison_comp_rationalToAnalyticDivisor y)).1

theorem divisorSequenceSecondMapOfCurve_comp_divisorComparison :
    Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y ≫
        divisorComparisonToDirectImage y = rationalToAnalyticDivisor y :=
  haveI : Smooth y := SmoothOfRelativeDimension.smooth 1 y
  (Limits.CokernelCofork.IsColimit.desc'
    (Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve y).gIsCokernel
    (rationalToAnalyticDivisor y)
    (multiplicativeDirectImageComparison_comp_rationalToAnalyticDivisor y)).2

/-- **The comparison of the divisor sequences** (FK I.11, the étale and the analytic divisor
sequences of a smooth curve over `ℂ`): a morphism of short complexes from the divisor sequence
`0 → 𝐆_m → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0` of Stacks 03RI to the direct image under
`ε_*` of the analytic divisor sequence `0 → 𝒪^× → 𝓜^× → 𝒟iv → 0`. -/
noncomputable def divisorSequenceComparison :
    Stacks.EtaleCohomology.divisorSequence y ⟶
      (RiemannSurface.divisorSequence (ComplexPoints y)).map
        (liftToAnalytic y ⋙ analyticDirectImage y) where
  τ₁ := unitsComparisonToDirectImage y
  τ₂ := rationalComparisonToDirectImage y
  τ₃ := divisorComparisonToDirectImage y
  comm₁₂ := (multiplicativeDirectImageComparison_comp_rationalComparison y).symm
  comm₂₃ := (divisorSequenceSecondMapOfCurve_comp_divisorComparison y).symm

/-- **Orders along local sections.** The meromorphic unit `a_an ∘ σ` has, at a point `x` of the
domain of `σ`, the order of vanishing of the rational function `a` at the point `σ x` of `U`. -/
theorem orderAt_alongSection_generic (U : Y.Etale) [IsAffine U.left] [IsIntegral U.left]
    [IsLocallyNoetherian U.left] (a : ToType ((etaleRationalUnits y).obj.obj (op U)))
    {W : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op W))
    {x : ComplexPoints y} (hx : ULift.up x ∈ W) :
    RiemannSurface.orderAt (alongSection σ (analytifyRat (y := U.hom ≫ y) (generic y U a))) x =
      (U.left.ord (generic y U a) (σ.1 ⟨ULift.up x, hx⟩).down.toPoint : WithTop ℤ) := by
  have := isCurve_etale_left (y := y) U
  have := smoothOfRelativeDimension_etale_comp (y := y) U
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) := ‹IsLocallyNoetherian U.left›
  let d := (σ.1 ⟨ULift.up x, hx⟩).down
  have hev : alongSection σ (analytifyRat (y := U.hom ≫ y) (generic y U a)) =ᶠ[𝓝[≠] x]
      analytifyRat (y := U.hom ≫ y) (generic y U a) ∘ extendSection σ d :=
    Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds ((isOpen_downOpens W).mem_nhds hx))
      fun _ h => eqOn_alongSection σ _ d h
  rw [RiemannSurface.orderAt_congr hev, (orderAt_comp_extendSection σ d hx _).1,
    orderAt_analytifyRat (generic_ne_zero y U a), extendSection_of_mem σ d hx]

/-- **The right square on sections**: the divisor comparison applied to the étale divisor of an
invertible rational function `a` on an affine integral étale `U` is, along every local section
`σ`, the divisor of the meromorphic unit `a_an ∘ σ`. -/
theorem evalSection_divisorComparison_secondMap (U : Y.Etale) [IsAffine U.left]
    [IsIntegral U.left] (a : ToType ((etaleRationalUnits y).obj.obj (op U)))
    {W : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : ((sectionsFunctor y).obj U).obj.obj W) :
    evalSection y ((divisorComparisonToDirectImage y).hom.app (op U)
        ((Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve.{0, 1} y).hom.app (op U) a)) σ =
      ((liftToAnalytic y).map
        (RiemannSurface.meromorphicUnitsToDivisor (ComplexPoints y))).hom.app W
        (meromorphicSection y U a W σ) := by
  have h := congrArg (fun φ => evalSection y (φ.hom.app (op U) a) σ)
    (divisorSequenceSecondMapOfCurve_comp_divisorComparison y)
  refine h.trans ?_
  refine (evalSection_analyticDirectImage_map y _ _ σ).trans ?_
  exact congrArg _ (evalSection_rationalComparisonToDirectImage y U a σ)

end RationalComparison

end AlgebraicGeometry.Scheme.ComplexPoints
