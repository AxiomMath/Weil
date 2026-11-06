/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.EtaleLocalHomeomorph

/-!
# The complex points of a smooth curve over `ℂ` form a Riemann surface

Let `C` be a scheme with a morphism `c : C ⟶ Spec ℂ` smooth of relative dimension `1`, and give
`C(ℂ)` the analytic topology. Locally on `C`, `c` factors through an étale morphism to the affine
line `𝔸¹_ℂ = Spec ℂ[x]` (a standard smooth algebra of relative dimension `1` is étale over a
polynomial ring in one variable). An étale morphism is a local homeomorphism on complex points,
and its local inverses are holomorphic in the coordinate `x`: every regular function is, near a
point, a holomorphic function of `x`. The local inverses of the étale coordinates therefore form
an atlas of `C(ℂ)` modelled on `ℂ`, whose transition maps are holomorphic: `C(ℂ)` is a
one-dimensional complex manifold. The charts are open partial homeomorphisms for the analytic
topology itself, so the manifold topology is the analytic one.

In this atlas every regular function on an open `V` of `C` is holomorphic on `V(ℂ)`, and every
morphism of smooth curves over `ℂ` induces a holomorphic map.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.affineLineHomeomorph`: `𝔸¹(ℂ) ≃ₜ ℂ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.IsCurveChart`: an open partial homeomorphism
  `C(ℂ) → ℂ` given by a regular function, in which every regular function is holomorphic.
* `AlgebraicGeometry.Scheme.ComplexPoints.instChartedSpace`: the charted space structure on
  `C(ℂ)` over `ℂ` for `c` smooth of relative dimension `1`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.exists_etale_affineLine`: a smooth curve is étale over
  `𝔸¹_ℂ` locally around every complex point.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_isCurveChart`: every complex point lies in the
  source of a chart `IsCurveChart`.
* `AlgebraicGeometry.Scheme.ComplexPoints.instIsManifold`: `IsManifold 𝓘(ℂ) ⊤ (ComplexPoints c)`
  (complex analytic transition maps), hence `IsManifold 𝓘(ℂ) n` for every `n`.
* `AlgebraicGeometry.Scheme.ComplexPoints.mdifferentiableOn_evalOrZero`: regular functions are
  holomorphic.
* `AlgebraicGeometry.Scheme.ComplexPoints.mdifferentiable_map`: morphisms of smooth curves over
  `ℂ` are holomorphic.

## Implementation notes

The model space is `ℂ`, so only relative dimension `1` is treated. In relative dimension `d` the
same argument gives charts to `ℂ^d` with transition maps complex differentiable in each chart,
and their complex analyticity needs the theory of holomorphic functions of several variables.
Holomorphy in a chart is stated as complex differentiability (`DifferentiableOn ℂ`); in one
variable this implies analyticity (`DifferentiableOn.contDiffOn`), which gives the analytic
manifold structure.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
* [SGA1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exposé XII, §1–3.
* [Stacks] The Stacks Project, Tag 054L (smooth morphisms are étale over affine space locally).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Filter Manifold

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### The affine line -/

section AffineLine

/-- The structure morphism of the affine line `𝔸¹_ℂ = Spec ℂ[x]` over `ℂ`. -/
noncomputable def affineLineHom : Spec (.of (MvPolynomial (Fin 1) ℂ)) ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.C)

/-- The coordinate `x` of the affine line, as a global function. -/
noncomputable def affineLineCoord : Fin 1 → Γ(Spec (.of (MvPolynomial (Fin 1) ℂ)), ⊤) :=
  fun i => (Scheme.ΓSpecIso _).inv (MvPolynomial.X i)

/-- The coordinate `x` presents `Γ(𝔸¹, ⊤) ≅ ℂ[x]`: the presentation map is the identification
`ℂ[x] ≅ Γ(Spec ℂ[x], ⊤)`. -/
theorem presentationHom_affineLineCoord :
    presentationHom affineLineHom affineLineCoord =
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) ℂ))).inv.hom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [presentationHom, MvPolynomial.eval₂Hom_C, constHom, affineLineHom]
    rw [appLE_top_top_eq_appTop, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  · simp [presentationHom, affineLineCoord]

/-- There are no relations: the zero set of the presentation of `𝔸¹` is all of `ℂ¹`. -/
theorem zeroLocus_affineLineCoord : zeroLocus affineLineHom affineLineCoord = Set.univ := by
  refine Set.eq_univ_of_forall fun z P hP => ?_
  rw [RingHom.mem_ker, presentationHom_affineLineCoord] at hP
  have : P = 0 := by
    have h := congrArg (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) ℂ))).hom.hom hP
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, map_zero] at h
    exact h
  simp [this]

theorem surjective_presentationHom_affineLineCoord :
    Function.Surjective (presentationHom affineLineHom affineLineCoord) := by
  rw [presentationHom_affineLineCoord]
  exact (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) ℂ))).commRingCatIsoToRingEquiv.symm.surjective

/-- The complex points of the affine line, `𝔸¹(ℂ) ≃ₜ ℂ`, `a ↦ x(a)`. -/
noncomputable def affineLineHomeomorph : ComplexPoints affineLineHom ≃ₜ ℂ :=
  ((homeomorphZeroLocusOfIsAffine surjective_presentationHom_affineLineCoord).trans
    ((Homeomorph.setCongr zeroLocus_affineLineCoord).trans (Homeomorph.Set.univ _))).trans
    (Homeomorph.funUnique (Fin 1) ℂ)

theorem affineLineHomeomorph_apply (a : ComplexPoints affineLineHom) :
    affineLineHomeomorph a = eval (affineLineCoord 0) a (mem_top a) := rfl

/-- The coordinates of a point of `𝔸¹(ℂ)` in the presentation `affineLineCoord`. -/
theorem coords_affineLineCoord (a : ComplexPoints affineLineHom) (ha : a.Mem ⊤) :
    coords affineLineHom affineLineCoord ⟨a, ha⟩ = fun _ => affineLineHomeomorph a := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

end AffineLine

/-! ### Charts on the complex points of a smooth curve -/

variable {C : Scheme.{0}} {c : C ⟶ Spec (.of ℂ)}

/-- **Smooth curves are étale over the affine line, locally.** If `c` is smooth of relative
dimension `1`, every complex point `p` lies in an affine open `V` admitting an étale morphism
`Spec Γ(C, V) ⟶ 𝔸¹_ℂ` over `ℂ`. -/
theorem exists_etale_affineLine [SmoothOfRelativeDimension 1 c] (p : ComplexPoints c) :
    ∃ (V : C.Opens) (hV : IsAffineOpen V)
      (f : Spec Γ(C, V) ⟶ Spec (.of (MvPolynomial (Fin 1) ℂ))),
      p.Mem V ∧ Etale f ∧ f ≫ affineLineHom = hV.fromSpec ≫ c := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨U, hU, V, hV, hx, e, hst⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c)
      (p.hom.base pt)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun z _ => by
    rw [Subsingleton.elim z (c.base (p.hom.base pt))]
    exact e hx
  obtain ⟨g, hgC, hg⟩ := hst.exists_etale_mvPolynomial
  let ρ : ℂ ≃+* Γ(Spec (.of ℂ), ⊤) := (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm
  let m : CommRingCat.of (MvPolynomial (Fin 1) ℂ) ≅
      CommRingCat.of (MvPolynomial (Fin 1) Γ(Spec (.of ℂ), ⊤)) :=
    (MvPolynomial.mapEquiv (Fin 1) ρ).toCommRingCatIso
  have : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.2 hg
  refine ⟨V, hV, Spec.map (CommRingCat.ofHom g) ≫ Spec.map m.hom, (mem_iff pt).2 hx,
    inferInstance, ?_⟩
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hV e,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, affineLineHom, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change g (MvPolynomial.map ρ.toRingHom (MvPolynomial.C r)) = _
  rw [MvPolynomial.map_C, ← RingHom.comp_apply g MvPolynomial.C, hgC]
  rfl


/-- An *algebraic holomorphic chart* of `C(ℂ)`: an open partial homeomorphism `e` to `ℂ` which
is given on its source by a regular function `t` on an open `V ⊇ e.source`, and in which every
regular function `g` on every open `V'` of `C` is holomorphic: `g ∘ e⁻¹` is complex
differentiable on `e(e.source ∩ V'(ℂ))`. -/
def IsCurveChart (e : OpenPartialHomeomorph (ComplexPoints c) ℂ) : Prop :=
  (∃ (V : C.Opens) (t : Γ(C, V)), (∀ q ∈ e.source, q.Mem V) ∧
      Set.EqOn e (evalOrZero V t) e.source) ∧
  ∀ (V : C.Opens) (g : Γ(C, V)),
    DifferentiableOn ℂ (evalOrZero V g ∘ e.symm) (e.target ∩ e.symm ⁻¹' {q | q.Mem V})

/-- **Every complex point of a smooth curve lies in an algebraic holomorphic chart.** The
chart is the étale coordinate `Spec Γ(C, V) ⟶ 𝔸¹` of `exists_etale_affineLine` restricted, by
`exists_openPartialHomeomorph_of_etale`, to a neighbourhood of `p` on which it is a
homeomorphism onto an open subset of `𝔸¹(ℂ) ≃ₜ ℂ`. -/
theorem exists_isCurveChart [SmoothOfRelativeDimension 1 c] (p : ComplexPoints c) :
    ∃ e : OpenPartialHomeomorph (ComplexPoints c) ℂ, p ∈ e.source ∧ IsCurveChart e := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨V, hV, f, hpV, hfe, hf⟩ := exists_etale_affineLine p
  set y' : Spec Γ(C, V) ⟶ Spec (.of ℂ) := hV.fromSpec ≫ c
  let J : ComplexPoints y' → ComplexPoints c := map hV.fromSpec rfl
  have hJ : IsOpenEmbedding J := isOpenEmbedding_map_of_isOpenImmersion _ rfl
  have hrange : Set.range J = {q | q.Mem V} := by
    rw [range_map_of_isOpenImmersion, IsAffineOpen.opensRange_fromSpec]
  obtain ⟨q₀, hq₀⟩ : p ∈ Set.range J := hrange ▸ hpV
  have : Nonempty (ComplexPoints y') := ⟨q₀⟩
  have htop : (⊤ : (Spec Γ(C, V)).Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  obtain ⟨φ, W, hq₀φ, hφ, -, -, -, -⟩ :=
    exists_openPartialHomeomorph_of_etale f hf (isAffineOpen_top _)
      surjective_presentationHom_affineLineCoord (isAffineOpen_top _) htop q₀ (mem_top q₀)
  let κ := affineLineHomeomorph
  let J' := hJ.toOpenPartialHomeomorph J
  let e := J'.symm.trans (φ.trans κ.toOpenPartialHomeomorph)
  have he_symm : ∀ z, e.symm z = J (φ.symm (κ.symm z)) := fun z => rfl
  have he_apply : ∀ q, e q = κ (φ (J'.symm q)) := fun q => rfl
  have hsrc : ∀ q, q ∈ e.source ↔ ∃ q' ∈ φ.source, J q' = q := by
    intro q
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ, Set.inter_univ, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨⟨q', -, rfl⟩, h⟩
      exact ⟨q', by rwa [hJ.toOpenPartialHomeomorph_left_inv] at h, rfl⟩
    · rintro ⟨q', h, rfl⟩
      exact ⟨⟨q', trivial, rfl⟩, by rwa [hJ.toOpenPartialHomeomorph_left_inv]⟩
  refine ⟨e, (hsrc p).2 ⟨q₀, hq₀φ, hq₀⟩,
    ⟨⟨V, (Scheme.ΓSpecIso Γ(C, V)).hom (f.appLE ⊤ ⊤ htop (affineLineCoord 0)), ?_, ?_⟩, ?_⟩⟩
  · intro q hq
    obtain ⟨q', -, rfl⟩ := (hsrc q).1 hq
    exact hrange.subset ⟨q', rfl⟩
  · intro q hq
    obtain ⟨q', -, rfl⟩ := (hsrc q).1 hq
    have hmem : (J q').Mem V := hrange.subset ⟨q', rfl⟩
    have key := eval_appLE hV.fromSpec rfl hV.fromSpec_preimage_self.ge
      ((Scheme.ΓSpecIso Γ(C, V)).hom (f.appLE ⊤ ⊤ htop (affineLineCoord 0))) q' (mem_top q')
    rw [fromSpec_appLE_top, Iso.hom_inv_id_apply, eval_appLE f hf htop] at key
    rw [he_apply, hJ.toOpenPartialHomeomorph_left_inv, hφ, affineLineHomeomorph_apply,
      evalOrZero_of_mem _ hmem]
    exact key
  · intro V'' g z₀ hz₀
    have htgt : ∀ z, z ∈ e.target ↔ κ.symm z ∈ φ.target := by
      intro z
      simp [e, J', κ]
    obtain ⟨hz₀t, hz₀V⟩ := hz₀
    rw [htgt] at hz₀t
    set a₀ := κ.symm z₀ with ha₀
    set q₀' := φ.symm a₀ with hq₀'
    have hJq : (J q₀').Mem V'' := by rw [← he_symm]; exact hz₀V
    obtain ⟨U'', hU'', hxU'', hU''le⟩ :=
      (Opens.isBasis_iff_nbhd.1 (Spec Γ(C, V)).isBasis_affineOpens)
        (show q₀'.hom.base pt ∈ hV.fromSpec ⁻¹ᵁ V'' from (mem_iff pt).1 hJq)
    obtain ⟨φ₂, W₂, hq₂, hφ₂, hW₂, hsrc₂, htgt₂, hol₂⟩ :=
      exists_openPartialHomeomorph_of_etale f hf (isAffineOpen_top _)
        surjective_presentationHom_affineLineCoord hU'' (by simp) q₀' ((mem_iff pt).2 hxU'')
    obtain ⟨G, hG, hGeq⟩ := hol₂ (hV.fromSpec.appLE V'' U'' hU''le g)
    let ιc : ℂ → (Fin 1 → ℂ) := fun z _ => z
    have hφq : φ q₀' = a₀ := φ.right_inv hz₀t
    have hmemW : ιc z₀ ∈ W₂ := by
      have h1 : φ₂ q₀' ∈ φ₂.target := φ₂.map_source hq₂
      rw [htgt₂] at h1
      obtain ⟨ha, h2⟩ := h1
      rw [coords_affineLineCoord, hφ₂, ← hφ, hφq, ha₀, Homeomorph.apply_symm_apply] at h2
      exact h2
    have hdiff : DifferentiableAt ℂ (G ∘ ιc) z₀ :=
      (hG.differentiableAt (hW₂.mem_nhds hmemW)).comp z₀
        (differentiableAt_pi.2 fun _ => differentiableAt_id)
    have hopen : IsOpen (κ.symm ⁻¹' (φ.target ∩ φ.symm ⁻¹' φ₂.source)) :=
      (φ.isOpen_inter_preimage_symm φ₂.open_source).preimage κ.symm.continuous
    have hev : (evalOrZero V'' g ∘ e.symm) =ᶠ[𝓝 z₀] G ∘ ιc := by
      filter_upwards [hopen.mem_nhds ⟨hz₀t, hq₂⟩] with z hz
      obtain ⟨hzt, hz2⟩ := hz
      have hqU : (φ.symm (κ.symm z)).Mem U'' := hsrc₂ _ hz2
      have hJqV : (J (φ.symm (κ.symm z))).Mem V'' := (map_mem_iff _ _ _ _).2 (hqU.mono hU''le)
      simp only [Function.comp_apply, he_symm]
      rw [evalOrZero_of_mem _ hJqV, ← eval_appLE hV.fromSpec rfl hU''le g _ hqU,
        hGeq _ hz2 hqU (mem_top _), coords_affineLineCoord, ← hφ, φ.right_inv hzt,
        Homeomorph.apply_symm_apply]
    exact (hdiff.congr_of_eventuallyEq hev).differentiableWithinAt


variable [SmoothOfRelativeDimension 1 c]

/-- **The complex points of a smooth curve over `ℂ` are a charted space over `ℂ`**, for the
analytic topology, with atlas the algebraic holomorphic charts (`IsCurveChart`). -/
noncomputable instance instChartedSpace : ChartedSpace ℂ (ComplexPoints c) where
  atlas := {e | IsCurveChart e}
  chartAt p := (exists_isCurveChart p).choose
  mem_chart_source p := (exists_isCurveChart p).choose_spec.1
  chart_mem_atlas p := (exists_isCurveChart p).choose_spec.2

/-- The charts of the atlas of `C(ℂ)` are algebraic holomorphic charts. -/
theorem isCurveChart_of_mem_atlas {e : OpenPartialHomeomorph (ComplexPoints c) ℂ}
    (he : e ∈ atlas ℂ (ComplexPoints c)) : IsCurveChart e := he

/-- The preferred chart at `p` is an algebraic holomorphic chart. -/
theorem isCurveChart_chartAt (p : ComplexPoints c) : IsCurveChart (chartAt ℂ p) :=
  (exists_isCurveChart p).choose_spec.2

/-- **The complex points of a smooth curve over `ℂ` form a Riemann surface**: the transition maps
of the atlas are holomorphic, hence complex analytic. In particular
`IsManifold 𝓘(ℂ) 1 (ComplexPoints c)` holds by `IsManifold.of_le`. -/
instance instIsManifold : IsManifold 𝓘(ℂ) ⊤ (ComplexPoints c) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨⟨V', t', hV', heq'⟩, -⟩ := isCurveChart_of_mem_atlas he'
  simp only [modelWithCornersSelf_coe, Set.range_id, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.inter_univ]
  refine DifferentiableOn.contDiffOn ?_ (e.symm.trans e').open_source
  refine ((isCurveChart_of_mem_atlas he).2 V' t' |>.mono ?_).congr ?_
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    exact ⟨hz.1, hV' _ hz.2⟩
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    exact heq' hz.2

/-- A regular function `g` on an open `V ∋ p` is complex differentiable in the chart at `p`. -/
theorem differentiableAt_evalOrZero_comp_chartAt_symm {V : C.Opens} (g : Γ(C, V))
    {p : ComplexPoints c} (hp : p.Mem V) :
    DifferentiableAt ℂ (evalOrZero V g ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
  have hopen : IsOpen ((chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' {q | q.Mem V}) :=
    (chartAt ℂ p).isOpen_inter_preimage_symm (isOpen_setOf_mem V)
  refine ((isCurveChart_chartAt p).2 V g).differentiableAt (hopen.mem_nhds ⟨?_, ?_⟩)
  · exact (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact hp

/-- **Regular functions are holomorphic.** A regular function `g ∈ Γ(C, V)` on an open `V` of a
smooth curve over `ℂ` is holomorphic on `V(ℂ)` (as the function `evalOrZero V g`, equal to
`q ↦ g(q)` on `V(ℂ)`). -/
theorem mdifferentiableOn_evalOrZero (V : C.Opens) (g : Γ(C, V)) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (evalOrZero V g) {q : ComplexPoints c | q.Mem V} := by
  intro p hp
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [mdifferentiableAt_iff]
  refine ⟨(continuousOn_evalOrZero V g).continuousAt ((isOpen_setOf_mem V).mem_nhds hp), ?_⟩
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, Set.range_id, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv]
  simp only [mfld_simps]
  exact (differentiableAt_evalOrZero_comp_chartAt_symm g hp).differentiableWithinAt


/-- **Morphisms of smooth curves are holomorphic.** A morphism `φ : C ⟶ D` over `ℂ` of curves
smooth of relative dimension `1` over `ℂ` induces a holomorphic map `C(ℂ) → D(ℂ)`. -/
theorem mdifferentiable_map {D : Scheme.{0}} {d : D ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension 1 d] (φ : C ⟶ D) (hφ : φ ≫ d = c) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (map φ hφ) := by
  intro p
  rw [mdifferentiableAt_iff]
  refine ⟨(continuous_map φ hφ).continuousAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, Set.range_id]
  simp only [mfld_simps]
  refine DifferentiableAt.differentiableWithinAt ?_
  set e := chartAt ℂ p
  set e' := chartAt ℂ (map φ hφ p)
  obtain ⟨⟨V', t', hV', heq'⟩, -⟩ := isCurveChart_chartAt (map φ hφ p)
  have hmp : map φ hφ p ∈ e'.source := mem_chart_source ℂ _
  have hpV : p.Mem (φ ⁻¹ᵁ V') := hV' _ hmp
  have hd := differentiableAt_evalOrZero_comp_chartAt_symm (φ.app V' t') hpV
  refine hd.congr_of_eventuallyEq ?_
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' (map φ hφ ⁻¹' e'.source)) :=
    e.isOpen_inter_preimage_symm (e'.open_source.preimage (continuous_map φ hφ))
  have hmem : e p ∈ e.target ∩ e.symm ⁻¹' (map φ hφ ⁻¹' e'.source) := by
    refine ⟨e.map_source (mem_chart_source ℂ p), ?_⟩
    simp only [Set.mem_preimage]
    rw [e.left_inv (mem_chart_source ℂ p)]
    exact hmp
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨-, hz⟩ := hz
  have hzV : (map φ hφ (e.symm z)).Mem V' := hV' _ hz
  simp only [Function.comp_apply]
  have hzV' : (e.symm z).Mem (φ ⁻¹ᵁ V') := hzV
  rw [heq' hz, evalOrZero_of_mem _ hzV, evalOrZero_of_mem _ hzV', eval_map_point]

end AlgebraicGeometry.Scheme.ComplexPoints
