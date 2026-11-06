module

public import WeilFrontier.Geometry.Manifold.Complex.CechDolbeaultShrinking
public import WeilFrontier.Analysis.Complex.BoundedHolomorphic
public import WeilFrontier.Analysis.Normed.Operator.Compact.SurjectivePerturbation

/-!
# Finite dimensionality of bounded Čech cohomology of a line bundle

Let `M` be a Riemann surface, `𝔇` a finite disc cover of `M` (coordinate discs
`W i ⊇ U i ⊇ U' i ⊇ U'' i`, the smallest ones covering `M`) and `g` a holomorphic line bundle on
the discs `W i`, given by its transition functions. The bounded holomorphic `1`-cocycles with
values in `g` on the smallest discs form a Banach space `𝔇.BddCocycles g 𝔇.U''`, and the coboundary
of bounded holomorphic `0`-cochains, `(δη) i j = η i - g i j * η j`, is a continuous linear map
`𝔇.bddCoboundary g _` into it. We show that its range has finite codimension: together with a
finite-dimensional subspace it spans all bounded cocycles. This is the finiteness theorem of
Cartan and Serre for the first cohomology of a line bundle on a compact Riemann surface, in the
form of Schwartz's perturbation argument.

The proof considers the Banach space `E` of pairs `(ξ, η)` of a bounded cocycle `ξ` on the discs
`U'` and a bounded `0`-cochain `η` on the discs `U''`, and the two continuous linear maps
`Φ (ξ, η) = ξ|U'' + δη` and `Ψ (ξ, η) = ξ|U''` from `E` to the bounded cocycles on `U''`. The
map `Φ` is surjective by the Dolbeault shrinking decomposition
(`RiemannSurface.DiscCover.exists_decomposition`), and `Ψ` is a compact operator since the
restriction of bounded holomorphic functions to a relatively compact subset is compact
(Montel's theorem, `Complex.boundedHolomorphic.isCompactOperator_restrictL`). The perturbation
lemma `ContinuousLinearMap.exists_finiteDimensional_range_sub_sup_eq_top` for the surjective
operator `Φ` and the compact operator `Ψ` then applies to `Φ - Ψ = δ ∘ snd`.

## Main definitions

* `RiemannSurface.boundedHolomorphic S`: the bounded holomorphic functions on a subset `S` of a
  Riemann surface, as a subspace of `S →ᵇ ℂ`; for `S` open in the source of a chart it is closed,
  hence a Banach space.
* `RiemannSurface.BddCochains V`, `RiemannSurface.BddCochains₁ V`: bounded holomorphic `0`- and
  `1`-cochains on a family of sets `V i`, with the supremum norm.
* `RiemannSurface.DiscCover.BddCocycles g V`: the bounded holomorphic `1`-cocycles with values in
  the line bundle `g`, a closed subspace of `BddCochains₁ V`.
* `RiemannSurface.DiscCover.bddCoboundary g hV`: the coboundary of bounded `0`-cochains.
* `RiemannSurface.DiscCover.cocycleRestrictL g h`: restriction of bounded cocycles to smaller
  sets.

## Main results

* `RiemannSurface.boundedHolomorphic.isCompactOperator_restrictL`: restriction of bounded
  holomorphic functions on an open subset of a chart to a subset whose image has compact closure
  inside the image of the larger one is a compact operator.
* `RiemannSurface.DiscCover.isCompactOperator_cocycleRestrictL`: restriction of bounded cocycles
  from the discs `U'` to the discs `U''` is a compact operator.
* `RiemannSurface.DiscCover.exists_finiteDimensional_sup_range_coboundary`: the range of the
  coboundary into the bounded cocycles on `U''` has a finite-dimensional complement.

## Implementation notes

Bounded holomorphic functions on a subset `S` of `M` are bounded continuous functions on the
subtype `S` which agree with a function on `M` holomorphic on `S`. All the sets used lie in the
source of one chart (the discs of index `i`, and their intersections with other discs, in the
chart of the `i`-th centre), and closedness and the compactness of restriction are transported
from the corresponding statements for open subsets of `ℂ` through that chart. A `1`-cochain is
written in the trivialisation of its first index, as in
`RiemannSurface.DiscCover.IsCocycleOn`.

## References

* [H. Cartan, J.-P. Serre, *Un théorème de finitude concernant les variétés analytiques
  compactes*][cartanserre1953].
* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], §14.
-/

@[expose] public noncomputable section

open Manifold Set Filter Topology Metric BoundedContinuousFunction

namespace RiemannSurface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-! ### Bounded holomorphic functions on subsets of a Riemann surface -/

/-- The bounded holomorphic functions on a set `S` of a Riemann surface `M`, as a subspace of the
Banach space `S →ᵇ ℂ`: those bounded continuous functions which agree on `S` with a function
`M → ℂ` holomorphic on `S`. -/
def boundedHolomorphic (S : Set M) : Submodule ℂ (S →ᵇ ℂ) where
  carrier := {f | ∃ F : M → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S ∧ ∀ x : S, f x = F x}
  add_mem' := by
    rintro f g ⟨F, hF, hFf⟩ ⟨G, hG, hGg⟩
    exact ⟨F + G, hF.add hG, fun x => by simp [hFf, hGg]⟩
  zero_mem' := ⟨0, mdifferentiableOn_const, fun _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hFf⟩
    exact ⟨c • F, hF.const_smul c, fun x => by simp [hFf]⟩

variable {S T : Set M}

theorem mem_boundedHolomorphic {f : S →ᵇ ℂ} :
    f ∈ boundedHolomorphic S ↔
      ∃ F : M → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S ∧ ∀ x : S, f x = F x :=
  Iff.rfl

namespace boundedHolomorphic

/-- A function holomorphic and bounded on `S`, as an element of `boundedHolomorphic S`. -/
def mk (F : M → ℂ) (hF : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S)
    (hb : BddAbove ((fun x => ‖F x‖) '' S)) : boundedHolomorphic S :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun x : S => F x)
      (continuousOn_iff_continuous_domRestrict.1 hF.continuousOn) (hb.choose)
      (fun x => hb.choose_spec (mem_image_of_mem _ x.2)),
    F, hF, fun _ => rfl⟩

@[simp]
theorem mk_apply (F : M → ℂ) (hF : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S)
    (hb : BddAbove ((fun x => ‖F x‖) '' S)) (x : S) :
    (mk F hF hb : S →ᵇ ℂ) x = F x :=
  rfl

/-- Every element of `boundedHolomorphic S` is given by a function holomorphic and bounded on
`S`. -/
theorem exists_eq (f : boundedHolomorphic S) :
    ∃ F : M → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S ∧ BddAbove ((fun x => ‖F x‖) '' S) ∧
      ∀ x : S, (f : S →ᵇ ℂ) x = F x := by
  obtain ⟨F, hF, hFf⟩ := f.2
  refine ⟨F, hF, ⟨‖(f : S →ᵇ ℂ)‖, ?_⟩, hFf⟩
  rintro _ ⟨x, hx, rfl⟩
  change ‖F x‖ ≤ _
  rw [← hFf ⟨x, hx⟩]
  exact (f : S →ᵇ ℂ).norm_coe_le_norm _

theorem compContinuous_inclusion_mem (hST : T ⊆ S) {f : S →ᵇ ℂ}
    (hf : f ∈ boundedHolomorphic S) :
    f.compContinuous ⟨inclusion hST, continuous_inclusion hST⟩ ∈ boundedHolomorphic T := by
  obtain ⟨F, hF, e⟩ := hf
  exact ⟨F, hF.mono hST, fun x => e _⟩

theorem mul_mem {f g : S →ᵇ ℂ} (hf : f ∈ boundedHolomorphic S)
    (hg : g ∈ boundedHolomorphic S) : f * g ∈ boundedHolomorphic S := by
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  exact ⟨F * G, hF.mul hG, fun x => by simp [eF, eG]⟩

/-- Restriction of bounded holomorphic functions on `S` to a subset `T`. -/
def restrictL (hTS : T ⊆ S) : boundedHolomorphic S →L[ℂ] boundedHolomorphic T :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(f : S →ᵇ ℂ).compContinuous ⟨inclusion hTS, continuous_inclusion hTS⟩,
        compContinuous_inclusion_mem hTS f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun f => by
      rw [one_mul]
      exact norm_compContinuous_le (f : S →ᵇ ℂ) ⟨inclusion hTS, continuous_inclusion hTS⟩

@[simp]
theorem restrictL_apply (hTS : T ⊆ S) (f : boundedHolomorphic S) (x : T) :
    (restrictL hTS f : T →ᵇ ℂ) x = (f : S →ᵇ ℂ) (inclusion hTS x) :=
  rfl

/-- Multiplication by a bounded holomorphic function `g` on `S`. -/
def mulL (g : boundedHolomorphic S) : boundedHolomorphic S →L[ℂ] boundedHolomorphic S :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(g : S →ᵇ ℂ) * f, mul_mem g.2 f.2⟩
      map_add' := fun _ _ => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c _ => Subtype.ext (mul_smul_comm c _ _) }
    ‖g‖ fun f => norm_mul_le (g : S →ᵇ ℂ) f

@[simp]
theorem mulL_apply (g f : boundedHolomorphic S) (x : S) :
    (mulL g f : S →ᵇ ℂ) x = (g : S →ᵇ ℂ) x * (f : S →ᵇ ℂ) x :=
  rfl

end boundedHolomorphic

/-! ### Transport to a chart -/

section Transport

variable (e : OpenPartialHomeomorph M ℂ) (hS : S ⊆ e.source)

/-- The chart `e` as a map from `S ⊆ e.source` onto its image. -/
def chartRestrict : C(S, e '' S) :=
  ⟨fun x => ⟨e x, mem_image_of_mem _ x.2⟩,
    (e.continuousOn.mono hS).domRestrict.subtype_mk _⟩

omit [ChartedSpace ℂ M] in
include hS in
theorem symm_mem_of_mem_image (z : e '' S) : e.symm z ∈ S := by
  obtain ⟨x, hx, hxz⟩ := z.2
  rw [← hxz, e.left_inv (hS hx)]
  exact hx

/-- The inverse of the chart `e` as a map from the image of `S ⊆ e.source` back to `S`. -/
def chartRestrictSymm : C(e '' S, S) :=
  ⟨fun z => ⟨e.symm z, symm_mem_of_mem_image e hS z⟩, by
    refine Continuous.subtype_mk ?_ _
    refine (e.continuousOn_symm.mono ?_).domRestrict
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hS hx)⟩

omit [ChartedSpace ℂ M] in
theorem chartRestrictSymm_chartRestrict (x : S) :
    chartRestrictSymm e hS (chartRestrict e hS x) = x :=
  Subtype.ext (e.left_inv (hS x.2))

omit [ChartedSpace ℂ M] in
theorem chartRestrict_chartRestrictSymm (z : e '' S) :
    chartRestrict e hS (chartRestrictSymm e hS z) = z := by
  obtain ⟨_, ⟨x, hx, rfl⟩⟩ := z
  refine Subtype.ext ?_
  change e (e.symm (e x)) = e x
  rw [e.left_inv (hS hx)]

/-- Bounded continuous functions on `S ⊆ e.source` and on its image under the chart `e`
correspond isometrically. -/
def chartTransport : (S →ᵇ ℂ) ≃ₗᵢ[ℂ] (e '' S →ᵇ ℂ) where
  toFun f := f.compContinuous (chartRestrictSymm e hS)
  invFun f := f.compContinuous (chartRestrict e hS)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by ext x; simp [chartRestrictSymm_chartRestrict]
  right_inv f := by ext z; simp [chartRestrict_chartRestrictSymm]
  norm_map' f := by
    refine le_antisymm (norm_compContinuous_le _ _) ?_
    calc ‖f‖ = ‖(f.compContinuous (chartRestrictSymm e hS)).compContinuous
          (chartRestrict e hS)‖ := by
          congr 1; ext x; simp [chartRestrictSymm_chartRestrict]
      _ ≤ _ := norm_compContinuous_le _ _

omit [ChartedSpace ℂ M] in
@[simp]
theorem chartTransport_apply (f : S →ᵇ ℂ) (z : e '' S) :
    chartTransport e hS f z = f (chartRestrictSymm e hS z) :=
  rfl

omit [ChartedSpace ℂ M] in
@[simp]
theorem chartTransport_symm_apply (f : e '' S →ᵇ ℂ) (x : S) :
    (chartTransport e hS).symm f x = f (chartRestrict e hS x) :=
  rfl

variable [IsManifold 𝓘(ℂ) 1 M]

/-- For `S` open in the source of a chart `e` of the atlas, a bounded continuous function on `S`
is holomorphic if and only if it is holomorphic read in the chart. -/
theorem mem_boundedHolomorphic_iff_chartTransport_mem (he : e ∈ atlas ℂ M) (hSo : IsOpen S)
    (f : S →ᵇ ℂ) :
    f ∈ boundedHolomorphic S ↔
      chartTransport e hS f ∈ Complex.boundedHolomorphic (e '' S) := by
  constructor
  · rintro ⟨F, hF, hFf⟩
    refine ⟨F ∘ e.symm, ?_, fun z => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h := (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he (hS hx)).1
        ((hF x hx).mdifferentiableAt (hSo.mem_nhds hx))
      exact h.differentiableWithinAt
    · simp only [chartTransport_apply, hFf]
      rfl
  · rintro ⟨G, hG, hGf⟩
    have hSo' : IsOpen (e '' S) := e.isOpen_image_of_subset_source hSo hS
    refine ⟨G ∘ e, fun x hx => ?_, fun x => ?_⟩
    · refine MDifferentiableAt.mdifferentiableWithinAt ?_
      rw [mdifferentiableAt_iff_differentiableAt_of_mem_atlas he (hS hx)]
      have hG' : DifferentiableAt ℂ G (e x) :=
        (hG _ (mem_image_of_mem _ hx)).differentiableAt
          (hSo'.mem_nhds (mem_image_of_mem _ hx))
      refine hG'.congr_of_eventuallyEq ?_
      filter_upwards [e.open_target.mem_nhds (e.map_source (hS hx))] with z hz
      simp [e.right_inv hz]
    · have := hGf (chartRestrict e hS x)
      simp only [chartTransport_apply, chartRestrictSymm_chartRestrict] at this
      exact this

include hS in
/-- For `S` open in the source of a chart of the atlas, `boundedHolomorphic S` is closed. -/
theorem isClosed_boundedHolomorphic (he : e ∈ atlas ℂ M) (hSo : IsOpen S) :
    IsClosed (boundedHolomorphic S : Set (S →ᵇ ℂ)) := by
  have h : (boundedHolomorphic S : Set (S →ᵇ ℂ)) =
      chartTransport e hS ⁻¹' (Complex.boundedHolomorphic (e '' S)) := by
    ext f
    exact mem_boundedHolomorphic_iff_chartTransport_mem e hS he hSo f
  rw [h]
  exact (Complex.isClosed_boundedHolomorphic (e.isOpen_image_of_subset_source hSo hS)).preimage
    (chartTransport e hS).continuous

include hS in
/-- For `S` open in the source of a chart of the atlas, `boundedHolomorphic S` is a Banach
space. -/
theorem completeSpace_boundedHolomorphic (he : e ∈ atlas ℂ M) (hSo : IsOpen S) :
    CompleteSpace (boundedHolomorphic S) :=
  IsClosed.completeSpace_coe (hs := isClosed_boundedHolomorphic e hS he hSo)

/-- Reading bounded holomorphic functions on `S` in the chart `e`. -/
def toChartL (he : e ∈ atlas ℂ M) (hSo : IsOpen S) :
    boundedHolomorphic S →L[ℂ] Complex.boundedHolomorphic (e '' S) :=
  ((chartTransport e hS).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (boundedHolomorphic S).subtypeL).codRestrict _
    fun f => (mem_boundedHolomorphic_iff_chartTransport_mem e hS he hSo f).1 f.2

/-- Bounded holomorphic functions on the image of `S` under the chart `e`, as functions on
`S`. -/
def ofChartL (he : e ∈ atlas ℂ M) (hSo : IsOpen S) :
    Complex.boundedHolomorphic (e '' S) →L[ℂ] boundedHolomorphic S :=
  ((chartTransport e hS).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Complex.boundedHolomorphic (e '' S)).subtypeL).codRestrict _
    fun f => (mem_boundedHolomorphic_iff_chartTransport_mem e hS he hSo _).2 (by
      simp)

end Transport

section Compact

variable [IsManifold 𝓘(ℂ) 1 M]

/-- Restriction of bounded holomorphic functions from an open set `S` in the source of a chart
`e` to an open subset `T` whose image in the chart has compact closure inside the image of `S` is
a compact operator. -/
theorem boundedHolomorphic.isCompactOperator_restrictL {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) (hSo : IsOpen S) (hS : S ⊆ e.source) (hTo : IsOpen T) (hTS : T ⊆ S)
    (hc : IsCompact (closure (e '' T))) (hcl : closure (e '' T) ⊆ e '' S) :
    IsCompactOperator (boundedHolomorphic.restrictL hTS) := by
  have hTe : T ⊆ e.source := hTS.trans hS
  have key : (boundedHolomorphic.restrictL hTS : boundedHolomorphic S → boundedHolomorphic T) =
      ofChartL e hTe he hTo ∘
        (Complex.boundedHolomorphic.restrictL (subset_closure.trans hcl)) ∘
          toChartL e hS he hSo := by
    funext f
    refine Subtype.ext ?_
    ext x
    change (f : S →ᵇ ℂ) (inclusion hTS x) = (f : S →ᵇ ℂ) (chartRestrictSymm e hS
      (inclusion (subset_closure.trans hcl) (chartRestrict e hTe x)))
    congr 1
    exact Subtype.ext (e.left_inv (hTe x.2)).symm
  rw [key]
  exact ((Complex.boundedHolomorphic.isCompactOperator_restrictL
    (e.isOpen_image_of_subset_source hSo hS) hc hcl).comp_clm _).clm_comp _

end Compact

/-! ### Compact operators into finite products -/

/-- A map into a finite product is a compact operator when each of its components is. -/
theorem isCompactOperator_pi {E : Type*} [TopologicalSpace E] [AddCommMonoid E] {κ : Type*}
    [Finite κ] {F : κ → Type*} [∀ k, TopologicalSpace (F k)] {f : E → ∀ k, F k}
    (h : ∀ k, IsCompactOperator fun x => f x k) : IsCompactOperator f := by
  simp only [isCompactOperator_iff_exists_mem_nhds_image_subset_compact] at h ⊢
  choose V hV K hK hVK using h
  refine ⟨⋂ k, V k, iInter_mem.2 hV, univ.pi K, isCompact_univ_pi hK, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ k -
  exact hVK k ⟨x, mem_iInter.1 hx k, rfl⟩

/-! ### Bounded holomorphic cochains and cocycles of a disc cover -/

section Cochains

variable {ι : Type*}

/-- Bounded holomorphic `0`-cochains on a family of sets `V i`. -/
abbrev BddCochains (V : ι → Set M) : Type _ := ∀ i, boundedHolomorphic (V i)

/-- Bounded holomorphic `1`-cochains on a family of sets `V i`: a bounded holomorphic function
on each `V i ∩ V j`. -/
abbrev BddCochains₁ (V : ι → Set M) : Type _ := ∀ i j, boundedHolomorphic (V i ∩ V j)

variable {V V' : ι → Set M}

/-- Restriction of bounded `1`-cochains from the sets `V i` to smaller sets `V' i`. -/
def cochainRestrictL (h : ∀ i, V' i ⊆ V i) : BddCochains₁ V →L[ℂ] BddCochains₁ V' :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (boundedHolomorphic.restrictL (inter_subset_inter (h i) (h j))).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun j => boundedHolomorphic (V i ∩ V j)) j).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun i => ∀ j, boundedHolomorphic (V i ∩ V j)) i))

@[simp]
theorem cochainRestrictL_apply (h : ∀ i, V' i ⊆ V i) (ζ : BddCochains₁ V) (i j : ι)
    (x : (V' i ∩ V' j : Set M)) :
    ((cochainRestrictL h ζ i j : (V' i ∩ V' j : Set M) →ᵇ ℂ) x) =
      (ζ i j : (V i ∩ V j : Set M) →ᵇ ℂ) (inclusion (inter_subset_inter (h i) (h j)) x) :=
  rfl

namespace DiscCover

variable (𝔇 : DiscCover M ι)

/-- Bounded holomorphic `1`-cocycles on the sets `V i` with values in the line bundle `g`: the
bounded holomorphic `1`-cochains `ζ` with `ζ i k = ζ i j + g i j * ζ j k` on
`V i ∩ V j ∩ V k`. -/
def BddCocycles (g : 𝔇.LineCocycle) (V : ι → Set M) : Submodule ℂ (BddCochains₁ V) where
  carrier := {ζ | ∀ i j k (x : M) (hx : x ∈ V i ∩ V j ∩ V k),
    (ζ i k : (V i ∩ V k : Set M) →ᵇ ℂ) ⟨x, hx.1.1, hx.2⟩ =
      (ζ i j : (V i ∩ V j : Set M) →ᵇ ℂ) ⟨x, hx.1.1, hx.1.2⟩ +
        g i j x * (ζ j k : (V j ∩ V k : Set M) →ᵇ ℂ) ⟨x, hx.1.2, hx.2⟩}
  add_mem' := by
    intro a b ha hb i j k x hx
    simp only [Pi.add_apply, Submodule.coe_add, BoundedContinuousFunction.coe_add,
      ha i j k x hx, hb i j k x hx]
    ring
  zero_mem' := by
    intro i j k x hx
    simp
  smul_mem' := by
    intro c a ha i j k x hx
    simp only [Pi.smul_apply, Submodule.coe_smul, BoundedContinuousFunction.coe_smul,
      ha i j k x hx, smul_eq_mul]
    ring

variable {𝔇} {g : 𝔇.LineCocycle}

theorem mem_bddCocycles {ζ : BddCochains₁ V} :
    ζ ∈ 𝔇.BddCocycles g V ↔ ∀ i j k (x : M) (hx : x ∈ V i ∩ V j ∩ V k),
      (ζ i k : (V i ∩ V k : Set M) →ᵇ ℂ) ⟨x, hx.1.1, hx.2⟩ =
        (ζ i j : (V i ∩ V j : Set M) →ᵇ ℂ) ⟨x, hx.1.1, hx.1.2⟩ +
          g i j x * (ζ j k : (V j ∩ V k : Set M) →ᵇ ℂ) ⟨x, hx.1.2, hx.2⟩ :=
  Iff.rfl

theorem isClosed_bddCocycles (𝔇 : DiscCover M ι) (g : 𝔇.LineCocycle) (V : ι → Set M) :
    IsClosed (𝔇.BddCocycles g V : Set (BddCochains₁ V)) := by
  have hc : ∀ i j (y : (V i ∩ V j : Set M)),
      Continuous fun ζ : BddCochains₁ V => (ζ i j : (V i ∩ V j : Set M) →ᵇ ℂ) y :=
    fun i j y => (continuous_eval_const y).comp
      (continuous_subtype_val.comp ((continuous_apply j).comp (continuous_apply i)))
  change IsClosed {ζ : BddCochains₁ V | ∀ i j k (x : M) (hx : x ∈ V i ∩ V j ∩ V k), _}
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
    isClosed_iInter fun x => isClosed_iInter fun hx =>
      isClosed_eq (hc _ _ _) ((hc _ _ _).add (continuous_const.mul (hc _ _ _)))

variable (g) in
/-- Restriction of bounded cocycles from the sets `V i` to smaller sets `V' i`. -/
def cocycleRestrictL (h : ∀ i, V' i ⊆ V i) : 𝔇.BddCocycles g V →L[ℂ] 𝔇.BddCocycles g V' :=
  ((cochainRestrictL h).comp (𝔇.BddCocycles g V).subtypeL).codRestrict _
    fun ζ i j k x hx => ζ.2 i j k x ⟨⟨h i hx.1.1, h j hx.1.2⟩, h k hx.2⟩

@[simp]
theorem cocycleRestrictL_apply (h : ∀ i, V' i ⊆ V i) (ζ : 𝔇.BddCocycles g V) (i j : ι)
    (x : (V' i ∩ V' j : Set M)) :
    (((𝔇.cocycleRestrictL g h ζ : BddCochains₁ V') i j : (V' i ∩ V' j : Set M) →ᵇ ℂ) x) =
      ((ζ : BddCochains₁ V) i j : (V i ∩ V j : Set M) →ᵇ ℂ)
        (inclusion (inter_subset_inter (h i) (h j)) x) :=
  rfl


/-! ### The coboundary -/

variable {V : ι → Set M}

/-- A transition function of a disc cover is bounded on the overlap of two discs `U`. -/
theorem LineCocycle.exists_bound [T2Space M] (g : 𝔇.LineCocycle) (i j : ι) :
    ∃ C, ∀ x ∈ 𝔇.U i ∩ 𝔇.U j, ‖g i j x‖ ≤ C := by
  set K := (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) (𝔇.r i) ∩
    (𝔇.chart j).symm '' closedBall (𝔇.centreCoord j) (𝔇.r j)
  have hK : IsCompact K := (𝔇.isCompact_symm_image_closedBall i (𝔇.r_lt_ρ i).le).inter_right
    (𝔇.isCompact_symm_image_closedBall j (𝔇.r_lt_ρ j).le).isClosed
  have hKW : K ⊆ 𝔇.W i ∩ 𝔇.W j := inter_subset_inter
    (𝔇.symm_image_closedBall_subset_W i (𝔇.r_lt_ρ i))
    (𝔇.symm_image_closedBall_subset_W j (𝔇.r_lt_ρ j))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((g.mdifferentiableOn i j).continuousOn.mono hKW)
  exact ⟨C, fun x hx => hC x ⟨𝔇.disc_subset_symm_image_closedBall i _ hx.1,
    𝔇.disc_subset_symm_image_closedBall j _ hx.2⟩⟩

/-- The transition function `g i j` as a bounded holomorphic function on `V i ∩ V j`, for sets
`V i ⊆ U i`. -/
def LineCocycle.restrict [T2Space M] (g : 𝔇.LineCocycle) (hV : ∀ i, V i ⊆ 𝔇.U i) (i j : ι) :
    boundedHolomorphic (V i ∩ V j) :=
  boundedHolomorphic.mk (g i j)
    ((g.mdifferentiableOn i j).mono (inter_subset_inter ((hV i).trans (𝔇.U_subset_W i))
      ((hV j).trans (𝔇.U_subset_W j))))
    (by
      obtain ⟨C, hC⟩ := g.exists_bound i j
      exact ⟨C, by
        rintro _ ⟨x, hx, rfl⟩
        exact hC x ⟨hV i hx.1, hV j hx.2⟩⟩)

@[simp]
theorem LineCocycle.restrict_apply [T2Space M] (g : 𝔇.LineCocycle) (hV : ∀ i, V i ⊆ 𝔇.U i)
    (i j : ι) (x : (V i ∩ V j : Set M)) :
    (g.restrict hV i j : (V i ∩ V j : Set M) →ᵇ ℂ) x = g i j x :=
  rfl

variable [T2Space M]

variable (g) in
/-- The coboundary `(δη) i j = η i - g i j * η j` of bounded holomorphic `0`-cochains on sets
`V i ⊆ U i`, a bounded holomorphic `1`-cocycle. -/
def bddCoboundary (hV : ∀ i, V i ⊆ 𝔇.U i) : BddCochains V →L[ℂ] 𝔇.BddCocycles g V :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (boundedHolomorphic.restrictL inter_subset_left).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun i => boundedHolomorphic (V i)) i) -
      (boundedHolomorphic.mulL (g.restrict hV i j)).comp
        ((boundedHolomorphic.restrictL inter_subset_right).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun i => boundedHolomorphic (V i))
            j))).codRestrict _ fun η i j k x hx => by
      have hW : x ∈ 𝔇.W i ∩ 𝔇.W j ∩ 𝔇.W k :=
        ⟨⟨𝔇.U_subset_W i (hV i hx.1.1), 𝔇.U_subset_W j (hV j hx.1.2)⟩,
          𝔇.U_subset_W k (hV k hx.2)⟩
      have h := g.mul_eq i j k x hW
      change (η i : (V i : Set M) →ᵇ ℂ) ⟨x, hx.1.1⟩ -
          g i k x * (η k : (V k : Set M) →ᵇ ℂ) ⟨x, hx.2⟩ =
        ((η i : (V i : Set M) →ᵇ ℂ) ⟨x, hx.1.1⟩ -
          g i j x * (η j : (V j : Set M) →ᵇ ℂ) ⟨x, hx.1.2⟩) +
          g i j x * ((η j : (V j : Set M) →ᵇ ℂ) ⟨x, hx.1.2⟩ -
            g j k x * (η k : (V k : Set M) →ᵇ ℂ) ⟨x, hx.2⟩)
      linear_combination ((η k : (V k : Set M) →ᵇ ℂ) ⟨x, hx.2⟩) * h

@[simp]
theorem bddCoboundary_apply (hV : ∀ i, V i ⊆ 𝔇.U i) (η : BddCochains V) (i j : ι)
    (x : (V i ∩ V j : Set M)) :
    (((𝔇.bddCoboundary g hV η : BddCochains₁ V) i j : (V i ∩ V j : Set M) →ᵇ ℂ) x) =
      (η i : (V i : Set M) →ᵇ ℂ) ⟨x, x.2.1⟩ - g i j x * (η j : (V j : Set M) →ᵇ ℂ) ⟨x, x.2.2⟩ :=
  rfl

end DiscCover

end Cochains

/-! ### Finite dimensionality -/

namespace DiscCover

variable {ι : Type*} (𝔇 : DiscCover M ι)

theorem U''_subset_U (i : ι) : 𝔇.U'' i ⊆ 𝔇.U i := (𝔇.U''_subset_U' i).trans (𝔇.U'_subset_U i)

theorem r''_le_ρ (i : ι) : 𝔇.r'' i ≤ 𝔇.ρ i :=
  ((𝔇.r''_lt_r' i).trans ((𝔇.r'_lt_r i).trans (𝔇.r_lt_ρ i))).le

/-- The closure of the smallest disc `U'' i` lies in the disc `U' i`. -/
theorem closure_U''_subset_U' [T2Space M] (i : ι) : closure (𝔇.U'' i) ⊆ 𝔇.U' i := by
  refine (closure_minimal (𝔇.disc_subset_symm_image_closedBall i _)
    (𝔇.isCompact_symm_image_closedBall i (𝔇.r''_le_ρ i)).isClosed).trans ?_
  rintro _ ⟨z, hz, rfl⟩
  have hzt := 𝔇.closedBall_subset_target' i (𝔇.r''_le_ρ i) hz
  refine ⟨(𝔇.chart i).map_target hzt, ?_⟩
  simp only [mem_preimage, (𝔇.chart i).right_inv hzt]
  exact closedBall_subset_ball (𝔇.r''_lt_r' i) hz

theorem completeSpace_boundedHolomorphic_disc [IsManifold 𝓘(ℂ) 1 M] (i : ι) (s : ℝ) :
    CompleteSpace (boundedHolomorphic (𝔇.disc i s)) :=
  completeSpace_boundedHolomorphic (𝔇.chart i) (𝔇.disc_subset_source i s)
    (chart_mem_atlas ℂ _) (𝔇.isOpen_disc i s)

theorem completeSpace_boundedHolomorphic_disc_inter [IsManifold 𝓘(ℂ) 1 M] (i j : ι)
    (s t : ℝ) : CompleteSpace (boundedHolomorphic (𝔇.disc i s ∩ 𝔇.disc j t)) :=
  completeSpace_boundedHolomorphic (𝔇.chart i) (inter_subset_left.trans (𝔇.disc_subset_source i s))
    (chart_mem_atlas ℂ _) ((𝔇.isOpen_disc i s).inter (𝔇.isOpen_disc j t))

variable [IsManifold 𝓘(ℂ) 1 M] [T2Space M]

/-- Restriction of bounded holomorphic functions from `U' i ∩ U' j` to `U'' i ∩ U'' j` is a
compact operator. -/
theorem isCompactOperator_restrictL_inter (i j : ι) :
    IsCompactOperator (boundedHolomorphic.restrictL
      (inter_subset_inter (𝔇.U''_subset_U' i) (𝔇.U''_subset_U' j))) := by
  set e := 𝔇.chart i
  have hcl1 : closure (e '' (𝔇.U'' i ∩ 𝔇.U'' j)) ⊆ closedBall (𝔇.centreCoord i) (𝔇.r'' i) :=
    closure_minimal (by rintro _ ⟨x, hx, rfl⟩; exact ball_subset_closedBall hx.1.2)
      isClosed_closedBall
  refine boundedHolomorphic.isCompactOperator_restrictL (chart_mem_atlas ℂ _)
    ((𝔇.isOpen_U' i).inter (𝔇.isOpen_U' j)) (inter_subset_left.trans (𝔇.disc_subset_source i _))
    ((𝔇.isOpen_U'' i).inter (𝔇.isOpen_U'' j)) _
    ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl1) ?_
  intro z hz
  have hzt : z ∈ e.target := 𝔇.closedBall_subset_target' i (𝔇.r''_le_ρ i) (hcl1 hz)
  have h1 : e.symm z ∈ closure (𝔇.U'' i ∩ 𝔇.U'' j) := by
    refine closure_mono ?_ ((e.continuousAt_symm hzt).continuousWithinAt.mem_closure_image hz)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [e.left_inv (𝔇.disc_subset_source i _ hx.1)]
    exact hx
  have h2 := closure_inter_subset_inter_closure _ _ h1
  exact ⟨e.symm z, ⟨𝔇.closure_U''_subset_U' i h2.1, 𝔇.closure_U''_subset_U' j h2.2⟩,
    e.right_inv hzt⟩

/-- Restriction of bounded cocycles from the discs `U'` to the smallest discs `U''` is a compact
operator. -/
theorem isCompactOperator_cocycleRestrictL [Finite ι] (g : 𝔇.LineCocycle) :
    IsCompactOperator (𝔇.cocycleRestrictL g 𝔇.U''_subset_U') := by
  have hR : IsCompactOperator (cochainRestrictL (V := 𝔇.U') 𝔇.U''_subset_U') := by
    refine isCompactOperator_pi fun i => isCompactOperator_pi fun j => ?_
    exact (𝔇.isCompactOperator_restrictL_inter i j).comp_clm
      ((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun j => boundedHolomorphic (𝔇.U' i ∩ 𝔇.U' j)) j).comp
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun i => ∀ j, boundedHolomorphic (𝔇.U' i ∩ 𝔇.U' j)) i))
  exact (hR.comp_clm (𝔇.BddCocycles g 𝔇.U').subtypeL).codRestrict _
    (𝔇.isClosed_bddCocycles g _)

/-- **Finite dimensionality of the bounded Čech cohomology of a line bundle.** For a holomorphic
line bundle `g` on a finite disc cover `𝔇` of a Riemann surface, the coboundaries of bounded
holomorphic `0`-cochains on the smallest discs `U''` span, together with a finite-dimensional
subspace, the whole space of bounded holomorphic `1`-cocycles on `U''`. -/
theorem exists_finiteDimensional_sup_range_coboundary [Finite ι] (g : 𝔇.LineCocycle) :
    ∃ F₀ : Submodule ℂ (𝔇.BddCocycles g 𝔇.U''), FiniteDimensional ℂ F₀ ∧
      LinearMap.range ((𝔇.bddCoboundary g 𝔇.U''_subset_U :
        BddCochains 𝔇.U'' →L[ℂ] 𝔇.BddCocycles g 𝔇.U'') :
          BddCochains 𝔇.U'' →ₗ[ℂ] 𝔇.BddCocycles g 𝔇.U'') ⊔ F₀ = ⊤ := by
  cases nonempty_fintype ι
  have : ∀ i j, CompleteSpace (boundedHolomorphic (𝔇.U' i ∩ 𝔇.U' j)) := fun i j =>
    𝔇.completeSpace_boundedHolomorphic_disc_inter i j _ _
  have : ∀ i j, CompleteSpace (boundedHolomorphic (𝔇.U'' i ∩ 𝔇.U'' j)) := fun i j =>
    𝔇.completeSpace_boundedHolomorphic_disc_inter i j _ _
  have : ∀ i, CompleteSpace (boundedHolomorphic (𝔇.U'' i)) := fun i =>
    𝔇.completeSpace_boundedHolomorphic_disc i _
  have : CompleteSpace (𝔇.BddCocycles g 𝔇.U') :=
    IsClosed.completeSpace_coe (hs := 𝔇.isClosed_bddCocycles g _)
  have : CompleteSpace (𝔇.BddCocycles g 𝔇.U'') :=
    IsClosed.completeSpace_coe (hs := 𝔇.isClosed_bddCocycles g _)
  set R := 𝔇.cocycleRestrictL g 𝔇.U''_subset_U'
  set δ := 𝔇.bddCoboundary g 𝔇.U''_subset_U
  set Ψ : (𝔇.BddCocycles g 𝔇.U' × BddCochains 𝔇.U'') →L[ℂ] 𝔇.BddCocycles g 𝔇.U'' :=
    R.comp (ContinuousLinearMap.fst ℂ _ _)
  set Φ : (𝔇.BddCocycles g 𝔇.U' × BddCochains 𝔇.U'') →L[ℂ] 𝔇.BddCocycles g 𝔇.U'' :=
    Ψ + δ.comp (ContinuousLinearMap.snd ℂ _ _)
  have hΨ : IsCompactOperator Ψ := (𝔇.isCompactOperator_cocycleRestrictL g).comp_clm _
  have hΦ : Function.Surjective Φ := by
    intro ζ
    choose F hF hFb hFeq using fun i j =>
      boundedHolomorphic.exists_eq ((ζ : BddCochains₁ 𝔇.U'') i j)
    have hζ : 𝔇.IsCocycleOn g 𝔇.U'' F := by
      refine ⟨hF, fun i j k x hx => ?_⟩
      have h := ζ.2 i j k x hx
      simp only [hFeq] at h
      exact h
    obtain ⟨ξ, η, hξ, hξb, hη, hdec⟩ := 𝔇.exists_decomposition g hζ hFb
    refine ⟨(⟨fun i j => boundedHolomorphic.mk (ξ i j)
        ((hξ.mdifferentiableOn i j).mono
          (inter_subset_inter (𝔇.U'_subset_U i) (𝔇.U'_subset_U j))) (hξb i j),
        fun i j k x hx => hξ.add_eq i j k x
          ⟨⟨𝔇.U'_subset_U i hx.1.1, 𝔇.U'_subset_U j hx.1.2⟩, 𝔇.U'_subset_U k hx.2⟩⟩,
      fun i => boundedHolomorphic.mk (η i) (hη i).1 (hη i).2), ?_⟩
    refine Subtype.ext (funext fun i => funext fun j => Subtype.ext ?_)
    ext x
    rw [hFeq]
    exact (hdec i j x x.2).symm
  obtain ⟨F₀, hF₀, htop⟩ :=
    ContinuousLinearMap.exists_finiteDimensional_range_sub_sup_eq_top Φ Ψ hΦ hΨ
  refine ⟨F₀, hF₀, eq_top_iff.2 (htop.symm.le.trans (sup_le_sup_right ?_ _))⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨x.2, by simp [Φ]⟩

end DiscCover

end RiemannSurface
