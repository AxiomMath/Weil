/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilFrontier.Topology.Covering.BranchedCover
public import WeilFrontier.Analysis.Complex.BrickCover
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.LocallyConvex.WithSeminorms


/-!
# Adapted covers of the Riemann sphere

Let `Y` be presented as the Riemann sphere by two charts `φ₀ φ₁ : ℂ → Y` with `φ₀ w = φ₁ w⁻¹`
(`Weil.RiemannSphereCharts`), let `B ⊆ Y` be finite and let `V₀ b` be a neighbourhood of each
`b : Y`. We write `Y = Y₁ ∪ Y₂` with `Y₁ = φ₀((-R - 1, R + 1)²)` and `Y₂ = φ₁(D)`, where
`D = {0} ∪ {u ≠ 0 | u⁻¹ ∉ [-R, R]²}` and `R` is large, and cover `Y₁`, `Y₂` and `Y₁ ∩ Y₂` by
finite open covers adapted to `B` and `V₀` (`Weil.IsAdaptedCover`):

* `Y₁` by the images of a brick wall of small mesh (`Complex.exists_brick_cover`), of order at
  most `3`; a brick containing a point `b₀` of `φ₀⁻¹ B` is convex, lies in `φ₀⁻¹ V₀ (φ₀ b₀)`
  and is contracted linearly to `b₀`;
* `Y₂` by the single member `φ₁(D)`, star-shaped about `0` in the chart at infinity and
  contracted to `φ₁ 0`;
* `Y₁ ∩ Y₂ = φ₀((-R - 1, R + 1)² ∖ [-R, R]²)` by the images of the four strips of the frame,
  of order at most `2`, all disjoint from `B`.

These are the covers of the base used to show that a compact space branched over the Riemann
sphere has cohomological dimension at most `2`, through the Mayer–Vietoris sequence of
`π⁻¹ Y₁` and `π⁻¹ Y₂`.

## Main definitions

* `Weil.closedSquare R`, `Weil.openSquare R`: the squares `[-R, R]²` and `(-R, R)²` in `ℂ`.
* `Weil.frameStrip R`: the four open strips covering `(-R - 1, R + 1)² ∖ [-R, R]²`.

## Main results

* `Weil.RiemannSphereCharts.exists_adapted_covers`: the open sets `Y₁`, `Y₂` covering `Y` and
  adapted covers of `Y₁`, `Y₂`, `Y₁ ∩ Y₂` of orders at most `3`, `1`, `2`.
* `Weil.isAdaptedCover_image`: a finite family of open subsets of `ℂ` with the properties of an
  adapted cover, read in a chart, maps to an adapted cover of `Y`.
* `Weil.RiemannSphereCharts.locallyPathConnectedSpace`: `Y` is locally path-connected.
* `Convex.reProdIm`: a product `s ×ℂ t` of convex subsets of `ℝ` is convex.
-/

public section

open Set Function Topology unitInterval Metric

/-- A product `s ×ℂ t` of convex subsets of `ℝ` is convex. -/
theorem Convex.reProdIm {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ (s ×ℂ t) := by
  rw [← hs.convexHull_eq, ← ht.convexHull_eq, ← Complex.convexHull_reProdIm]
  exact convex_convexHull ℝ _

namespace Weil

variable {Y : Type*} [TopologicalSpace Y]

namespace RiemannSphereCharts

/-- A space presented as the Riemann sphere is locally path-connected: it is the image of
`ℂ ⊕ ℂ` under the open surjection `Sum.elim φ₀ φ₁`. -/
theorem locallyPathConnectedSpace (c : RiemannSphereCharts Y) : LocallyPathConnectedSpace Y := by
  have hc : Continuous (Sum.elim c.φ₀ c.φ₁) := c.continuous_φ₀.sumElim c.continuous_φ₁
  have ho : IsOpenMap (Sum.elim c.φ₀ c.φ₁) :=
    c.isOpenEmbedding_φ₀.isOpenMap.sumElim c.isOpenEmbedding_φ₁.isOpenMap
  have hs : Surjective (Sum.elim c.φ₀ c.φ₁) := by
    intro y
    have : y ∈ range c.φ₀ ∪ range c.φ₁ := c.range_union ▸ mem_univ y
    rcases this with ⟨z, rfl⟩ | ⟨z, rfl⟩
    exacts [⟨Sum.inl z, rfl⟩, ⟨Sum.inr z, rfl⟩]
  exact (ho.isQuotientMap hc hs).locallyPathConnectedSpace

end RiemannSphereCharts

/-- The image of a star-shaped subset `W` of `ℂ` (about `b₀`) under an embedding `e` is
contracted to `e b₀` by `y ↦ e (t b₀ + (1 - t) e⁻¹ y)`, which reaches `e b₀` only at time `1`
or from `e b₀`. -/
theorem exists_contraction_image {e : ℂ → Y} (he : IsEmbedding e) {W : Set ℂ} {b₀ : ℂ}
    (hW : StarConvex ℝ b₀ W) :
    ∃ h : C(I × (e '' W), e '' W), (∀ y, h (0, y) = y) ∧
      ∀ t y, ((h (t, y) : Y) = e b₀ ↔ (t = 1 ∨ (y : Y) = e b₀)) := by
  let g := he.homeomorphImage W
  have hg : ∀ x, (g x : Y) = e x := fun _ ↦ rfl
  have hg' : ∀ y, e (g.symm y) = y := fun y ↦ by rw [← hg, g.apply_symm_apply]
  let F : C(I × W, W) :=
    { toFun := fun p ↦ ⟨(p.1 : ℝ) • b₀ + (1 - (p.1 : ℝ)) • (p.2 : ℂ),
        hW p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (by ring)⟩
      continuous_toFun := by fun_prop }
  refine ⟨(⟨g, g.continuous⟩ : C(W, e '' W)).comp
    (F.comp ((ContinuousMap.id I).prodMap (⟨g.symm, g.symm.continuous⟩ : C(e '' W, W)))), ?_, ?_⟩
  · intro y
    apply Subtype.ext
    change e (0 • b₀ + (1 - 0 : ℝ) • (g.symm y : ℂ)) = y
    simp [hg']
  · intro t y
    change e ((t : ℝ) • b₀ + (1 - (t : ℝ)) • (g.symm y : ℂ)) = e b₀ ↔ _
    rw [he.injective.eq_iff, ← hg' y, he.injective.eq_iff]
    constructor
    · intro h
      have h' : (1 - (t : ℝ)) • ((g.symm y : ℂ) - b₀) = 0 := by
        rw [smul_sub, sub_eq_zero]
        calc (1 - (t : ℝ)) • (g.symm y : ℂ)
            = (t : ℝ) • b₀ + (1 - (t : ℝ)) • (g.symm y : ℂ) - (t : ℝ) • b₀ := by abel
          _ = (1 - (t : ℝ)) • b₀ := by rw [h, sub_smul, one_smul]
      rcases smul_eq_zero.1 h' with h1 | h1
      · left; ext; simp only [Set.Icc.coe_one]; linarith
      · right; exact sub_eq_zero.1 h1
    · rintro (rfl | h)
      · simp
      · rw [h, ← add_smul]; simp

/-- A finite family of open subsets of `ℂ` with the properties of an adapted cover, read in an
open embedding `e : ℂ → Y` (each member either disjoint from `e⁻¹ B` or star-shaped about its
only point `b₀` of `e⁻¹ B` and contained in `e⁻¹ V₀ (e b₀)`), maps under `e` to an adapted
cover of `Y`. -/
theorem isAdaptedCover_image [LocallyPathConnectedSpace Y] {e : ℂ → Y} (he : IsOpenEmbedding e)
    {B : Set Y} {V₀ : Y → Set Y} {ι : Type} [Fintype ι] {W : ι → Set ℂ} {N : ℕ}
    (hWo : ∀ i, IsOpen (W i))
    (horder : ∀ s : Finset ι, N < s.card → ⋂ i ∈ s, W i = ∅)
    (hcontr : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, W i).Nonempty →
      ContractibleSpace (⋂ i ∈ s, W i))
    (hfb : ∀ i, Disjoint (W i) (e ⁻¹' B) ∨ ∃ b₀ ∈ W i, W i ∩ e ⁻¹' B ⊆ {b₀} ∧
      W i ⊆ e ⁻¹' V₀ (e b₀) ∧ StarConvex ℝ b₀ (W i))
    (hfree : ∀ s : Finset ι, 2 ≤ s.card → (⋂ i ∈ s, W i).Nonempty →
      ∃ i ∈ s, Disjoint (W i) (e ⁻¹' B)) :
    IsAdaptedCover B V₀ (fun i ↦ e '' W i) N where
  isOpen i := he.isOpenMap _ (hWo i)
  order s hs := by
    rw [← he.injective.injOn.image_biInter_eq (Finset.card_pos.1 (by omega)), horder s hs,
      image_empty]
  contractible s hs hne := by
    rw [← he.injective.injOn.image_biInter_eq hs] at hne ⊢
    have := hcontr s hs (image_nonempty.1 hne)
    exact (he.isEmbedding.homeomorphImage _).symm.contractibleSpace
  locallyPathConnected s :=
    (isOpen_biInter_finset fun i _ ↦ he.isOpenMap _ (hWo i)).locallyPathConnectedSpace
  free_or_branch i := by
    rcases hfb i with h | ⟨b₀, hb₀, hB, hV, hst⟩
    · exact Or.inl (disjoint_image_left.2 h)
    · refine Or.inr ⟨e b₀, mem_image_of_mem e hb₀, ?_, image_subset_iff.2 hV,
        exists_contraction_image he.isEmbedding hst⟩
      rintro _ ⟨⟨x, hx, rfl⟩, hxB⟩
      rw [hB ⟨hx, hxB⟩]
      rfl
  free_of_two s hs hne := by
    rw [← he.injective.injOn.image_biInter_eq (Finset.card_pos.1 (by omega))] at hne
    obtain ⟨i, hi, h⟩ := hfree s hs (image_nonempty.1 hne)
    exact ⟨i, hi, disjoint_image_left.2 h⟩

/-- A single open star-shaped set in a chart, meeting `e⁻¹ B` at most in its centre `b₀` and
contained in `e⁻¹ V₀ (e b₀)`, is an adapted cover of order at most `1`. -/
theorem isAdaptedCover_single [LocallyPathConnectedSpace Y] {e : ℂ → Y} (he : IsOpenEmbedding e)
    {B : Set Y} {V₀ : Y → Set Y} {W : Set ℂ} {b₀ : ℂ} (hWo : IsOpen W) (hb₀ : b₀ ∈ W)
    (hst : StarConvex ℝ b₀ W) (hB : W ∩ e ⁻¹' B ⊆ {b₀}) (hV : W ⊆ e ⁻¹' V₀ (e b₀)) :
    IsAdaptedCover B V₀ (fun _ : Unit ↦ e '' W) 1 := by
  have hcard : ∀ s : Finset Unit, s.card ≤ 1 := fun s ↦ by
    simpa using Finset.card_le_univ s
  refine isAdaptedCover_image he (fun _ ↦ hWo) (fun s hs ↦ absurd (hcard s) (by omega))
    (fun s hs _ ↦ ?_) (fun _ ↦ Or.inr ⟨b₀, hb₀, hB, hV, hst⟩)
    (fun s hs _ ↦ absurd (hcard s) (by omega))
  obtain rfl : s = {()} := Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hs, fun _ _ ↦ rfl⟩
  rw [Finset.set_biInter_singleton]
  exact hst.contractibleSpace ⟨b₀, hb₀⟩

/-- The closed square `[-R, R] ×ℂ [-R, R]`. -/
abbrev closedSquare (R : ℝ) : Set ℂ := Icc (-R) R ×ℂ Icc (-R) R

/-- The open square `(-R, R) ×ℂ (-R, R)`. -/
abbrev openSquare (R : ℝ) : Set ℂ := Ioo (-R) R ×ℂ Ioo (-R) R

/-- The four strips of the frame `openSquare (R + 1) \ closedSquare R`. -/
def frameStrip (R : ℝ) : Fin 4 → Set ℂ :=
  ![Ioo (-(R + 1)) (R + 1) ×ℂ Ioo R (R + 1), Ioo (-(R + 1)) (R + 1) ×ℂ Ioo (-(R + 1)) (-R),
    Ioo (-(R + 1)) (-R) ×ℂ Ioo (-(R + 1)) (R + 1), Ioo R (R + 1) ×ℂ Ioo (-(R + 1)) (R + 1)]

/-- The four strips cover the frame `(-R - 1, R + 1)² ∖ [-R, R]²`. -/
theorem iUnion_frameStrip (R : ℝ) (hR : 0 < R) :
    ⋃ i, frameStrip R i = openSquare (R + 1) \ closedSquare R := by
  ext z
  simp only [frameStrip, neg_add_rev, mem_iUnion, Fin.exists_fin_succ, Fin.isValue,
    Matrix.cons_val_zero, Complex.mem_reProdIm, mem_Ioo, add_neg_lt_iff_lt_add,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, exists_const, mem_sdiff, mem_Icc, not_and,
    not_le, and_imp]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) <;>
      exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, fun _ _ _ ↦ by linarith⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    rcases lt_or_ge z.re (-R) with a | a
    · exact Or.inr (Or.inr (Or.inl ⟨⟨h1, a⟩, h3, h4⟩))
    rcases lt_or_ge R z.re with b | b
    · exact Or.inr (Or.inr (Or.inr ⟨⟨b, h2⟩, h3, h4⟩))
    rcases lt_or_ge z.im (-R) with c | c
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, h3, c⟩)
    exact Or.inl ⟨⟨h1, h2⟩, h a b c, h4⟩

/-- The top and bottom strips are disjoint. -/
theorem frameStrip_zero_inter_one (R : ℝ) (hR : 0 < R) :
    frameStrip R 0 ∩ frameStrip R 1 = ∅ := by
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro h
  simp [frameStrip] at h
  linarith [h.1.2.1, h.2.2.2]

/-- The left and right strips are disjoint. -/
theorem frameStrip_two_inter_three (R : ℝ) (hR : 0 < R) :
    frameStrip R 2 ∩ frameStrip R 3 = ∅ := by
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro h
  simp [frameStrip] at h
  linarith [h.1.1.2, h.2.1.1]

/-- Each strip of the frame is convex. -/
theorem convex_frameStrip (R : ℝ) (i : Fin 4) : Convex ℝ (frameStrip R i) := by
  fin_cases i <;> exact Convex.reProdIm (convex_Ioo _ _) (convex_Ioo _ _)

/-- Each strip of the frame is open. -/
theorem isOpen_frameStrip (R : ℝ) (i : Fin 4) : IsOpen (frameStrip R i) := by
  fin_cases i <;> exact isOpen_Ioo.reProdIm isOpen_Ioo

/-- The images of the four strips of the frame under an open embedding `e` form an adapted
cover of order at most `2` (no three strips meet), all of whose members are free when
`e⁻¹ B ⊆ [-R, R]²`. -/
theorem isAdaptedCover_frameStrip [LocallyPathConnectedSpace Y] {e : ℂ → Y}
    (he : IsOpenEmbedding e) {B : Set Y} (V₀ : Y → Set Y) {R : ℝ} (hR : 0 < R)
    (hB : e ⁻¹' B ⊆ closedSquare R) :
    IsAdaptedCover B V₀ (fun i ↦ e '' frameStrip R i) 2 := by
  have hfree : ∀ i, Disjoint (frameStrip R i) (e ⁻¹' B) := fun i ↦ by
    refine Disjoint.mono_right hB (disjoint_left.2 fun z hz hzQ ↦ ?_)
    have : z ∈ ⋃ i, frameStrip R i := mem_iUnion.2 ⟨i, hz⟩
    rw [iUnion_frameStrip R hR] at this
    exact this.2 hzQ
  have hpair : ∀ s : Finset (Fin 4), 2 < s.card → (0 ∈ s ∧ 1 ∈ s) ∨ (2 ∈ s ∧ 3 ∈ s) := by
    decide
  refine isAdaptedCover_image he (isOpen_frameStrip R) (fun s hs ↦ ?_) (fun s _ hne ↦ ?_)
    (fun i ↦ Or.inl (hfree i)) (fun s hs _ ↦ ?_)
  · rw [eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_iInter₂] at hz
    rcases hpair s hs with ⟨h0, h1⟩ | ⟨h2, h3⟩
    · rw [← mem_empty_iff_false z, ← frameStrip_zero_inter_one R hR]
      exact ⟨hz 0 h0, hz 1 h1⟩
    · rw [← mem_empty_iff_false z, ← frameStrip_two_inter_three R hR]
      exact ⟨hz 2 h2, hz 3 h3⟩
  · exact (convex_iInter₂ fun i _ ↦ convex_frameStrip R i).contractibleSpace hne
  · obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < s.card)
    exact ⟨i, hi, hfree i⟩

/-- The image of the open square `(-R, R)²` under an open embedding `e` has an adapted cover
of order at most `3`: the images of the bricks of a brick wall whose mesh is small against the
neighbourhoods `V₀ (e b₀)` of the finitely many points `b₀` of `e⁻¹ B`. -/
theorem exists_isAdaptedCover_openSquare [LocallyPathConnectedSpace Y] {e : ℂ → Y}
    (he : IsOpenEmbedding e) {B : Set Y} (hB : (e ⁻¹' B).Finite) (V₀ : Y → Set Y)
    (hV₀ : ∀ b ∈ B, V₀ b ∈ 𝓝 b) (R : ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (V : ι → Set Y), IsAdaptedCover B V₀ V 3 ∧
      (⋃ i, V i) = e '' openSquare R := by
  -- a radius `ρ` such that the `ρ`-ball around each point of `e⁻¹ B` lies in its `V₀`
  obtain ⟨ρ, hρV, hρ⟩ : ∃ ρ : ℝ, (∀ z ∈ hB.toFinset, ball z ρ ⊆ e ⁻¹' V₀ (e z)) ∧ 0 < ρ := by
    have : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ z ∈ hB.toFinset, ball z ρ ⊆ e ⁻¹' V₀ (e z) := by
      rw [Filter.eventually_all_finset]
      intro z hz
      rw [Finite.mem_toFinset] at hz
      obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1
        (he.continuous.continuousAt.preimage_mem_nhds (hV₀ _ hz))
      filter_upwards [Ioc_mem_nhdsGT hη] with ρ hρ'
      exact (ball_subset_ball hρ'.2).trans hηV
    exact (this.and self_mem_nhdsWithin).exists
  obtain ⟨ι, _, V, hrect, hunion, horder, hdiam, -, hsub, hdisj⟩ :=
    Complex.exists_brick_cover hB.toFinset R ρ hρ
  have hconv : ∀ i, Convex ℝ (V i) := fun i ↦ by
    obtain ⟨a, b, c, d, h⟩ := hrect i
    rw [h]
    exact ((convex_Ioo a b).reProdIm (convex_Ioo c d)).inter
      ((convex_Ioo _ _).reProdIm (convex_Ioo _ _))
  have hopen : ∀ i, IsOpen (V i) := fun i ↦ by
    obtain ⟨a, b, c, d, h⟩ := hrect i
    rw [h]
    exact (isOpen_Ioo.reProdIm isOpen_Ioo).inter (isOpen_Ioo.reProdIm isOpen_Ioo)
  have hcoe : ((hB.toFinset : Set ℂ)) = e ⁻¹' B := hB.coe_toFinset
  have hfree : ∀ i, ¬ (V i ∩ hB.toFinset).Nonempty → Disjoint (V i) (e ⁻¹' B) := fun i h ↦ by
    rw [← hcoe]
    exact disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)
  refine ⟨ι, inferInstance, fun i ↦ e '' V i,
    isAdaptedCover_image he hopen horder (fun s _ hne ↦ ?_) (fun i ↦ ?_) (fun s hs hne ↦ ?_),
    by rw [← image_iUnion, hunion]⟩
  · exact (convex_iInter₂ fun i _ ↦ hconv i).contractibleSpace hne
  · by_cases h : (V i ∩ hB.toFinset).Nonempty
    · obtain ⟨b₀, hbV, hbB⟩ := h
      refine Or.inr ⟨b₀, hbV, fun z hz ↦ hsub i ⟨hz.1, hcoe.symm ▸ hz.2⟩ ⟨hbV, hbB⟩, fun z hz ↦ ?_,
        (hconv i).starConvex hbV⟩
      have hbdd : Bornology.IsBounded (V i) :=
        (Metric.isBounded_Ioo (-R) R).reProdIm (Metric.isBounded_Ioo (-R) R) |>.subset
          (hunion ▸ subset_iUnion V i)
      exact hρV b₀ hbB (mem_ball.2 ((dist_le_diam_of_mem hbdd hz hbV).trans_lt (hdiam i)))
    · exact Or.inl (hfree i h)
  · obtain ⟨z, hz⟩ := hne
    rw [mem_iInter₂] at hz
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
    by_cases hi' : (V i ∩ hB.toFinset).Nonempty
    · by_cases hj' : (V j ∩ hB.toFinset).Nonempty
      · exact absurd (hdisj i j hij hi' hj') (not_disjoint_iff.2 ⟨z, hz i hi, hz j hj⟩)
      · exact ⟨j, hj, hfree j hj'⟩
    · exact ⟨i, hi, hfree i hi'⟩

/-- **Adapted covers of the Riemann sphere.** For a finite `B ⊆ Y` and neighbourhoods `V₀ b`
of the points of `Y`, there are open sets `Y₁`, `Y₂` covering `Y` and adapted covers of `Y₁`,
`Y₂` and `Y₁ ∩ Y₂` of orders at most `3`, `1` and `2`. -/
theorem RiemannSphereCharts.exists_adapted_covers (c : RiemannSphereCharts Y) {B : Set Y}
    (hB : B.Finite) (V₀ : Y → Set Y) (hV₀ : ∀ b, V₀ b ∈ 𝓝 b) :
    ∃ Y₁ Y₂ : Set Y, IsOpen Y₁ ∧ IsOpen Y₂ ∧ Y₁ ∪ Y₂ = univ ∧
      (∃ (ι : Type) (_ : Fintype ι) (V : ι → Set Y), IsAdaptedCover B V₀ V 3 ∧
        (⋃ i, V i) = Y₁) ∧
      (∃ (ι : Type) (_ : Fintype ι) (V : ι → Set Y), IsAdaptedCover B V₀ V 1 ∧
        (⋃ i, V i) = Y₂) ∧
      (∃ (ι : Type) (_ : Fintype ι) (V : ι → Set Y), IsAdaptedCover B V₀ V 2 ∧
        (⋃ i, V i) = Y₁ ∩ Y₂) := by
  have := c.locallyPathConnectedSpace
  have hB₀ : (c.φ₀ ⁻¹' B).Finite := hB.preimage c.injective_φ₀.injOn
  -- a ball around `0` mapped by `φ₁` into the neighbourhood `V₀` of the point at infinity
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1
    (c.continuous_φ₁.continuousAt.preimage_mem_nhds (hV₀ (c.φ₁ 0)))
  -- the half-side `R`: the square `[-R, R]²` contains `φ₀⁻¹ B`, and `1 / R ≤ η`
  obtain ⟨R, hR, hRη, hRB⟩ : ∃ R : ℝ, 0 < R ∧ 1 / R ≤ η ∧ c.φ₀ ⁻¹' B ⊆ closedSquare R := by
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall 0).1 hB₀.isBounded
    have h1η : 0 < 1 / η := by positivity
    refine ⟨max r (1 / η) + 1, by positivity, ?_, fun z hz ↦ ?_⟩
    · rw [one_div_le (by positivity) hη]
      linarith [le_max_right r (1 / η)]
    · have hz' : ‖z‖ ≤ r := by simpa using hr hz
      have hre := abs_le.1 ((Complex.abs_re_le_norm z).trans hz')
      have him := abs_le.1 ((Complex.abs_im_le_norm z).trans hz')
      have := le_max_left r (1 / η)
      simp only [closedSquare, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hQ0 : (0 : ℂ) ∈ closedSquare R := by
    simp only [closedSquare, Complex.mem_reProdIm, mem_Icc, Complex.zero_re, Complex.zero_im]
    exact ⟨⟨by linarith, hR.le⟩, by linarith, hR.le⟩
  have hQstar : StarConvex ℝ 0 (closedSquare R) :=
    ((convex_Icc _ _).reProdIm (convex_Icc _ _)).starConvex hQ0
  have hQclosed : IsClosed (closedSquare R) := isClosed_Icc.reProdIm isClosed_Icc
  have hQS : closedSquare R ⊆ openSquare (R + 1) := fun z hz ↦ by
    simp only [closedSquare, openSquare, Complex.mem_reProdIm, mem_Icc, mem_Ioo] at hz ⊢
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- the neighbourhood `D` of `0` in the chart at infinity
  set D : Set ℂ := {u | u = 0 ∨ u⁻¹ ∉ closedSquare R} with hD
  have hD0 : (0 : ℂ) ∈ D := Or.inl rfl
  have hDsmall : ∀ u ∈ D, ‖u‖ < 1 / R := by
    rintro u (rfl | hu)
    · simpa using hR
    · by_contra h
      push Not at h
      have hu0 : 0 < ‖u‖ := (one_div_pos.2 hR).trans_le h
      have h' : ‖u⁻¹‖ ≤ R := by
        rw [norm_inv]
        simpa using inv_anti₀ (one_div_pos.2 hR) h
      have hre := abs_le.1 ((Complex.abs_re_le_norm u⁻¹).trans h')
      have him := abs_le.1 ((Complex.abs_im_le_norm u⁻¹).trans h')
      exact hu ⟨hre, him⟩
  have hDopen : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    rintro u (rfl | hu)
    · refine Filter.mem_of_superset (ball_mem_nhds 0 (by positivity : (0 : ℝ) < (2 * R)⁻¹))
        fun v hv ↦ ?_
      by_cases hv0 : v = 0
      · exact Or.inl hv0
      refine Or.inr fun hQ ↦ ?_
      have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have h1 : 2 * R < ‖v⁻¹‖ := by
        rw [norm_inv]
        exact (lt_inv_comm₀ hpos (by positivity)).1 (by simpa using hv)
      have h2 := Complex.norm_le_abs_re_add_abs_im v⁻¹
      have hre := abs_le.2 hQ.1
      have him := abs_le.2 hQ.2
      linarith
    · have hu0 : u ≠ 0 := by rintro rfl; exact hu (by simpa using hQ0)
      exact Filter.mem_of_superset ((continuousAt_inv₀ hu0).preimage_mem_nhds
        (hQclosed.isOpen_compl.mem_nhds hu)) fun v hv ↦ Or.inr hv
  have hDstar : StarConvex ℝ 0 D := by
    intro y hy a b _ hb hab
    rw [smul_zero, zero_add]
    by_cases hb0 : b = 0
    · exact Or.inl (by rw [hb0, zero_smul])
    by_cases hy0 : y = 0
    · exact Or.inl (by rw [hy0, smul_zero])
    refine Or.inr fun hmem ↦ (hy.resolve_left hy0) ?_
    have := hQstar.smul_mem hmem hb (by linarith : b ≤ 1)
    have e : b • (b • y)⁻¹ = y⁻¹ := by
      rw [Complex.real_smul, Complex.real_smul, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (by exact_mod_cast hb0), one_mul]
    rwa [e] at this
  have hDB : D ∩ c.φ₁ ⁻¹' B ⊆ {0} := by
    rintro u ⟨hu, huB⟩
    by_contra hu0
    have hu0' : u ≠ 0 := hu0
    have : u⁻¹ ∈ c.φ₀ ⁻¹' B := by
      rw [mem_preimage, ← c.transition' u hu0']
      exact huB
    exact (hu.resolve_left hu0') (hRB this)
  have hDV : D ⊆ c.φ₁ ⁻¹' V₀ (c.φ₁ 0) := fun u hu ↦
    hηV (ball_subset_ball hRη (mem_ball_zero_iff.2 (hDsmall u hu)))
  have hinter : c.φ₀ '' openSquare (R + 1) ∩ c.φ₁ '' D =
      c.φ₀ '' (openSquare (R + 1) \ closedSquare R) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, u, hu, hzu⟩
      have hu0 : u ≠ 0 := by
        rintro rfl
        exact c.φ₁_zero_notMem ⟨z, hzu.symm⟩
      rw [c.transition' u hu0] at hzu
      obtain rfl := c.injective_φ₀ hzu
      exact ⟨u⁻¹, ⟨hz, hu.resolve_left hu0⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzQ⟩, rfl⟩
      have hz0 : z ≠ 0 := by rintro rfl; exact hzQ hQ0
      exact ⟨⟨z, hz, rfl⟩, z⁻¹, Or.inr (by rwa [inv_inv]), (c.transition z hz0).symm⟩
  refine ⟨c.φ₀ '' openSquare (R + 1), c.φ₁ '' D,
    c.isOpenEmbedding_φ₀.isOpenMap _ (isOpen_Ioo.reProdIm isOpen_Ioo),
    c.isOpenEmbedding_φ₁.isOpenMap _ hDopen, ?_,
    exists_isAdaptedCover_openSquare c.isOpenEmbedding_φ₀ hB₀ V₀ (fun b _ ↦ hV₀ b) (R + 1),
    ⟨Unit, inferInstance, _, isAdaptedCover_single c.isOpenEmbedding_φ₁ hDopen hD0 hDstar hDB hDV,
      iUnion_const _⟩,
    ⟨Fin 4, inferInstance, _, isAdaptedCover_frameStrip c.isOpenEmbedding_φ₀ V₀ hR hRB,
      by rw [← image_iUnion, iUnion_frameStrip R hR, hinter]⟩⟩
  refine eq_univ_of_forall fun y ↦ ?_
  rcases c.mem_range_φ₀_or_eq y with ⟨z, rfl⟩ | rfl
  · by_cases hz : z ∈ openSquare (R + 1)
    · exact Or.inl ⟨z, hz, rfl⟩
    · have hz0 : z ≠ 0 := by rintro rfl; exact hz (hQS hQ0)
      refine Or.inr ⟨z⁻¹, Or.inr ?_, (c.transition z hz0).symm⟩
      rw [inv_inv]
      exact fun h ↦ hz (hQS h)
  · exact Or.inr ⟨0, hD0, rfl⟩

end Weil
