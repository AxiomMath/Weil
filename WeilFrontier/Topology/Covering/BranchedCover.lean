/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Finite branched covers

A continuous map `π : X → Y` with finite fibres is a *finite branched cover with branch locus
contained in `B`* if it is a local homeomorphism at every point of `π⁻¹(Y ∖ B)`. When `X` is
compact and both spaces are Hausdorff, `π` is then a covering map over `Y ∖ B`. Over an open
subset `V ⊆ Y ∖ B` that is simply connected and locally path-connected (for instance a convex
open subset of a chart), the preimage `π⁻¹ V` is a finite disjoint union of open sheets, each
mapped homeomorphically onto `V`: the sheets are the images of the lifts of the inclusion
`V ↪ Y` through the covering map.

This file also introduces the two pieces of data used to build finite open covers of a
compact space branched over the Riemann sphere whose finite intersections are contractible:
a pair of charts presenting a space as the Riemann sphere, and finite open covers of the base
adapted to the branch locus.

## Main definitions

* `Weil.IsBranchedCover π B`: `π` is continuous with finite fibres and a local homeomorphism
  at every point of `π⁻¹ Bᶜ`.
* `Weil.RiemannSphereCharts Y`: two open embeddings `φ₀ φ₁ : ℂ → Y` whose ranges cover `Y`,
  with `φ₁ 0` outside the range of `φ₀` and transition `φ₀ w = φ₁ w⁻¹` for `w ≠ 0`.
* `Weil.IsAdaptedCover B V₀ V N`: a finite family of open subsets of `Y` of order at most `N`
  (no `N + 1` distinct members meet) whose nonempty finite intersections are contractible and
  locally path-connected, each member either disjoint from `B` or a contractible neighbourhood
  of a single point `b` of `B` inside `V₀ b`, contracted to `b` by a homotopy reaching `b`
  only at time `1`, and every nonempty intersection of two or more members containing a member
  disjoint from `B`.

## Main results

* `Weil.IsBranchedCover.isCoveringMapOn`: for `X` compact Hausdorff and `Y` Hausdorff, a
  branched cover over `B` is a covering map over `Bᶜ`.
* `Weil.IsBranchedCover.exists_sheets`: over an open, simply connected, locally path-connected
  `V` disjoint from `B`, the preimage `π⁻¹ V` is a finite disjoint union of open sets, each
  mapped injectively onto `V`.

## Implementation notes

The sheets are indexed by `Fin n` with `n` the cardinality of a fibre over a point of `V`, so
that the index type lives in `Type` whatever the universe of `X`. The hypotheses on `V` are
simple connectivity and local path-connectedness, which is what the lifting criterion needs;
a contractible `V` is simply connected by `SimplyConnectedSpace.ofContractible`.
-/

@[expose] public section

open Set Function Topology unitInterval

namespace Weil

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `π : X → Y` is a finite branched cover with branch locus contained in `B`: it is
continuous, its fibres are finite, and it is a local homeomorphism at every point of
`π⁻¹ Bᶜ`. -/
structure IsBranchedCover (π : X → Y) (B : Set Y) : Prop where
  continuous : Continuous π
  finite_fiber : ∀ y, (π ⁻¹' {y}).Finite
  isLocalHomeomorphOn : IsLocalHomeomorphOn π (π ⁻¹' Bᶜ)

namespace IsBranchedCover

variable {π : X → Y} {B : Set Y}

/-- Enlarging the branch locus preserves being a branched cover. -/
theorem mono (h : IsBranchedCover π B) {B' : Set Y} (hBB' : B ⊆ B') : IsBranchedCover π B' where
  continuous := h.continuous
  finite_fiber := h.finite_fiber
  isLocalHomeomorphOn := h.isLocalHomeomorphOn.mono
    (preimage_mono (compl_subset_compl.mpr hBB'))

/-- A local homeomorphism with finite fibres is a branched cover with empty branch locus. -/
theorem of_isLocalHomeomorph (h : IsLocalHomeomorph π) (hfin : ∀ y, (π ⁻¹' {y}).Finite) :
    IsBranchedCover π ∅ where
  continuous := h.continuous
  finite_fiber := hfin
  isLocalHomeomorphOn := fun x _ ↦ (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp h) x
    (mem_univ x)

/-- A branched cover from a compact Hausdorff space to a Hausdorff space is a closed map. -/
theorem isClosedMap [CompactSpace X] [T2Space Y] (h : IsBranchedCover π B) : IsClosedMap π :=
  h.continuous.isClosedMap

/-- A branched cover of a Hausdorff space by a compact Hausdorff space is a covering map off
the branch locus. -/
theorem isCoveringMapOn [CompactSpace X] [T2Space X] [T2Space Y] (h : IsBranchedCover π B) :
    IsCoveringMapOn π Bᶜ :=
  IsCoveringMapOn.of_isLocalHomeomorphOn h.continuous h.isLocalHomeomorphOn

/-- Over an open simply connected, locally path-connected subset `V` disjoint from the branch
locus, the preimage of `V` under a branched cover is a finite disjoint union of open sheets,
each mapped injectively onto `V`. -/
theorem exists_sheets [CompactSpace X] [T2Space X] [T2Space Y] (hπ : IsBranchedCover π B)
    {V : Set Y} (hV : IsOpen V) (hVB : Disjoint V B) [SimplyConnectedSpace V]
    [LocallyPathConnectedSpace V] :
    ∃ (ι : Type) (_ : Finite ι) (s : ι → Set X), (∀ i, IsOpen (s i)) ∧
      Pairwise (Disjoint on s) ∧ (⋃ i, s i) = π ⁻¹' V ∧ ∀ i, InjOn π (s i) ∧ π '' s i = V := by
  -- the restriction `g : π⁻¹ V → V` is a covering map
  have hcovV : IsCoveringMapOn π V := fun y hy ↦
    hπ.isCoveringMapOn y (disjoint_left.mp hVB hy)
  set g : π ⁻¹' V → V := V.restrictPreimage π
  have hg : IsCoveringMap g := hcovV.isCoveringMap_restrictPreimage
  have hgval : ∀ x : π ⁻¹' V, ((g x : V) : Y) = π x := fun _ ↦ rfl
  have hopen : IsOpen (π ⁻¹' V) := hV.preimage hπ.continuous
  -- a base point and its (finite) fibre
  obtain ⟨y₀⟩ : Nonempty V := inferInstance
  let F : Set (π ⁻¹' V) := g ⁻¹' {y₀}
  have hFfin : F.Finite := by
    refine Finite.of_finite_image ?_ Subtype.val_injective.injOn
    refine (hπ.finite_fiber y₀).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hx ⊢
    rw [← hgval, hx]
  have : Finite F := hFfin.to_subtype
  -- the lift of the identity of `V` through the point `e` of the fibre
  have hlift : ∀ (v : V) (e : π ⁻¹' V), g e = v →
      ∃! L : C(V, π ⁻¹' V), L v = e ∧ g ∘ L = ContinuousMap.id V := fun v e he ↦
    hg.existsUnique_continuousMap_lifts (ContinuousMap.id V) v e he
  choose lft hlft₀ hlft using fun e : F ↦ (hlift y₀ e e.2).exists
  -- uniqueness of lifts agreeing at one point
  have huniq : ∀ L L' : C(V, π ⁻¹' V), g ∘ L = id → g ∘ L' = id → ∀ v, L v = L' v → L = L' := by
    intro L L' hL hL' v hv
    exact DFunLike.coe_injective
      (hg.eq_of_comp_eq L.continuous L'.continuous (hL.trans hL'.symm) v hv)
  have hlftid : ∀ e, g ∘ lft e = id := fun e ↦ hlft e
  have hlftapp : ∀ e v, π (lft e v : X) = v := fun e v ↦ by
    rw [← hgval]; exact congrArg Subtype.val (congrFun (hlftid e) v)
  -- each lift is an open embedding into `X`
  have hlftemb : ∀ e, IsOpenEmbedding (Subtype.val ∘ lft e) := fun e ↦
    hopen.isOpenEmbedding_subtypeVal.comp
      (hg.isLocalHomeomorph.isOpenEmbedding_of_comp (by rw [hlftid e]; exact .id)
        (lft e).continuous)
  let eqv : F ≃ Fin (Nat.card F) := Finite.equivFin F
  refine ⟨Fin (Nat.card F), inferInstance, fun i ↦ range (Subtype.val ∘ lft (eqv.symm i)),
    fun i ↦ (hlftemb _).isOpen_range, ?_, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · -- disjointness
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro _ ⟨v, rfl⟩ ⟨w, hw⟩
    apply hij
    have hvw : w = v := Subtype.ext (by
      rw [← hlftapp (eqv.symm j) w, ← hlftapp (eqv.symm i) v]; exact congrArg π hw)
    subst hvw
    have hL := huniq _ _ (hlftid _) (hlftid _) w (Subtype.ext hw)
    have := congrArg (fun L : C(V, π ⁻¹' V) ↦ L y₀) hL
    simp only [hlft₀] at this
    exact eqv.symm.injective (Subtype.ext this.symm)
  · -- the sheets cover `π⁻¹ V`
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨i, rfl⟩, ⟨v, rfl⟩⟩
      exact (lft (eqv.symm i) v).2
    · intro x hx
      obtain ⟨L, ⟨hLv, hL⟩, -⟩ := hlift (g ⟨x, hx⟩) ⟨x, hx⟩ rfl
      have hLy : L y₀ ∈ F := by
        exact congrFun hL y₀
      have hLlft : L = lft ⟨L y₀, hLy⟩ :=
        huniq _ _ hL (hlftid _) y₀ (hlft₀ ⟨L y₀, hLy⟩).symm
      refine mem_iUnion.mpr ⟨eqv ⟨L y₀, hLy⟩, g ⟨x, hx⟩, ?_⟩
      simp only [Equiv.symm_apply_apply, comp_apply, ← hLlft, hLv]
  · -- injectivity of `π` on a sheet
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ hvw
    simp only [comp_apply, hlftapp] at hvw
    rw [Subtype.ext hvw]
  · -- each sheet maps onto `V`
    rw [← range_comp]
    have : π ∘ Subtype.val ∘ lft (eqv.symm i) = Subtype.val := funext (hlftapp _)
    rw [this, Subtype.range_coe]

end IsBranchedCover

/-- Two charts presenting `Y` as the Riemann sphere: open embeddings `φ₀ φ₁ : ℂ → Y` whose
ranges cover `Y`, such that `φ₁ 0` (the point at infinity of `φ₀`) is not in the range of
`φ₀`, with transition map `w ↦ w⁻¹` on `ℂ ∖ {0}`. -/
structure RiemannSphereCharts (Y : Type*) [TopologicalSpace Y] where
  /-- The chart around `0`. -/
  φ₀ : ℂ → Y
  /-- The chart around `∞`. -/
  φ₁ : ℂ → Y
  isOpenEmbedding_φ₀ : IsOpenEmbedding φ₀
  isOpenEmbedding_φ₁ : IsOpenEmbedding φ₁
  range_union : range φ₀ ∪ range φ₁ = univ
  φ₁_zero_notMem : φ₁ 0 ∉ range φ₀
  transition : ∀ w : ℂ, w ≠ 0 → φ₀ w = φ₁ w⁻¹

namespace RiemannSphereCharts

variable (c : RiemannSphereCharts Y)

theorem continuous_φ₀ : Continuous c.φ₀ := c.isOpenEmbedding_φ₀.continuous

theorem continuous_φ₁ : Continuous c.φ₁ := c.isOpenEmbedding_φ₁.continuous

theorem injective_φ₀ : Injective c.φ₀ := c.isOpenEmbedding_φ₀.injective

theorem injective_φ₁ : Injective c.φ₁ := c.isOpenEmbedding_φ₁.injective

theorem isOpen_range_φ₀ : IsOpen (range c.φ₀) := c.isOpenEmbedding_φ₀.isOpen_range

theorem isOpen_range_φ₁ : IsOpen (range c.φ₁) := c.isOpenEmbedding_φ₁.isOpen_range

/-- The transition map in the other direction: `φ₁ u = φ₀ u⁻¹` for `u ≠ 0`. -/
theorem transition' (u : ℂ) (hu : u ≠ 0) : c.φ₁ u = c.φ₀ u⁻¹ := by
  rw [c.transition u⁻¹ (inv_ne_zero hu), inv_inv]

/-- The range of `φ₀` is the complement of the point `φ₁ 0`. -/
theorem range_φ₀ : range c.φ₀ = {c.φ₁ 0}ᶜ := by
  ext y
  simp only [mem_compl_iff, mem_singleton_iff]
  refine ⟨fun hy h ↦ c.φ₁_zero_notMem (h ▸ hy), fun hy ↦ ?_⟩
  have : y ∈ range c.φ₀ ∪ range c.φ₁ := c.range_union ▸ mem_univ y
  rcases this with h | ⟨u, rfl⟩
  · exact h
  · have hu : u ≠ 0 := by rintro rfl; exact hy rfl
    exact ⟨u⁻¹, (c.transition' u hu).symm⟩

/-- Every point is either in the range of `φ₀` or the point `φ₁ 0`. -/
theorem mem_range_φ₀_or_eq (y : Y) : y ∈ range c.φ₀ ∨ y = c.φ₁ 0 := by
  rw [range_φ₀]
  exact (em (y = c.φ₁ 0)).symm

end RiemannSphereCharts

/-- A finite open cover `V` of part of `Y`, adapted to a branch locus `B` and to branch
neighbourhoods `V₀ b`, of order at most `N`: no `N + 1` distinct members meet; every nonempty
finite intersection is contractible and locally path-connected; each member is either disjoint
from `B` (a *free* member) or contains exactly one point `b` of `B`, lies in `V₀ b` and is
contracted to `b` by a homotopy that reaches `b` only at time `1` or from `b` (a *branch*
member); and every nonempty intersection of at least two members contains a free member. -/
structure IsAdaptedCover (B : Set Y) (V₀ : Y → Set Y) {ι : Type} [Fintype ι] (V : ι → Set Y)
    (N : ℕ) : Prop where
  isOpen : ∀ i, IsOpen (V i)
  order : ∀ s : Finset ι, N < s.card → ⋂ i ∈ s, V i = ∅
  contractible : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, V i).Nonempty →
    ContractibleSpace (⋂ i ∈ s, V i)
  locallyPathConnected : ∀ s : Finset ι, LocallyPathConnectedSpace (⋂ i ∈ s, V i)
  free_or_branch : ∀ i, Disjoint (V i) B ∨ ∃ b ∈ V i, V i ∩ B ⊆ {b} ∧ V i ⊆ V₀ b ∧
    ∃ h : C(I × V i, V i), (∀ y, h (0, y) = y) ∧
      ∀ t y, ((h (t, y) : Y) = b ↔ (t = 1 ∨ (y : Y) = b))
  free_of_two : ∀ s : Finset ι, 2 ≤ s.card → (⋂ i ∈ s, V i).Nonempty →
    ∃ i ∈ s, Disjoint (V i) B

namespace IsAdaptedCover

variable {B : Set Y} {V₀ : Y → Set Y} {ι : Type} [Fintype ι] {V : ι → Set Y} {N : ℕ}

/-- A member of an adapted cover is contractible when nonempty. -/
theorem contractibleSpace_of_nonempty (hV : IsAdaptedCover B V₀ V N) (i : ι)
    (hi : (V i).Nonempty) : ContractibleSpace (V i) := by
  have h := hV.contractible {i} (Finset.singleton_nonempty i) (by simpa using hi)
  rwa [Finset.set_biInter_singleton] at h

/-- A member of an adapted cover is locally path-connected. -/
theorem locallyPathConnectedSpace (hV : IsAdaptedCover B V₀ V N) (i : ι) :
    LocallyPathConnectedSpace (V i) := by
  have h := hV.locallyPathConnected {i}
  rwa [Finset.set_biInter_singleton] at h

/-- Two distinct members of an adapted cover of order at most `1` are disjoint. -/
theorem disjoint_of_order_le_one (hV : IsAdaptedCover B V₀ V N) (hN : N ≤ 1) {i j : ι}
    (hij : i ≠ j) : Disjoint (V i) (V j) := by
  classical
  have h := hV.order {i, j} (by rw [Finset.card_pair hij]; omega)
  rw [disjoint_iff_inter_eq_empty, ← h]
  ext y
  simp

end IsAdaptedCover

end Weil

end
