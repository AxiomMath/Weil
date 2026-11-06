/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.Topology.Covering.BranchedCover

/-!
# Branched covers near a branch point

Let `π : X → Y` be a finite branched cover with branch locus contained in `B`, with `X` compact
Hausdorff and `Y` Hausdorff, and let `b ∈ Y`. Choose pairwise disjoint open neighbourhoods
`N p` of the finitely many points `p` of the fibre `π⁻¹ {b}`. Since `π` is a closed map,
`V₀ := Y ∖ π (X ∖ ⋃ N p)` is a neighbourhood of `b`, and `π⁻¹ V₀ ⊆ ⋃ N p`.

If now `V ⊆ V₀` is an open neighbourhood of `b` meeting `B` at most in `b`, carrying a
contraction `h` to `b` which reaches `b` only at time `1` (or from `b`), then `π⁻¹ V` is the
disjoint union of the open sets `W p := π⁻¹ V ∩ N p`, and each `W p` is contractible. The
contraction of `W p` to `p` sends `(t, x)` with `t < 1` and `π x ≠ b` to the end point of the lift,
starting at `x`, of the path `s ↦ h (s t, π x)`, which runs in `V ∖ {b}`, over which `π` is a
covering map; all other points go to `p`. Continuity at the points sent to `p` holds because the
sets `N p ∩ π⁻¹ M`, for `M` a neighbourhood of `b`, form a neighbourhood basis of `p`.

## Main definitions

* `Weil.IsBranchedCover.branchNhd`: a neighbourhood `V₀` of `b` as above.

## Main results

* `Weil.IsBranchedCover.exists_nhds_contractible_pieces`: there is a neighbourhood `V₀` of `b`
  such that for every open `V ⊆ V₀` containing `b`, meeting `B` at most in `b` and contracted to
  `b` by a homotopy reaching `b` only at time `1` or from `b`, the preimage `π⁻¹ V` is a
  disjoint union of open contractible sets `W p`, one around each point `p` of `π⁻¹ {b}`.
* `Weil.IsBranchedCover.branchNhd_mem_nhds`, `Weil.IsBranchedCover.branchNhd_spec`: the
  same for `branchNhd`.

## Implementation notes

The lift on the half-open interval `[0, 1)` is obtained from Mathlib's homotopy lifting
property for covering maps applied to the homotopy `(s, (t, x)) ↦ h (s t, π x)` on
`I × {(t, x) | t < 1, π x ≠ b}`, evaluated at `s = 1`.
-/

@[expose] public section

open Set Function Topology unitInterval Filter

namespace Weil

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsBranchedCover

variable {π : X → Y} {B : Set Y}

/-- If `closure N` meets the fibre of `π` through `p` only in `p`, a map `f` with values in `N`
taking the value `p` at `z₀` is continuous at `z₀` as soon as `π ∘ f` is. -/
theorem continuousAt_of_continuousAt_comp [CompactSpace X] [T2Space Y] {Z : Type*}
    [TopologicalSpace Z] (hπc : Continuous π) {N : Set X} {p : X}
    (hN : closure N ∩ π ⁻¹' {π p} ⊆ {p}) {f : Z → X} (hf : ∀ z, f z ∈ N) {z₀ : Z}
    (hz₀ : f z₀ = p) (hcont : ContinuousAt (π ∘ f) z₀) : ContinuousAt f z₀ := by
  rw [ContinuousAt, hz₀, (nhds_basis_opens p).tendsto_right_iff]
  rintro O ⟨hpO, hO⟩
  set C := closure N \ O
  have hC : IsClosed (π '' C) :=
    ((isClosed_closure.sdiff hO).isCompact.image hπc).isClosed
  have hpC : π p ∉ π '' C := by
    rintro ⟨c, ⟨hcN, hcO⟩, hc⟩
    exact hcO (by rw [hN ⟨hcN, hc⟩] ; exact hpO)
  have hM : (π '' C)ᶜ ∈ 𝓝 (π (f z₀)) := by
    rw [hz₀]; exact hC.isOpen_compl.mem_nhds hpC
  filter_upwards [hcont hM] with z hz
  by_contra hzO
  exact hz ⟨f z, ⟨subset_closure (hf z), hzO⟩, rfl⟩

/-- The contraction of a branch piece. Let `V` be an open neighbourhood of `b` meeting `B` at
most in `b`, contracted to `b` by `h` reaching `b` only at time `1` or from `b`, and let `N` be
an open neighbourhood of a point `p` over `b` whose closure meets `π⁻¹ {b}` only in `p`, such
that every path starting in `N` and lying over `V` stays in `N`. Then `π⁻¹ V ∩ N` is
contractible. -/
theorem contractibleSpace_preimage_inter [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) {b : Y} {V : Set Y} (hbV : b ∈ V)
    (hVB : V ∩ B ⊆ {b}) (h : C(I × V, V)) (h0 : ∀ y, h (0, y) = y)
    (hhb : ∀ t y, (h (t, y) : Y) = b ↔ (t = 1 ∨ (y : Y) = b)) {N : Set X} {p : X}
    (hpN : p ∈ N) (hpb : π p = b) (hNb : closure N ∩ π ⁻¹' {b} ⊆ {p})
    (hNstay : ∀ γ : C(I, X), γ 0 ∈ N → (∀ s, π (γ s) ∈ V) → ∀ s, γ s ∈ N) :
    ContractibleSpace (π ⁻¹' V ∩ N : Set X) := by
  classical
  set W : Set X := π ⁻¹' V ∩ N with hW
  have hpW : p ∈ W := ⟨by simpa [hpb] using hbV, hpN⟩
  -- the covering map over `V ∖ {b}`
  set V' : Set Y := V \ {b} with hV'
  have hV'B : ∀ y ∈ V', y ∉ B := fun y hy hyB ↦ hy.2 (hVB ⟨hy.1, hyB⟩)
  have hcovV' : IsCoveringMapOn π V' := fun y hy ↦ hπ.isCoveringMapOn y (hV'B y hy)
  set E : Set X := π ⁻¹' V' with hE
  set g : E → V' := V'.restrictPreimage π
  have hg : IsCoveringMap g := hcovV'.isCoveringMap_restrictPreimage
  have hgval : ∀ x : E, ((g x : V') : Y) = π x := fun _ ↦ rfl
  -- the parameter space of the lifted homotopy
  set A : Set (I × W) := {q | q.1 < 1 ∧ π q.2 ≠ b} with hA
  have hmul : ∀ s u : I, u < 1 → s * u ≠ 1 := fun s u hu hsu ↦
    (lt_of_le_of_lt mul_le_right hu).ne hsu
  have hHmem : ∀ (s : I) (a : A), (h (s * a.1.1, ⟨π a.1.2, a.1.2.2.1⟩) : Y) ∈ V' := fun s a ↦
    ⟨(h _).2, fun hb ↦ by
      rcases (hhb _ _).mp hb with h1 | h1
      · exact hmul s _ a.2.1 h1
      · exact a.2.2 h1⟩
  let H : C(I × A, V') :=
    ⟨fun sa ↦ ⟨h (sa.1 * sa.2.1.1, ⟨π sa.2.1.2, sa.2.1.2.2.1⟩), hHmem sa.1 sa.2⟩, by
      refine Continuous.subtype_mk (continuous_subtype_val.comp (h.continuous.comp ?_)) _
      refine Continuous.prodMk (by fun_prop) ?_
      exact Continuous.subtype_mk (hπ.continuous.comp (by fun_prop)) _⟩
  let f : C(A, E) := ⟨fun a ↦ ⟨a.1.2, a.1.2.2.1, a.2.2⟩, by fun_prop⟩
  have H_0 : ∀ a, H (0, a) = g (f a) := fun a ↦ by
    apply Subtype.ext
    change (h (0 * a.1.1, _) : Y) = π a.1.2
    rw [zero_mul, h0]
  set L := hg.liftHomotopy H f H_0
  have hLlifts : ∀ s a, π (L (s, a) : X) = h (s * a.1.1, ⟨π a.1.2, a.1.2.2.1⟩) := fun s a ↦ by
    rw [← hgval]
    exact congrArg Subtype.val (congrFun (hg.liftHomotopy_lifts H f H_0) (s, a))
  have hL0 : ∀ a, (L (0, a) : X) = a.1.2 := fun a ↦
    congrArg Subtype.val (hg.liftHomotopy_zero H f H_0 a)
  -- the lifts stay in `N`
  have hLN : ∀ s a, (L (s, a) : X) ∈ N := fun s a ↦ by
    let γ : C(I, X) := ⟨fun s ↦ (L (s, a) : X), by fun_prop⟩
    refine hNstay γ ?_ (fun s ↦ ?_) s
    · change (L (0, a) : X) ∈ N
      rw [hL0]; exact a.1.2.2.2
    · change π (L (s, a) : X) ∈ V
      exact (L (s, a)).2.1
  -- the contraction
  let K : I × W → X := fun q ↦ if hq : q ∈ A then (L (1, ⟨q, hq⟩) : X) else p
  have hKπ : ∀ q : I × W, π (K q) = h (q.1, ⟨π q.2, q.2.2.1⟩) := by
    rintro ⟨t, x⟩
    by_cases hq : (t, x) ∈ A
    · simp only [K, hq, ↓reduceDIte, hLlifts, one_mul]
    · simp only [K, hq, ↓reduceDIte, hpb]
      symm
      refine (hhb _ _).mpr ?_
      simp only [hA, mem_ofPred_eq, not_and_or, not_lt, not_not] at hq
      rcases hq with h1 | h1
      · exact Or.inl (le_antisymm le_one' h1)
      · exact Or.inr h1
  have hKN : ∀ q, K q ∈ N := by
    intro q
    by_cases hq : q ∈ A
    · simp only [K, hq, ↓reduceDIte]; exact hLN _ _
    · simp only [K, hq, ↓reduceDIte]; exact hpN
  have hKW : ∀ q, K q ∈ W := fun q ↦ ⟨by
    change π (K q) ∈ V
    rw [hKπ]; exact (h _).2, hKN q⟩
  have hAopen : IsOpen A := by
    refine (isOpen_lt continuous_fst continuous_const).inter ?_
    exact (isOpen_compl_singleton.preimage (hπ.continuous.comp
      (continuous_subtype_val.comp continuous_snd)))
  have hKcont : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : q ∈ A
    · have hon : ContinuousOn K A := by
        rw [continuousOn_iff_continuous_domRestrict]
        refine (show Continuous fun a : A ↦ (L (1, a) : X) by fun_prop).congr fun a ↦ ?_
        simp [K, Set.domRestrict_apply, a.2]
      exact hon.continuousAt (hAopen.mem_nhds hq)
    · refine continuousAt_of_continuousAt_comp hπ.continuous (N := N) (p := p) ?_ hKN
        (by simp only [K, hq, ↓reduceDIte]) ?_
      · rw [hpb]; exact hNb
      · have : π ∘ K = fun q : I × W ↦ (h (q.1, ⟨π q.2, q.2.2.1⟩) : Y) := funext hKπ
        rw [this]
        refine (continuous_subtype_val.comp (h.continuous.comp ?_)).continuousAt
        exact continuous_fst.prodMk
          (Continuous.subtype_mk (hπ.continuous.comp (by fun_prop)) _)
  have hK0 : ∀ x : W, K (0, x) = x := by
    intro x
    by_cases hq : ((0 : I), x) ∈ A
    · simp only [K, hq, ↓reduceDIte]
      -- the lifted path is constant
      have hconst : (fun s ↦ L (s, ⟨(0, x), hq⟩)) = fun _ ↦ f ⟨(0, x), hq⟩ := by
        refine hg.eq_of_comp_eq (by fun_prop) continuous_const ?_ 0
          (hg.liftHomotopy_zero H f H_0 _)
        funext s
        apply Subtype.ext
        simp only [comp_apply]
        rw [hgval, hgval, hLlifts]
        change (h (s * 0, _) : Y) = π x
        rw [mul_zero, h0]
      exact congrArg Subtype.val (congrFun hconst 1)
    · simp only [K, hq, ↓reduceDIte]
      simp only [hA, mem_ofPred_eq, not_and, not_not] at hq
      have hxb : π (x : X) = b := hq zero_lt_one
      exact (hNb ⟨subset_closure x.2.2, hxb⟩).symm
  have hK1 : ∀ x : W, K (1, x) = p := fun x ↦ by
    have : ((1 : I), x) ∉ A := fun hq ↦ lt_irrefl _ hq.1
    simp only [K, this, ↓reduceDIte]
  let Kh : (ContinuousMap.id W).Homotopy (ContinuousMap.const W ⟨p, hpW⟩) :=
    { toFun := fun q ↦ ⟨K q, hKW q⟩
      continuous_toFun := hKcont.subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext (hK0 x)
      map_one_left := fun x ↦ Subtype.ext (hK1 x) }
  have : Nonempty W := ⟨⟨p, hpW⟩⟩
  exact (contractible_iff_id_nullhomotopic W).mpr ⟨⟨p, hpW⟩, ⟨Kh⟩⟩

/-- **Branch pieces.** Around a point `b` of the base of a finite branched cover there is a
neighbourhood `V₀` such that for every open `V ⊆ V₀` containing `b`, meeting the branch locus
at most in `b`, and contracted to `b` by a homotopy reaching `b` only at time `1` or from `b`,
the preimage `π⁻¹ V` is a disjoint union of open contractible sets `W p`, one around each point
`p` of the fibre `π⁻¹ {b}`. -/
theorem exists_nhds_contractible_pieces [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) (b : Y) :
    ∃ V₀ ∈ 𝓝 b, ∀ (V : Set Y) (_hbV : b ∈ V), IsOpen V → V ⊆ V₀ → V ∩ B ⊆ {b} →
      ∀ h : C(I × V, V), (∀ y, h (0, y) = y) →
        (∀ t y, (h (t, y) : Y) = b ↔ (t = 1 ∨ (y : Y) = b)) →
      ∃ W : π ⁻¹' {b} → Set X, (∀ p, IsOpen (W p)) ∧ (∀ p, (p : X) ∈ W p) ∧
        Pairwise (Disjoint on W) ∧ (⋃ p, W p) = π ⁻¹' V ∧ ∀ p, ContractibleSpace (W p) := by
  classical
  obtain ⟨U, hU, hUd⟩ := (hπ.finite_fiber b).t2_separation
  set F : Set X := π ⁻¹' {b}
  let N : F → Set X := fun p ↦ U p
  have hNo : ∀ p, IsOpen (N p) := fun p ↦ (hU p).2
  have hpN : ∀ p : F, (p : X) ∈ N p := fun p ↦ (hU p).1
  have hNd : Pairwise (Disjoint on N) := fun p q hpq ↦
    hUd p.2 q.2 (fun h ↦ hpq (Subtype.ext h))
  have hcover : F ⊆ ⋃ p, N p := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hpN ⟨x, hx⟩⟩
  set V₀ : Set Y := (π '' (⋃ p, N p)ᶜ)ᶜ
  have hV₀o : IsOpen V₀ :=
    (hπ.isClosedMap _ (isOpen_iUnion hNo).isClosed_compl).isOpen_compl
  have hbV₀ : b ∈ V₀ := by
    rintro ⟨x, hx, hxb⟩
    exact hx (hcover hxb)
  have hV₀N : π ⁻¹' V₀ ⊆ ⋃ p, N p := fun x hx ↦ by
    by_contra hxN
    exact hx ⟨x, hxN, rfl⟩
  refine ⟨V₀, hV₀o.mem_nhds hbV₀, fun V hbV hVo hVV₀ hVB h h0 hhb ↦ ?_⟩
  refine ⟨fun p ↦ π ⁻¹' V ∩ N p, fun p ↦ (hVo.preimage hπ.continuous).inter (hNo p),
    fun p ↦ ⟨by simpa [show π p = b from p.2] using hbV, hpN p⟩,
    fun p q hpq ↦ ((hNd hpq).mono inter_subset_right inter_subset_right), ?_, fun p ↦ ?_⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun p ↦ inter_subset_left
    · intro x hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp (hV₀N (hVV₀ hx))
      exact mem_iUnion.mpr ⟨p, hx, hp⟩
  · refine contractibleSpace_preimage_inter hπ hbV hVB h h0 hhb (hpN p) p.2 ?_ ?_
    · rintro x ⟨hxcl, hxb⟩
      by_contra hxp
      have hq : (⟨x, hxb⟩ : F) ≠ p := fun h ↦ hxp (congrArg Subtype.val h)
      exact disjoint_left.mp ((hNd hq).closure_right (hNo _)) (hpN ⟨x, hxb⟩) hxcl
    · intro γ hγ0 hγV s
      have hsub : range γ ⊆ N p ∪ ⋃ q ∈ ({p}ᶜ : Set F), N q := by
        rintro _ ⟨s, rfl⟩
        obtain ⟨q, hq⟩ := mem_iUnion.mp (hV₀N (hVV₀ (hγV s)))
        by_cases hqp : q = p
        · exact Or.inl (hqp ▸ hq)
        · exact Or.inr (mem_biUnion hqp hq)
      refine (isPreconnected_range γ.continuous).subset_left_of_subset_union (hNo p)
        (isOpen_biUnion fun q _ ↦ hNo q) ?_ hsub ⟨γ 0, mem_range_self 0, hγ0⟩ (mem_range_self s)
      refine disjoint_iUnion₂_right.mpr fun q hq ↦ hNd (Ne.symm hq)

/-- A neighbourhood of `b` satisfying the conclusion of
`Weil.IsBranchedCover.exists_nhds_contractible_pieces`. -/
noncomputable def branchNhd [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) (b : Y) : Set Y :=
  (hπ.exists_nhds_contractible_pieces b).choose

theorem branchNhd_mem_nhds [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) (b : Y) : hπ.branchNhd b ∈ 𝓝 b :=
  (hπ.exists_nhds_contractible_pieces b).choose_spec.1

theorem branchNhd_spec [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) (b : Y) :
    ∀ (V : Set Y) (_hbV : b ∈ V), IsOpen V → V ⊆ hπ.branchNhd b → V ∩ B ⊆ {b} →
      ∀ h : C(I × V, V), (∀ y, h (0, y) = y) →
        (∀ t y, (h (t, y) : Y) = b ↔ (t = 1 ∨ (y : Y) = b)) →
      ∃ W : π ⁻¹' {b} → Set X, (∀ p, IsOpen (W p)) ∧ (∀ p, (p : X) ∈ W p) ∧
        Pairwise (Disjoint on W) ∧ (⋃ p, W p) = π ⁻¹' V ∧ ∀ p, ContractibleSpace (W p) :=
  (hπ.exists_nhds_contractible_pieces b).choose_spec.2

end IsBranchedCover

end Weil

end
