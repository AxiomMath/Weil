/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.Topology.Covering.BranchedCoverLocal

/-!
# Pulling back an adapted cover along a branched cover

Let `π : X → Y` be a finite branched cover with branch locus contained in `B`, with `X` compact
Hausdorff and `Y` Hausdorff, and let `V` be a finite open cover of part of `Y` adapted to `B` and
to the branch neighbourhoods `Weil.IsBranchedCover.branchNhd`, of order at most `N`. Each member
of `V` has a preimage that splits into finitely many disjoint open *pieces*:

* a member disjoint from `B` splits into sheets, each mapped injectively onto the member;
* any other member is a branch member around a point `b`, and its preimage splits into
  contractible pieces, one around each point of `π⁻¹ {b}`.

The family of all pieces is a finite open cover of `π⁻¹ (⋃ i, V i)` of order at most `N`
(two distinct pieces of one member are disjoint), and every nonempty finite intersection `Z` of
pieces is contractible. A single branch piece is contractible by construction. Otherwise `Z`
lies over the intersection `V_T` of at least one member disjoint from `B`, so it lies in a
sheet `P` over such a member and `π` is injective on it. Each piece `U` of a member `j` in
the intersection, together with the union of the other pieces of `j`, splits `π (P ∩ π⁻¹ V_T)`
into two disjoint open sets, the first meeting `V_T`; since `V_T` is connected, `π (P ∩ U)`
contains `V_T`. Hence `π` maps `Z` bijectively, and openly, onto the contractible set `V_T`.

## Main results

* `Weil.IsBranchedCover.isOpen_image_of_subset`: a branched cover maps open subsets of
  `π⁻¹ Bᶜ` to open sets.
* `Weil.IsBranchedCover.contractibleSpace_of_injOn`: an open subset of `π⁻¹ Bᶜ` on which `π`
  is injective is homeomorphic to its image, hence contractible when the image is.
* `Weil.IsBranchedCover.exists_contractible_cover`: the pulled-back cover of an adapted cover of
  order at most `N` is a finite open cover of the preimage, of order at most `N`, with
  contractible nonempty finite intersections.
* `Weil.IsBranchedCover.exists_nhds_contractible_cover`: the same, with the branch
  neighbourhoods quantified existentially.
-/

public section

open Set Function Topology unitInterval

namespace Weil

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsBranchedCover

variable {π : X → Y} {B : Set Y}

/-- A branched cover maps open subsets of `π⁻¹ Bᶜ` to open sets. -/
theorem isOpen_image_of_subset (hπ : IsBranchedCover π B) {O : Set X} (hO : IsOpen O)
    (hOB : O ⊆ π ⁻¹' Bᶜ) : IsOpen (π '' O) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  rw [← hπ.isLocalHomeomorphOn.map_nhds_eq (hOB hx)]
  exact Filter.image_mem_map (hO.mem_nhds hx)

/-- An open subset `Z ⊆ π⁻¹ Bᶜ` on which a branched cover `π` is injective is contractible as
soon as its image is. -/
theorem contractibleSpace_of_injOn (hπ : IsBranchedCover π B) {Z : Set X} (hZ : IsOpen Z)
    (hZB : Z ⊆ π ⁻¹' Bᶜ) (hinj : InjOn π Z) [ContractibleSpace (π '' Z)] :
    ContractibleSpace Z := by
  set g : Z → Y := π ∘ Subtype.val with hgdef
  have hg : IsOpenEmbedding g := by
    refine .of_continuous_injective_isOpenMap (hπ.continuous.comp continuous_subtype_val)
      (fun a b h ↦ Subtype.ext (hinj a.2 b.2 h)) ?_
    intro U hU
    rw [hgdef, image_comp]
    exact hπ.isOpen_image_of_subset (hZ.isOpenMap_subtype_val U hU)
      ((image_subset_iff.mpr fun z _ ↦ z.2).trans hZB)
  have hr : range g = π '' Z := by rw [hgdef, range_comp, Subtype.range_coe]
  exact (hg.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)).contractibleSpace

/-- The preimage of a member of an adapted cover splits into finitely many disjoint open
pieces: sheets mapped injectively onto the member if it is disjoint from `B`, contractible
pieces otherwise. -/
theorem exists_pieces [CompactSpace X] [T2Space X] [T2Space Y] (hπ : IsBranchedCover π B)
    {ι : Type} [Fintype ι] {V : ι → Set Y} {N : ℕ} (hV : IsAdaptedCover B hπ.branchNhd V N)
    (i : ι) :
    ∃ (J : Type) (_ : Finite J) (P : J → Set X), (∀ a, IsOpen (P a)) ∧
      Pairwise (Disjoint on P) ∧ (⋃ a, P a) = π ⁻¹' V i ∧
      (Disjoint (V i) B → ∀ a, InjOn π (P a) ∧ π '' P a = V i) ∧
      (¬ Disjoint (V i) B → ∀ a, ContractibleSpace (P a)) := by
  by_cases hfree : Disjoint (V i) B
  · rcases (V i).eq_empty_or_nonempty with he | hne
    · refine ⟨Empty, inferInstance, Empty.elim, fun a ↦ a.elim, fun a ↦ a.elim, ?_,
        fun _ a ↦ a.elim, fun h ↦ (h hfree).elim⟩
      simp [he]
    · have := hV.contractibleSpace_of_nonempty i hne
      have := hV.locallyPathConnectedSpace i
      obtain ⟨J, hJ, s, hso, hsd, hsU, hs⟩ := hπ.exists_sheets (hV.isOpen i) hfree
      exact ⟨J, hJ, s, hso, hsd, hsU, fun _ ↦ hs, fun h ↦ (h hfree).elim⟩
  · obtain ⟨b, hbV, hVB, hVV₀, h, h0, hhb⟩ :=
      (hV.free_or_branch i).resolve_left hfree
    obtain ⟨W, hWo, -, hWd, hWU, hWc⟩ :=
      hπ.branchNhd_spec b (V i) hbV (hV.isOpen i) hVV₀ hVB h h0 hhb
    have : Finite (π ⁻¹' {b}) := (hπ.finite_fiber b).to_subtype
    let e := Finite.equivFin (π ⁻¹' {b})
    refine ⟨Fin (Nat.card (π ⁻¹' {b})), inferInstance, W ∘ e.symm, fun a ↦ hWo _,
      fun a c hac ↦ hWd (e.symm.injective.ne hac), ?_, fun h ↦ (hfree h).elim,
      fun _ a ↦ hWc _⟩
    rw [← hWU]
    exact e.symm.surjective.iUnion_comp W

/-- **Pulled-back cover.** Pulling back a finite open cover of order at most `N` adapted to the
branch locus `B` and to the branch neighbourhoods `branchNhd` along a finite branched cover
gives a finite open cover of the preimage of its union, of order at most `N`, whose nonempty
finite intersections are contractible. -/
theorem exists_contractible_cover [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) {ι : Type} [Fintype ι] (V : ι → Set Y) (N : ℕ)
    (hV : IsAdaptedCover B hπ.branchNhd V N) :
    ∃ (κ : Type) (_ : Fintype κ) (U : κ → Set X), (∀ k, IsOpen (U k)) ∧
      (⋃ k, U k) = π ⁻¹' (⋃ i, V i) ∧ (∀ S : Finset κ, N < S.card → ⋂ k ∈ S, U k = ∅) ∧
      ∀ S : Finset κ, S.Nonempty → (⋂ k ∈ S, U k).Nonempty →
        ContractibleSpace (⋂ k ∈ S, U k) := by
  classical
  choose J hJ P hPo hPd hPU hPfree hPbr using fun i ↦ hπ.exists_pieces hV i
  let κ := Σ i, J i
  have : Finite κ := inferInstance
  let U : κ → Set X := fun k ↦ P k.1 k.2
  -- the union of the other pieces of the same member
  let Uc : κ → Set X := fun k ↦ ⋃ (c : J k.1) (_ : c ≠ k.2), P k.1 c
  have hUo : ∀ k, IsOpen (U k) := fun k ↦ hPo k.1 k.2
  have hUco : ∀ k, IsOpen (Uc k) := fun k ↦ isOpen_biUnion fun c _ ↦ hPo k.1 c
  have hUUc : ∀ k, Disjoint (U k) (Uc k) := fun k ↦
    disjoint_iUnion₂_right.mpr fun c hc ↦ hPd k.1 (Ne.symm hc)
  have hUsub : ∀ k, U k ⊆ π ⁻¹' V k.1 := fun k ↦ (hPU k.1) ▸ subset_iUnion (P k.1) k.2
  have hcovk : ∀ k, π ⁻¹' V k.1 ⊆ U k ∪ Uc k := by
    intro k x hx
    rw [← hPU k.1] at hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    by_cases hck : c = k.2
    · subst hck; exact Or.inl hc
    · exact Or.inr (mem_biUnion hck hc)
  -- a nonempty intersection uses at most one piece of each member
  have hinj : ∀ S : Finset κ, (⋂ k ∈ S, U k).Nonempty → InjOn Sigma.fst (S : Set κ) := by
    rintro S ⟨z, hz⟩ ⟨i, a⟩ hk ⟨i', a'⟩ hk' (rfl : i = i')
    by_contra hne
    have haa' : a ≠ a' := by rintro rfl; exact hne rfl
    rw [mem_iInter₂] at hz
    exact disjoint_left.mp (hPd i haa') (hz _ hk) (hz _ hk')
  -- a nonempty intersection lies over the intersection of the members involved
  have hover : ∀ S : Finset κ, (⋂ k ∈ S, U k) ⊆ π ⁻¹' ⋂ i ∈ S.image Sigma.fst, V i := by
    intro S z hz
    rw [mem_iInter₂] at hz
    simp only [mem_preimage, mem_iInter₂, Finset.mem_image]
    rintro _ ⟨k, hk, rfl⟩
    exact hUsub k (hz k hk)
  refine ⟨κ, Fintype.ofFinite κ, U, hUo, ?_, ?_, ?_⟩
  · simp only [U, κ, iUnion_sigma, hPU, preimage_iUnion]
  · intro S hS
    by_contra hne
    have hZ : (⋂ k ∈ S, U k).Nonempty := nonempty_iff_ne_empty.mpr hne
    obtain ⟨z, hz⟩ := hZ
    have hcard : (S.image Sigma.fst).card = S.card := Finset.card_image_of_injOn (hinj S ⟨z, hz⟩)
    have h := hV.order (S.image Sigma.fst) (hcard ▸ hS)
    have := hover S hz
    rw [h] at this
    exact this
  · intro S hSne hZ
    set Z := ⋂ k ∈ S, U k with hZdef
    set T := S.image Sigma.fst
    set VT := ⋂ i ∈ T, V i
    have hcard : T.card = S.card := Finset.card_image_of_injOn (hinj S hZ)
    have hZo : IsOpen Z := isOpen_biInter_finset fun k _ ↦ hUo k
    have hTne : T.Nonempty := hSne.image _
    have hVTne : VT.Nonempty := hZ.image π |>.mono (image_subset_iff.mpr (hover S))
    by_cases hfr : ∃ k₀ ∈ S, Disjoint (V k₀.1) B
    · obtain ⟨k₀, hk₀, hfree⟩ := hfr
      obtain ⟨hinj₀, himg₀⟩ := hPfree k₀.1 hfree k₀.2
      have hZU₀ : Z ⊆ U k₀ := biInter_subset_of_mem hk₀
      have hU₀B : U k₀ ⊆ π ⁻¹' Bᶜ := fun x hx ↦ disjoint_left.mp hfree (hUsub k₀ hx)
      have hVTsub : VT ⊆ V k₀.1 := biInter_subset_of_mem (Finset.mem_image_of_mem _ hk₀)
      have hVTc : ContractibleSpace VT := hV.contractible T hTne hVTne
      have hVTpc : IsPreconnected VT := isPreconnected_iff_preconnectedSpace.mpr inferInstance
      obtain ⟨z₀, hz₀⟩ := hZ
      have hZimg : π '' Z = VT := by
        refine Subset.antisymm (image_subset_iff.mpr (hover S)) fun y hy ↦ ?_
        obtain ⟨x, hx₀, hxy⟩ : y ∈ π '' U k₀ := himg₀ ▸ hVTsub hy
        subst hxy
        refine ⟨x, ?_, rfl⟩
        rw [hZdef, mem_iInter₂]
        intro k hk
        have hkT : k.1 ∈ T := Finset.mem_image_of_mem _ hk
        have hVTk : VT ⊆ V k.1 := biInter_subset_of_mem hkT
        have hsplit : VT ⊆ π '' (U k₀ ∩ U k) := by
          refine hVTpc.subset_left_of_subset_union
            (hπ.isOpen_image_of_subset ((hUo k₀).inter (hUo k))
              (inter_subset_left.trans hU₀B))
            (hπ.isOpen_image_of_subset ((hUo k₀).inter (hUco k))
              (inter_subset_left.trans hU₀B)) ?_ ?_ ?_
          · refine disjoint_left.mpr ?_
            rintro _ ⟨a, ⟨ha₀, hak⟩, rfl⟩ ⟨c, ⟨hc₀, hck⟩, hca⟩
            rw [hinj₀ hc₀ ha₀ hca] at hck
            exact disjoint_left.mp (hUUc k) hak hck
          · intro y' hy'
            obtain ⟨x', hx'₀, rfl⟩ : y' ∈ π '' U k₀ := himg₀ ▸ hVTsub hy'
            rcases hcovk k (hVTk hy') with h | h
            · exact Or.inl ⟨x', ⟨hx'₀, h⟩, rfl⟩
            · exact Or.inr ⟨x', ⟨hx'₀, h⟩, rfl⟩
          · have hz₀' := hz₀
            rw [hZdef, mem_iInter₂] at hz₀'
            exact ⟨π z₀, hover S hz₀, z₀, ⟨hZU₀ hz₀, hz₀' k hk⟩, rfl⟩
        obtain ⟨x'', ⟨hx''₀, hx''k⟩, hx''⟩ := hsplit hy
        rwa [hinj₀ hx''₀ hx₀ hx''] at hx''k
      have : ContractibleSpace (π '' Z) := hZimg ▸ hVTc
      exact hπ.contractibleSpace_of_injOn hZo (hZU₀.trans hU₀B) (hinj₀.mono hZU₀)
    · push Not at hfr
      have hS1 : S.card = 1 := by
        by_contra h1
        have h2 : 2 ≤ T.card := by
          have := hSne.card_pos
          omega
        obtain ⟨i, hiT, hi⟩ := hV.free_of_two T h2 hVTne
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hiT
        exact hfr k hk hi
      obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp hS1
      have := hPbr k.1 (hfr k (Finset.mem_singleton_self k)) k.2
      rw [hZdef, Finset.set_biInter_singleton]
      exact this

/-- **Pulled-back cover**, with the branch neighbourhoods quantified existentially: there are
neighbourhoods `V₀ b` of the points `b` of `Y` such that every finite open cover of order at most
`N` adapted to `B` and `V₀` pulls back to a finite open cover of the preimage of its union, of
order at most `N`, with contractible nonempty finite intersections. -/
theorem exists_nhds_contractible_cover [CompactSpace X] [T2Space X] [T2Space Y]
    (hπ : IsBranchedCover π B) :
    ∃ V₀ : Y → Set Y, (∀ b, V₀ b ∈ 𝓝 b) ∧ ∀ {ι : Type} [Fintype ι] (V : ι → Set Y) (N : ℕ),
      IsAdaptedCover B V₀ V N →
      ∃ (κ : Type) (_ : Fintype κ) (U : κ → Set X), (∀ k, IsOpen (U k)) ∧
        (⋃ k, U k) = π ⁻¹' (⋃ i, V i) ∧ (∀ S : Finset κ, N < S.card → ⋂ k ∈ S, U k = ∅) ∧
        ∀ S : Finset κ, S.Nonempty → (⋂ k ∈ S, U k).Nonempty →
          ContractibleSpace (⋂ k ∈ S, U k) :=
  ⟨hπ.branchNhd, hπ.branchNhd_mem_nhds, fun V N hV ↦ hπ.exists_contractible_cover V N hV⟩

end IsBranchedCover

end Weil

end
