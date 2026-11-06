/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilFrontier.Topology.Sheaves.Cohomology.ContractibleCover
public import WeilFrontier.Topology.Covering.BranchedCoverPullbackCover
public import WeilFrontier.Topology.Covering.RiemannSphereCover
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Cohomological dimension of a branched cover of the Riemann sphere

Let `Z` be a compact Hausdorff space and `π : Z → Y` a finite branched cover of a space `Y`
presented by two charts as the Riemann sphere, with finite branch locus `B`. Then the sheaf
cohomology `Hⁿ(Z, A)` of every constant sheaf `A` vanishes for `n ≥ 3`.

The sphere `Y` is covered by two opens `Y₁`, `Y₂` carrying adapted covers of orders at most `3`
(on `Y₁`), `1` (on `Y₂`) and `2` (on `Y₁ ∩ Y₂`). Pulling these back along `π` gives open covers
of `π⁻¹ Y₁`, `π⁻¹ Y₂` and `π⁻¹ (Y₁ ∩ Y₂)` of the same orders whose nonempty finite intersections
are contractible, so the cohomology of the constant sheaf over these three opens vanishes in
degrees at least `3`, `1` and `2` respectively. The Mayer–Vietoris sequence
`Hⁿ⁻¹(π⁻¹(Y₁ ∩ Y₂)) → Hⁿ(Z) → Hⁿ(π⁻¹ Y₁) ⊕ Hⁿ(π⁻¹ Y₂)` then gives `Hⁿ(Z, A) = 0` for `n ≥ 3`.

## Main results

* `TopCat.SheafCohomology.subsingleton_H_constantSheaf_of_isBranchedCover`: `Hⁿ(Z, A) = 0` for
  `n ≥ 3`.
* `TopCat.SheafCohomology.subsingleton_H'_constantSheaf_of_contractible_cover`: the cohomology of
  a constant sheaf over an open covered by an open cover of order at most `N` with contractible
  nonempty finite intersections vanishes in degrees `n ≥ N`.

## Implementation notes

Everything is in universe `0`, the universe of
`TopCat.SheafCohomology.subsingleton_H_constantSheaf_of_contractible_cover`.

## References

* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Set Topology

namespace TopCat.SheafCohomology

/-- A subset `T` of an open `W` is homeomorphic to its preimage in the subspace `W`. -/
def preimageValHomeomorph {X : Type*} [TopologicalSpace X] {W T : Set X} (hTW : T ⊆ W) :
    (Subtype.val ⁻¹' T : Set W) ≃ₜ T where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hTW y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Vanishing over an open with a cover of contractible intersections.** Let `W` be an open of
`Z` covered by a family of opens `U` such that no `N + 1` distinct members meet and every
nonempty finite intersection of members is contractible. Then the cohomology of every constant
sheaf over `W` vanishes in degrees `n ≥ N`. -/
theorem subsingleton_H'_constantSheaf_of_contractible_cover {Z : TopCat.{0}} (W : Opens Z)
    {κ : Type} (U : κ → Set Z) (hUo : ∀ k, IsOpen (U k)) (hcov : (⋃ k, U k) = W)
    (N : ℕ) (horder : ∀ S : Finset κ, N < S.card → ⋂ k ∈ S, U k = ∅)
    (hcontr : ∀ S : Finset κ, S.Nonempty → (⋂ k ∈ S, U k).Nonempty →
      ContractibleSpace (⋂ k ∈ S, U k))
    (A : AddCommGrpCat.{0}) {n : ℕ} (hn : N ≤ n) :
    Subsingleton ((((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj
        A).cohomologyPresheaf n).obj (op W)) := by
  rw [subsingleton_H'_constantSheaf_iff.{0, 0}]
  let U' : κ → Set (TopCat.of W) := fun k ↦ Subtype.val ⁻¹' U k
  have hinter : ∀ S : Finset κ, ⋂ k ∈ S, U' k = Subtype.val ⁻¹' (⋂ k ∈ S, U k) := by
    intro S
    ext x
    simp [U']
  refine subsingleton_H_constantSheaf_of_contractible_cover (TopCat.of W) U'
    (fun k ↦ (hUo k).preimage continuous_subtype_val) ?_ N ?_ ?_ A hn
  · ext x
    have hx : (x.1 : Z) ∈ ⋃ k, U k := by rw [hcov]; exact x.2
    simpa [U'] using hx
  · intro S hS
    rw [hinter, horder S hS, preimage_empty]
  · intro S hS hne
    rw [hinter] at hne ⊢
    have hsub : (⋂ k ∈ S, U k) ⊆ (W : Set Z) := by
      obtain ⟨k, hk⟩ := hS
      intro x hx
      rw [← hcov]
      exact mem_iUnion.2 ⟨k, mem_iInter₂.1 hx k hk⟩
    have : ContractibleSpace (⋂ k ∈ S, U k) := by
      obtain ⟨x, hx⟩ := hne
      exact hcontr S hS ⟨x.1, hx⟩
    exact (preimageValHomeomorph hsub).contractibleSpace

/-- **Cohomological dimension of a branched cover of the Riemann sphere.** Let `Z` be a compact
Hausdorff space, `Y` a Hausdorff space presented by two charts as the Riemann sphere, and
`π : Z → Y` a finite branched cover with finite branch locus `B`. Then `Hⁿ(Z, A) = 0` for every
abelian group `A` and every `n ≥ 3`. -/
theorem subsingleton_H_constantSheaf_of_isBranchedCover (Z : TopCat.{0}) [CompactSpace Z]
    [T2Space Z] {Y : Type*} [TopologicalSpace Y] [T2Space Y] (c : Weil.RiemannSphereCharts Y)
    {π : Z → Y} {B : Set Y} (hB : B.Finite) (hπ : Weil.IsBranchedCover π B)
    (A : AddCommGrpCat.{0}) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj A) n) := by
  obtain ⟨Y₁, Y₂, hY₁, hY₂, hY, ⟨ι₁, _, V₁, hV₁, hV₁U⟩, ⟨ι₂, _, V₂, hV₂, hV₂U⟩,
      ⟨ι₃, _, V₃, hV₃, hV₃U⟩⟩ :=
    c.exists_adapted_covers hB hπ.branchNhd hπ.branchNhd_mem_nhds
  have hcont : Continuous π := hπ.continuous
  let W₁ : Opens Z := ⟨π ⁻¹' Y₁, hY₁.preimage hcont⟩
  let W₂ : Opens Z := ⟨π ⁻¹' Y₂, hY₂.preimage hcont⟩
  have vanish : ∀ (W : Opens Z) (T : Set Y) (_ : (W : Set Z) = π ⁻¹' T) {ι : Type} [Fintype ι]
      (V : ι → Set Y) (N : ℕ), Weil.IsAdaptedCover B hπ.branchNhd V N → (⋃ i, V i) = T →
      ∀ m, N ≤ m → Subsingleton ((((constantSheaf (Opens.grothendieckTopology Z)
        AddCommGrpCat.{0}).obj A).cohomologyPresheaf m).obj (op W)) := by
    intro W T hWT ι _ V N hV hVT m hm
    obtain ⟨κ, _, U, hUo, hUcov, hUord, hUcontr⟩ := hπ.exists_contractible_cover V N hV
    exact subsingleton_H'_constantSheaf_of_contractible_cover W U hUo
      (by rw [hUcov, hVT, hWT]) N hUord hUcontr A hm
  let F := (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj A
  let S := Opens.mayerVietorisSquare W₁ W₂
  have h4 : W₁ ⊔ W₂ = ⊤ := by
    ext x
    simp only [Opens.coe_sup, Opens.coe_top, mem_union, mem_univ, iff_true]
    have : π x ∈ Y₁ ∪ Y₂ := by rw [hY]; trivial
    exact this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hex := (S.sequence_exact F m (m + 1) rfl).exact 2
  have h1 : IsZero (F.H' m S.X₁) :=
    AddCommGrpCat.isZero_iff_subsingleton.2
      (vanish (W₁ ⊓ W₂) (Y₁ ∩ Y₂) rfl V₃ 2 hV₃ hV₃U m (by omega))
  have h3 : IsZero (F.H' (m + 1) S.X₂ ⊞ F.H' (m + 1) S.X₃) := by
    rw [biprod_isZero_iff]
    exact ⟨AddCommGrpCat.isZero_iff_subsingleton.2
        (vanish W₁ Y₁ rfl V₁ 3 hV₁ hV₁U (m + 1) (by omega)),
      AddCommGrpCat.isZero_iff_subsingleton.2
        (vanish W₂ Y₂ rfl V₂ 1 hV₂ hV₂U (m + 1) (by omega))⟩
  have h2 : IsZero (F.H' (m + 1) S.X₄) :=
    hex.isZero_X₂ (h1.eq_of_src _ _) (h3.eq_of_tgt _ _)
  have h2' : Subsingleton ((F.cohomologyPresheaf (m + 1)).obj (op (⊤ : Opens Z))) := by
    have : S.X₄ = ⊤ := h4
    rw [← this]
    exact AddCommGrpCat.isZero_iff_subsingleton.1 h2
  exact (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    F (m + 1)).2 h2'

end TopCat.SheafCohomology
