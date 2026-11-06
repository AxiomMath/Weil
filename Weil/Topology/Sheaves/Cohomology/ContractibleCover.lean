module

public import Weil.Topology.Sheaves.Cohomology.HomotopyInvariance
public import Weil.Topology.Sheaves.Cohomology.OpenSubspace

/-!
# Vanishing of cohomology for covers with contractible intersections

Let `Z` be a topological space and `U : κ → Set Z` a finite open cover such that no `N + 1`
distinct members have a common point, and every nonempty finite intersection of members is
contractible. Then the sheaf cohomology `Hⁿ(Z, A)` of every constant sheaf `A` vanishes for
`n ≥ N`.

Indeed, every nonempty finite intersection `V` is contractible, hence acyclic for constant
coefficients, and the cohomology of the constant sheaf of `Z` over the open `V` is the cohomology
of the constant sheaf of the subspace `V`; an empty intersection carries no cohomology at all.
Leray's theorem then computes `Hⁿ(Z, A)` by the alternating Čech complex of the cover, which
vanishes in degrees `n ≥ N` since its degree-`n` cochains are indexed by `n + 1` distinct members.

## Main results

* `TopCat.SheafCohomology.subsingleton_H_constantSheaf_of_contractible_cover`:
  `Hⁿ(Z, A) = 0` for `n ≥ N`.
* `TopCat.SheafCohomology.subsingleton_H_of_isEmpty`: the cohomology of any abelian sheaf on an
  empty space vanishes.

## Implementation notes

Everything is in universe `0`, the universe of the homotopy invariance theorem
`TopCat.SheafCohomology.subsingleton_H_of_contractibleSpace`; the index type of the cover may be
any `Type`, and need not be finite.

## References

* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Abelian Set

namespace TopCat.SheafCohomology

/-- An abelian sheaf on an empty space is a zero object. -/
theorem isZero_sheaf_of_isEmpty {X : TopCat.{0}} [IsEmpty X]
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) : IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  ext V : 3
  have hV : V.unop = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have : Subsingleton (G.obj.obj V) := by
    rw [← V.op_unop, hV]
    exact TopologicalSpace.Opens.CechAcyclic.subsingleton_obj_bot G
  exact AddCommGrpCat.ext fun _ ↦ Subsingleton.elim _ _

/-- The cohomology of an abelian sheaf on an empty space vanishes in every degree. -/
theorem subsingleton_H_of_isEmpty {X : TopCat.{0}} [IsEmpty X]
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} G n) := by
  refine ⟨fun a b ↦ ?_⟩
  have h : 𝟙 G = 0 := (IsZero.iff_id_eq_zero G).1 (isZero_sheaf_of_isEmpty G)
  have key : ∀ x : CategoryTheory.Sheaf.H.{0} G n, x = 0 := fun x ↦ by
    rw [← Ext.comp_mk₀_id x, h, Ext.mk₀_zero, Ext.comp_zero]
  rw [key a, key b]

/-- **Vanishing above the order of a cover with contractible intersections.** Let `U` be an open
cover of `Z` such that no `N + 1` distinct members meet and every nonempty finite intersection of
members is contractible. Then `Hⁿ(Z, A) = 0` for every abelian group `A` and every `n ≥ N`. -/
theorem subsingleton_H_constantSheaf_of_contractible_cover (Z : TopCat.{0}) {κ : Type}
    (U : κ → Set Z) (hUo : ∀ k, IsOpen (U k)) (hcov : (⋃ k, U k) = univ)
    (N : ℕ) (horder : ∀ S : Finset κ, N < S.card → ⋂ k ∈ S, U k = ∅)
    (hcontr : ∀ S : Finset κ, S.Nonempty → (⋂ k ∈ S, U k).Nonempty →
      ContractibleSpace (⋂ k ∈ S, U k))
    (A : AddCommGrpCat.{0}) {n : ℕ} (hn : N ≤ n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj A) n) := by
  let V : κ → Opens Z := fun k ↦ ⟨U k, hUo k⟩
  have hinf : ∀ S : Finset κ, ((⨅ k ∈ S, V k : Opens Z) : Set Z) = ⋂ k ∈ S, U k := by
    intro S
    rw [← Finset.inf_eq_iInf, Opens.coe_finset_inf, Finset.inf_eq_iInf]
    rfl
  have hU : ⨆ k, V k = ⊤ := by
    refine Opens.ext ?_
    rw [Opens.coe_iSup, Opens.coe_top]
    exact hcov
  refine TopologicalSpace.Opens.CechAcyclic.subsingleton_sheafH_of_iInf_eq_bot V _ hU ?_ N
    (fun S hS ↦ Opens.ext (by rw [hinf, horder S hS]; rfl)) hn
  intro S hS q hq
  refine (subsingleton_H'_constantSheaf_iff (⨅ k ∈ S, V k) A q).2 ?_
  by_cases hne : (⋂ k ∈ S, U k).Nonempty
  · have hc := hcontr S hS hne
    have : ContractibleSpace (TopCat.of (⨅ k ∈ S, V k : Opens Z)) := by
      have e : (⋂ k ∈ S, U k) ≃ₜ (⨅ k ∈ S, V k : Opens Z) :=
        Homeomorph.setCongr (hinf S).symm
      exact (e.toHomotopyEquiv).contractibleSpace_iff.1 hc
    exact subsingleton_H_of_contractibleSpace _ A q hq
  · have : IsEmpty (TopCat.of (⨅ k ∈ S, V k : Opens Z)) := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      refine ⟨fun x ↦ ?_⟩
      have hx := x.2
      rw [← SetLike.mem_coe, hinf, hne] at hx
      exact hx
    exact subsingleton_H_of_isEmpty _ q

end TopCat.SheafCohomology
