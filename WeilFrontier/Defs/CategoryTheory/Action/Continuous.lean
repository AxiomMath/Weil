module

public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.FundamentalGroup
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Weil.Attr

/-!
# Finite continuous `π₁(X, s)`-sets

Let `s` be a geometric point of a scheme `X`. A *finite continuous `π₁(X, s)`-set* is a finite
set `E` with a left action of the fundamental group `π₁(X, s)` such that some open subgroup of
`π₁(X, s)` acts trivially on `E`. With the `π₁(X, s)`-equivariant maps as morphisms they form
the category `𝒞(X, s)`.

We realise `𝒞(X, s)` as Mathlib's full subcategory `ContAction FintypeCat π₁(X, s)` of the
category `Action FintypeCat π₁(X, s)` of finite `π₁(X, s)`-sets, finite sets carrying the discrete
topology, cut out by the continuity of the action. Its morphisms are the morphisms of
`Action FintypeCat π₁(X, s)`, i.e. the equivariant maps. On a finite discrete set, continuity of
the action is the condition that some open subgroup acts trivially: the stabilizers of a
continuous action on a discrete space are open, and the finitely many of them meet in an open
subgroup acting trivially; conversely every stabilizer contains that open subgroup.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.FiniteContinuousPi1Set s` — the category `𝒞(X, s)` of finite
  continuous `π₁(X, s)`-sets.

## Main results

* `continuousSMul_iff_exists_openSubgroup_smul_eq` — an action of a topological group on a finite
  discrete set is continuous if and only if some open subgroup acts trivially.
* `Action.isContinuous_iff_exists_openSubgroup` — the same statement for an object of
  `Action FintypeCat G`.
* `AlgebraicGeometry.GeometricPoint.isContinuous_iff_exists_openSubgroup` — a finite
  `π₁(X, s)`-set is an object of `𝒞(X, s)` if and only if some open subgroup of `π₁(X, s)` acts
  trivially on it.

## Implementation notes

Finite sets carry the discrete topology through the scoped instances of `FintypeCatDiscrete`,
as in `CategoryTheory.PreGaloisCategory.functorToContAction`. The universe of the finite sets is
left free.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory

open scoped FintypeCatDiscrete

universe u w

section OpenSubgroup

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- An action of a topological group on a finite discrete set is continuous if and only if some
open subgroup acts trivially. -/
theorem continuousSMul_iff_exists_openSubgroup_smul_eq :
    ContinuousSMul G E ↔ ∃ U : OpenSubgroup G, ∀ g ∈ U, ∀ x : E, g • x = x := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  constructor
  · intro h
    refine ⟨⟨⨅ x : E, MulAction.stabilizer G x, ?_⟩, fun g hg x ↦ ?_⟩
    · change IsOpen ((⨅ x : E, MulAction.stabilizer G x : Subgroup G) : Set G)
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite h
    · exact (Subgroup.mem_iInf.1 hg) x
  · rintro ⟨U, hU⟩ x
    exact Subgroup.isOpen_mono (H₁ := (U : Subgroup G)) (fun g hg ↦ hU g hg x) U.isOpen

end OpenSubgroup

namespace Action

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An object of `Action FintypeCat G`, a finite set with an action of `G` and the discrete
topology, has a continuous action if and only if some open subgroup of `G` acts trivially. -/
theorem isContinuous_iff_exists_openSubgroup (E : Action FintypeCat.{w} G) :
    E.IsContinuous ↔ ∃ U : OpenSubgroup G, ∀ g ∈ U, ∀ x : E.V, (E.ρ g).hom x = x :=
  have : Finite ((forget₂ _ TopCat).obj E) := inferInstanceAs (Finite E.V)
  have : DiscreteTopology ((forget₂ _ TopCat).obj E) := inferInstanceAs (DiscreteTopology E.V)
  continuousSMul_iff_exists_openSubgroup_smul_eq

end Action

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} (s : GeometricPoint X)

/-- **The category `𝒞(X, s)` of finite continuous `π₁(X, s)`-sets.** The finite sets with a left
action of `π₁(X, s)` such that some open subgroup of `π₁(X, s)` acts trivially
(`isContinuous_iff_exists_openSubgroup`), with the `π₁(X, s)`-equivariant maps as morphisms: the
full subcategory of continuous actions in `Action FintypeCat π₁(X, s)`. -/
@[weil "def_fka1_finite_continuous_pi1_set"]
abbrev FiniteContinuousPi1Set : Type _ :=
  ContAction FintypeCat.{w} s.fundamentalGroup

variable {s}

/-- A finite `π₁(X, s)`-set is a finite continuous `π₁(X, s)`-set if and only if some open
subgroup of `π₁(X, s)` acts trivially on it. -/
@[weil "def_fka1_finite_continuous_pi1_set"]
theorem isContinuous_iff_exists_openSubgroup (E : Action FintypeCat.{w} s.fundamentalGroup) :
    E.IsContinuous ↔
      ∃ U : OpenSubgroup s.fundamentalGroup, ∀ g ∈ U, ∀ x : E.V, (E.ρ g).hom x = x :=
  Action.isContinuous_iff_exists_openSubgroup E

/-- Every object of `𝒞(X, s)` has an open subgroup of `π₁(X, s)` acting trivially on it. -/
theorem FiniteContinuousPi1Set.exists_openSubgroup (E : FiniteContinuousPi1Set.{u, w} s) :
    ∃ U : OpenSubgroup s.fundamentalGroup, ∀ g ∈ U, ∀ x : E.obj.V, (E.obj.ρ g).hom x = x :=
  (isContinuous_iff_exists_openSubgroup E.obj).1 E.property

/-- A finite `π₁(X, s)`-set on which some open subgroup acts trivially, as an object of
`𝒞(X, s)`. -/
def FiniteContinuousPi1Set.mk (E : Action FintypeCat.{w} s.fundamentalGroup)
    (h : ∃ U : OpenSubgroup s.fundamentalGroup, ∀ g ∈ U, ∀ x : E.V, (E.ρ g).hom x = x) :
    FiniteContinuousPi1Set.{u, w} s :=
  ⟨E, (isContinuous_iff_exists_openSubgroup E).2 h⟩

@[simp]
theorem FiniteContinuousPi1Set.mk_obj (E : Action FintypeCat.{w} s.fundamentalGroup)
    (h : ∃ U : OpenSubgroup s.fundamentalGroup, ∀ g ∈ U, ∀ x : E.V, (E.ρ g).hom x = x) :
    (FiniteContinuousPi1Set.mk E h).obj = E :=
  rfl

end GeometricPoint

end AlgebraicGeometry

end
