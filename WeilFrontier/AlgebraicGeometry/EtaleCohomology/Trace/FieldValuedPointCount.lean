module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Morphisms.Preimmersion
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentTraceFormulaConclusion

/-!
# Additivity of point counts over a partition into locally closed pieces

Let `X` be a scheme over a field `k` and let `ι_i : Y_i ⟶ X` (`i` in a finite index set) be
preimmersions whose images are pairwise disjoint and cover `X` — for instance the inclusions of
pairwise disjoint locally closed subsets `Y_i` covering `X`, each with its reduced induced
structure. For every field extension `K` of `k`, composing with the `ι_i` is a bijection
`∐ᵢ Y_i(K) ≃ X(K)`: a `K`-valued point of `X` has its image point in exactly one `Y_i`, and
factors uniquely through `ι_i`. Hence, when `X(K)` is finite, `#X(K) = ∑ᵢ #Y_i(K)`. For `X` of
finite type over a finite field `k`, this gives `A_n(X) = ∑ᵢ A_n(Y_i)` for all `n ≥ 1`.

## Main definitions

* `AlgebraicGeometry.fieldValuedPointsSigmaEquivOfIsPreimmersion`: the bijection
  `(Σ i, Y_i(K)) ≃ X(K)`.

## Main results

* `AlgebraicGeometry.pointCount_eq_sum_of_isPreimmersion`: `#X(K) = ∑ᵢ #Y_i(K)` when `X(K)` is
  finite.
* `AlgebraicGeometry.pointCountOfDegree_eq_sum_of_isPreimmersion`: `A_n(X) = ∑ᵢ A_n(Y_i)` for
  `X` of finite type over a finite field.

## Implementation notes

The source states the result for pairwise disjoint locally closed subsets `Y_i` covering `X`,
each with its reduced subscheme structure. We state it for any finite family of preimmersions
`Y_i ⟶ X` with pairwise disjoint images covering `X`; this contains the source's case, since
the inclusion of a locally closed subset with its reduced structure is an immersion, and shows
that the scheme structure on the pieces is irrelevant. Each `Y_i` is a scheme over `k` through
`ι_i ≫ f`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe u v

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {ι : Type v} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, IsPreimmersion (g i)]

/-- For preimmersions `g i : Y i ⟶ X` with pairwise disjoint images covering `X`, composition
with the `g i` is a bijection from the disjoint union of the sets `Y_i(K)` of `K`-valued points
onto `X(K)`. -/
def fieldValuedPointsSigmaEquivOfIsPreimmersion
    (hdisj : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j)))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (g i))
    (K : Type u) [Field K] [Algebra k K] :
    (Σ i, fieldValuedPoints (g i ≫ f) K) ≃ fieldValuedPoints f K :=
  Equiv.ofBijective
    (fun b => ⟨b.2.1 ≫ g b.1, by rw [Category.assoc]; exact b.2.2⟩)
    (by
      constructor
      · rintro ⟨i, b, hb⟩ ⟨i', b', hb'⟩ h
        have h' : b ≫ g i = b' ≫ g i' := congrArg Subtype.val h
        obtain rfl : i = i' := by
          by_contra hne
          refine Set.disjoint_left.1 (hdisj hne) ⟨b default, rfl⟩ ?_
          refine ⟨b' default, ?_⟩
          change (b' ≫ g i').base default = (b ≫ g i).base default
          rw [h']
        obtain rfl : b = b' := (cancel_mono (g i)).1 h'
        rfl
      · rintro ⟨a, ha⟩
        obtain ⟨i, hi⟩ := hcover (a default)
        obtain ⟨⟨b, hb, -⟩, -⟩ :=
          existsUnique_lift_over_of_isPreimmersion f _ (g i) a ha hi
        exact ⟨⟨i, b, by rw [← Category.assoc, hb, ha]⟩, Subtype.ext hb⟩)

/-- Let `g i : Y i ⟶ X` be finitely many preimmersions with pairwise disjoint images covering
`X`. If the set `X(K)` of `K`-valued points of `X` over `k` is finite, then
`#X(K) = ∑ᵢ #Y_i(K)`, each `Y i` being a scheme over `k` through `g i ≫ f`. -/
theorem pointCount_eq_sum_of_isPreimmersion [Fintype ι]
    (hdisj : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j)))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (g i))
    (K : Type u) [Field K] [Algebra k K] [Finite (fieldValuedPoints f K)] :
    pointCount f K = ∑ i, pointCount (g i ≫ f) K := by
  let e := fieldValuedPointsSigmaEquivOfIsPreimmersion f g hdisj hcover K
  have : Finite (Σ i, fieldValuedPoints (g i ≫ f) K) := Finite.of_equiv _ e.symm
  have : ∀ i, Finite (fieldValuedPoints (g i ≫ f) K) := fun i =>
    Finite.of_injective (Sigma.mk (β := fun i => fieldValuedPoints (g i ≫ f) K) i)
      sigma_mk_injective
  classical
  have : ∀ i, Fintype (fieldValuedPoints (g i ≫ f) K) := fun i => Fintype.ofFinite _
  unfold pointCount
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card]

/-- **Additivity of point counts.** Let `X` be a scheme of finite type over a finite field `k`
and `g i : Y i ⟶ X` finitely many preimmersions (e.g. the inclusions of pairwise disjoint
locally closed subsets covering `X`, with their reduced structures) whose images are pairwise
disjoint and cover `X`. Then for every `n ≥ 1`, `A_n(X) = ∑ᵢ A_n(Y_i)`, each `Y i` being a
scheme over `k` through `g i ≫ f`. -/
@[weil "lem_fk0_point_count_additive_locally_closed_partition"]
theorem pointCountOfDegree_eq_sum_of_isPreimmersion [Finite k] [LocallyOfFiniteType f]
    [QuasiCompact f] [Fintype ι]
    (hdisj : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j)))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (g i)) (n : ℕ) [NeZero n] :
    pointCountOfDegree f n = ∑ i, pointCountOfDegree (g i ≫ f) n := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have : Finite (FiniteField.Extension k (ringChar k) n) := inferInstance
  have : Finite (fieldValuedPoints f (ULift.{u} (FiniteField.Extension k (ringChar k) n))) :=
    finite_fieldValuedPoints f _
  exact pointCount_eq_sum_of_isPreimmersion f g hdisj hcover _

end AlgebraicGeometry
