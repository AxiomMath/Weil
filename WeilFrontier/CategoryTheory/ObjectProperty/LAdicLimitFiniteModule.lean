module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.ObjectProperty.LAdicSystem
public import WeilFrontier.Defs.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The projective limit of an `l`-adic system is a finitely generated module

Let `Λ` be a commutative ring, `l ∈ Λ`, and let `F = (F_n, u_n)` be an `l`-adic system of
`Λ`-modules. Then every projection `π_n : lim F → F_n` is surjective, and if `Λ` is
`l`-adically precomplete (for instance `Λ = ℤ_l`), the projective limit `M = lim F` is a finitely
generated `Λ`-module.

Surjectivity of the projections: an element of `F_n` is lifted step by step along the
surjective transition maps `u_{m+1}`. Finite generation: lifts `ẽ_1, …, ẽ_k ∈ M` of generators
`e_1, …, e_k` of `F_0` generate every `F_n` after projection, since their projections generate
`F_n` modulo `l F_n` and `l^{n+1} F_n = 0`. Given `x ∈ M`, one finds compatible coefficient
vectors `c^{(n)} ∈ Λ^k`, with `π_n(x) = ∑ c^{(n)}_i π_n(ẽ_i)` and
`c^{(n+1)} ≡ c^{(n)} mod l^{n+1}`; their `l`-adic limit `c ∈ Λ^k` gives `x = ∑ c_i ẽ_i`.

## Main results

* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.surjective_sections_apply`: every projection
  `π_n : lim F → F_n` of an `l`-adic system is surjective.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.finite_sectionsSubmodule`: over an
  `l`-adically precomplete ring, the projective limit of an `l`-adic system is a finitely
  generated module.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.finite_sectionsSubmodule_padicInt`: the case
  `Λ = ℤ_l` of the source.

## Implementation notes

The source takes `Λ = ℤ_l`; the finiteness statement is proved for every commutative ring that
is precomplete for the ideal `(l)`, which is what the passage from the coefficient vectors
`c^{(n)}` to their limit uses (the source's identification `lim_n Λ_n^k = Λ^k`). Without it the
statement fails (`Λ = ℤ`, `F_n = ℤ/l^{n+1}` has limit `ℤ_l`). The source deduces surjectivity
of `Λ^k → M` from exactness of the projective limit on Mittag-Leffler systems; here the
coefficient vectors are constructed directly by induction on `n`, which is the same argument
written out. The projective limit is `ModuleCat.sectionsSubmodule F.obj`, the object of the
projective-limit functor `CategoryTheory.ProjectiveSystem.ArCategory.limFunctor`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

namespace IsLAdicSystem

variable {F : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F)
include hF

omit hF in
/-- An element of `lim F` is compatible with the maps `F_a → F_b`, `b ≤ a`. -/
lemma mapLE_apply_sections (x : ModuleCat.sectionsSubmodule F.obj) {a b : ℤ} (h : b ≤ a) :
    (F.mapLE h).hom (x.1 (op a)) = x.1 (op b) :=
  x.2 (homOfLE h).op

omit hF in
private lemma mapLE_apply_mapLE {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (y : F.term c) :
    (F.mapLE hab).hom ((F.mapLE hbc).hom y) = (F.mapLE (hab.trans hbc)).hom y := by
  rw [← F.mapLE_comp hab hbc]
  rfl

/-- Every projection `π_n : lim F → F_n` of an `l`-adic system is surjective. -/
@[weil "lem_fk112_l_adic_limit_finite_module"]
theorem surjective_sections_apply (n : ℤ) :
    Function.Surjective fun x : ModuleCat.sectionsSubmodule F.obj => x.1 (op n) := by
  intro y
  rcases lt_or_ge n 0 with hn | hn
  · refine ⟨0, ?_⟩
    exact ((ModuleCat.isZero_iff_subsingleton.1 (hF.isZero_of_neg n hn)).elim _ _)
  obtain ⟨n₀, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  -- lift `y` step by step along the surjective transition maps
  let seq : (k : ℕ) → F.term (n₀ + k : ℕ) := fun k =>
    Nat.rec (motive := fun k => F.term (n₀ + k : ℕ)) y
      (fun k z => Classical.choose (hF.surjective (n₀ + k) z)) k
  have seq_succ : ∀ k : ℕ,
      (F.mapLE (m := (n₀ + k : ℕ)) (n := (n₀ + k + 1 : ℕ)) (by omega)).hom (seq (k + 1)) =
        seq k :=
    fun k => Classical.choose_spec (hF.surjective (n₀ + k) (seq k))
  have seq_mapLE : ∀ j k : ℕ, (h : j ≤ k) →
      (F.mapLE (m := (n₀ + j : ℕ)) (n := (n₀ + k : ℕ)) (by omega)).hom (seq k) = seq j := by
    intro j k h
    induction k, h using Nat.le_induction with
    | base =>
      change (F.obj.map (𝟙 _)).hom (seq j) = seq j
      simp
    | succ k hjk ih =>
      rw [← ih, ← seq_succ k, mapLE_apply_mapLE]
  let x : ∀ m : ℤᵒᵖ, F.obj.obj m := fun m =>
    (F.mapLE (m := m.unop) (n := (n₀ + m.unop.toNat : ℕ)) (by omega)).hom (seq m.unop.toNat)
  have hx : x ∈ ModuleCat.sectionsSubmodule F.obj := by
    rintro ⟨a⟩ ⟨b⟩ h
    have hba : b ≤ a := leOfHom h.unop
    obtain rfl : h = (homOfLE hba).op := Subsingleton.elim _ _
    change (F.mapLE hba).hom ((F.mapLE _).hom (seq a.toNat)) =
      (F.mapLE _).hom (seq b.toNat)
    rw [mapLE_apply_mapLE, ← seq_mapLE b.toNat a.toNat (by omega), mapLE_apply_mapLE]
  refine ⟨⟨x, hx⟩, ?_⟩
  exact seq_mapLE 0 n₀ (Nat.zero_le _)

/-- If the projections to `F_0` of finitely many `ẽ_i ∈ lim F` generate `F_0`, then their
projections to `F_n` generate `F_n` for every `n ≥ 0`. -/
lemma span_range_sections_apply_eq_top {k : ℕ} (e : Fin k → ModuleCat.sectionsSubmodule F.obj)
    (he : Submodule.span Λ (Set.range fun i => (e i).1 (op ((0 : ℕ) : ℤ))) = ⊤) (n : ℕ) :
    Submodule.span Λ (Set.range fun i => (e i).1 (op (n : ℤ))) = ⊤ := by
  induction n with
  | zero => exact he
  | succ n ih =>
    set S := Submodule.span Λ (Set.range fun i => (e i).1 (op ((n + 1 : ℕ) : ℤ)))
    -- every element of `F_{n+1}` lies in `S + l^{n+1} F_{n+1}`
    have key : ∀ z : F.term (n + 1 : ℕ), ∃ s ∈ S, ∃ w : F.term (n + 1 : ℕ),
        z = s + l ^ (n + 1) • w := by
      intro z
      have hmem : (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom z ∈
          Submodule.span Λ (Set.range fun i => (e i).1 (op (n : ℤ))) := by
        rw [ih]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 hmem
      refine ⟨∑ i, c i • (e i).1 (op ((n + 1 : ℕ) : ℤ)),
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
        ?_⟩
      have hz : (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom
          (z - ∑ i, c i • (e i).1 (op ((n + 1 : ℕ) : ℤ))) = 0 := by
        simp only [map_sub, map_sum, map_smul, mapLE_apply_sections]
        rw [hc, sub_self]
      obtain ⟨w, hw⟩ := (hF.mem_ker_iff n _).1 hz
      exact ⟨w, by rw [hw]; abel⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨s, hs, w, rfl⟩ := key z
    obtain ⟨s', hs', w', rfl⟩ := key w
    have h0 : l ^ (n + 1) • l ^ (n + 1) • w' = 0 := by
      rw [smul_smul, ← pow_add, show n + 1 + (n + 1) = n + (n + 1 + 1) by omega, pow_add,
        mul_smul, hF.pow_smul_eq_zero (n + 1) w', smul_zero]
    rw [smul_add, h0, add_zero]
    exact S.add_mem hs (S.smul_mem _ hs')

/-- Given `π_n(x) = ∑ c_i π_n(ẽ_i)`, there are coefficients `c' ≡ c mod l^{n+1}` with
`π_{n+1}(x) = ∑ c'_i π_{n+1}(ẽ_i)`. -/
lemma exists_coeff_succ {k : ℕ} (e : Fin k → ModuleCat.sectionsSubmodule F.obj)
    (he : ∀ n : ℕ, Submodule.span Λ (Set.range fun i => (e i).1 (op (n : ℤ))) = ⊤)
    (x : ModuleCat.sectionsSubmodule F.obj) (n : ℕ) (c : Fin k → Λ)
    (hc : ∑ i, c i • (e i).1 (op (n : ℤ)) = x.1 (op (n : ℤ))) :
    ∃ c' : Fin k → Λ, ∑ i, c' i • (e i).1 (op ((n + 1 : ℕ) : ℤ)) = x.1 (op ((n + 1 : ℕ) : ℤ)) ∧
      ∀ i, ∃ d : Λ, c' i = c i + l ^ (n + 1) * d := by
  have hy : (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom
      (x.1 (op ((n + 1 : ℕ) : ℤ)) - ∑ i, c i • (e i).1 (op ((n + 1 : ℕ) : ℤ))) = 0 := by
    simp only [map_sub, map_sum, map_smul, mapLE_apply_sections]
    rw [hc, sub_self]
  obtain ⟨z, hz⟩ := (hF.mem_ker_iff n _).1 hy
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1
    ((he (n + 1)).symm ▸ Submodule.mem_top : z ∈
      Submodule.span Λ (Set.range fun i => (e i).1 (op ((n + 1 : ℕ) : ℤ))))
  refine ⟨fun i => c i + l ^ (n + 1) * d i, ?_, fun i => ⟨d i, rfl⟩⟩
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hd, hz]
  abel

/-- Over an `l`-adically precomplete ring, the projective limit `lim F` of an `l`-adic system
is a finitely generated `Λ`-module. -/
@[weil "lem_fk112_l_adic_limit_finite_module"]
theorem finite_sectionsSubmodule [IsPrecomplete (Ideal.span {l}) Λ] :
    Module.Finite Λ (ModuleCat.sectionsSubmodule F.obj) := by
  set I : Ideal Λ := Ideal.span {l}
  have : IsNoetherian Λ (F.term ((0 : ℕ) : ℤ)) :=
    ((isFiniteLength_iff_isNoetherian_isArtinian).1 (hF.isFiniteLength _)).1
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := Λ) (M := F.term ((0 : ℕ) : ℤ))
  choose e he using fun i => hF.surjective_sections_apply ((0 : ℕ) : ℤ) (g i)
  have hspan := hF.span_range_sections_apply_eq_top e (by
    rw [show (fun i => (e i).1 (op ((0 : ℕ) : ℤ))) = g from funext he]; exact hg)
  -- every element of `lim F` is a `Λ`-linear combination of the `e i`
  suffices hsurj : ∀ x : ModuleCat.sectionsSubmodule F.obj, ∃ L : Fin k → Λ, ∑ i, L i • e i = x by
    refine ⟨Submodule.fg_iff_exists_fin_generating_family.2 ⟨k, e, eq_top_iff.2 fun x _ => ?_⟩⟩
    obtain ⟨L, rfl⟩ := hsurj x
    exact (Submodule.mem_span_range_iff_exists_fun Λ).2 ⟨L, rfl⟩
  intro x
  -- compatible coefficient vectors `c n` with `π_n(x) = ∑ (c n)_i π_n(e_i)`
  let P : ℕ → (Fin k → Λ) → Prop := fun n c => ∑ i, c i • (e i).1 (op (n : ℤ)) = x.1 (op (n : ℤ))
  have h0 : ∃ c, P 0 c := (Submodule.mem_span_range_iff_exists_fun Λ).1
    ((hspan 0).symm ▸ Submodule.mem_top)
  let seq : (n : ℕ) → {c // P n c} := fun n =>
    Nat.rec (motive := fun n => {c // P n c}) ⟨h0.choose, h0.choose_spec⟩
      (fun n c => ⟨(hF.exists_coeff_succ e hspan x n c.1 c.2).choose,
        (hF.exists_coeff_succ e hspan x n c.1 c.2).choose_spec.1⟩) n
  have seq_succ : ∀ n i, ∃ d : Λ, (seq (n + 1)).1 i = (seq n).1 i + l ^ (n + 1) * d :=
    fun n => (hF.exists_coeff_succ e hspan x n (seq n).1 (seq n).2).choose_spec.2
  have seq_le : ∀ i m n, m ≤ n → ∃ d : Λ, (seq n).1 i = (seq m).1 i + l ^ (m + 1) * d := by
    intro i m n h
    induction n, h using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨d, hd⟩ := ih
      obtain ⟨d', hd'⟩ := seq_succ n i
      refine ⟨d + l ^ (n - m) * d', ?_⟩
      rw [hd', hd, mul_add, ← mul_assoc, ← pow_add, show m + 1 + (n - m) = n + 1 by omega]
      ring
  have hpow : ∀ (m : ℕ) (a : Λ), l ^ m * a ∈ (I ^ m • ⊤ : Submodule Λ Λ) := fun m a =>
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self l) m) trivial
  have hlim : ∀ i, ∃ L : Λ, ∀ n, (seq n).1 i ≡ L [SMOD (I ^ n • ⊤ : Submodule Λ Λ)] := by
    intro i
    refine IsPrecomplete.prec inferInstance fun {m n} h => ?_
    obtain ⟨d, hd⟩ := seq_le i m n h
    rw [SModEq.sub_mem, hd, sub_add_cancel_left]
    convert hpow m (-(l * d)) using 1
    ring
  choose L hL using hlim
  refine ⟨L, ?_⟩
  -- all projections of `x - ∑ L i • e i` vanish
  rw [← sub_eq_zero]
  apply Subtype.ext
  funext ⟨m⟩
  rcases lt_or_ge m 0 with hm | hm
  · exact (ModuleCat.isZero_iff_subsingleton.1 (hF.isZero_of_neg m hm)).elim _ _
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have hcoeff : ∀ i, ∃ t : Λ, (seq n).1 i - L i = l ^ (n + 1) * t := by
    intro i
    have h1 := (SModEq.sub_mem.1 (hL i (n + 1)))
    rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, Ideal.span_singleton_pow,
      Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨d, hd⟩ := seq_succ n i
    refine ⟨t - d, ?_⟩
    rw [mul_sub, mul_comm _ t, ht, hd]
    ring
  change (∑ i, L i • e i).1 (op (n : ℤ)) - x.1 (op (n : ℤ)) = 0
  rw [← (seq n).2]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨t, ht⟩ := hcoeff i
  rw [← neg_sub, ht, neg_smul, mul_comm, mul_smul, hF.pow_smul_eq_zero n, smul_zero, neg_zero]

omit hF in
/-- The projective limit of an `l`-adic system of `ℤ_l`-modules is a finitely generated
`ℤ_l`-module. -/
@[weil "lem_fk112_l_adic_limit_finite_module"]
theorem finite_sectionsSubmodule_padicInt {p : ℕ} [Fact p.Prime] {F : LAdic.{v} p}
    (hF : IsLAdicSystem F) : Module.Finite ℤ_[p] (ModuleCat.sectionsSubmodule F.obj) :=
  have : IsPrecomplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  hF.finite_sectionsSubmodule

end IsLAdicSystem

end ProjectiveSystem

end CategoryTheory
