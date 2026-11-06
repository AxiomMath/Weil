module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Brick-wall covers of a square in `ℂ`

Fix a finite set `B₀ ⊆ ℂ`, a half-side `R` and a mesh bound `ρ > 0`. We cover the open square
`(-R, R) ×ℂ (-R, R)` by finitely many open rectangles (each intersected with the square) such that

* no four distinct members meet (the cover has order at most `3`);
* every member has diameter `< ρ`;
* every point of `B₀` lies in exactly one member, every member contains at most one point of `B₀`,
  and two distinct members both meeting `B₀` are disjoint.

The construction is a brick wall. For a mesh `δ`, an overlap `ε < δ / 4` and offsets `t`, `u`,
row `j : ℤ` is the horizontal strip `t + jδ - ε < im z < t + (j + 1)δ + ε`, and the brick `(j, k)`
of row `j` is cut out of it by `u + jδ/2 + kδ - ε < re z < u + jδ/2 + (k + 1)δ + ε`. Consecutive
rows are shifted against each other by `δ / 2`. A point lies in at most two consecutive rows and
in at most two consecutive bricks of each row; if it lay in two bricks of each of two consecutive
rows, it would be `ε`-close to a joint of each row, and these joints are at least `δ / 2 > 2ε`
apart. The offsets are chosen (by countability) so that no point of `B₀` lies on a grid line,
`ε` is then chosen smaller than the distance from `B₀` to the grid lines, and `δ` small against
`ρ` and the distances between the points of `B₀`.

## Main results

* `Complex.exists_brick_cover`: the brick-wall cover of the open square `(-R, R) ×ℂ (-R, R)`.

## Implementation notes

Rectangles are written with Mathlib's `Complex.reProdIm` (`s ×ℂ t`), applied to open intervals.
-/

@[expose] public section

open Set Filter Topology

namespace Complex

namespace BrickCover

/-- A point of the interval `n` of a one-dimensional family of overlapping intervals
`(a + nδ - ε, a + (n + 1)δ + ε)` has index `⌊(x - a - ε)/δ⌋` or that index plus one. -/
theorem eq_floor_or_eq_floor_add_one {a δ ε x : ℝ} {n : ℤ} (hδ : 0 < δ) (hε : 2 * ε < δ)
    (hx : x ∈ Ioo (a + n * δ - ε) (a + (n + 1) * δ + ε)) :
    n = ⌊(x - a - ε) / δ⌋ ∨ n = ⌊(x - a - ε) / δ⌋ + 1 := by
  set y := (x - a - ε) / δ with hy
  have hyδ : y * δ = x - a - ε := by rw [hy]; field_simp
  have e1 : ((n : ℝ) + 1) * δ = n * δ + δ := by ring
  have h1 : y < n + 1 := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h hδ.le
    linarith [hx.2]
  have h2 : (n : ℝ) < y + 1 := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h hδ.le
    have e2 : (y + 1) * δ = y * δ + δ := by ring
    linarith [hx.1]
  have h3 : (⌊y⌋ : ℝ) < (n : ℝ) + 1 := lt_of_le_of_lt (Int.floor_le y) h1
  have h4 : (n : ℝ) < (⌊y⌋ : ℝ) + 2 := by linarith [Int.lt_floor_add_one y]
  have h3' : ⌊y⌋ < n + 1 := by exact_mod_cast h3
  have h4' : n < ⌊y⌋ + 2 := by exact_mod_cast h4
  omega

/-- A point of the interval `n` that keeps distance `≥ ε` from the endpoints' centres
`a + nδ` and `a + (n + 1)δ` determines `n` as `⌊(x - a)/δ⌋`. -/
theorem eq_floor_of_mem_Ioo {a δ ε x : ℝ} {n : ℤ} (hδ : 0 < δ) (hε : 0 < ε)
    (hx : x ∈ Ioo (a + n * δ - ε) (a + (n + 1) * δ + ε))
    (h₁ : ε ≤ |x - a - n * δ|) (h₂ : ε ≤ |x - a - (n + 1) * δ|) :
    n = ⌊(x - a) / δ⌋ := by
  have l : n * δ < x - a := by
    rcases le_or_gt 0 (x - a - n * δ) with h | h
    · rw [abs_of_nonneg h] at h₁; linarith
    · rw [abs_of_neg h] at h₁; linarith [hx.1]
  have r : x - a < (n + 1) * δ := by
    rcases le_or_gt 0 (x - a - (n + 1) * δ) with h | h
    · rw [abs_of_nonneg h] at h₂; linarith [hx.2]
    · rw [abs_of_neg h] at h₂; linarith
  symm
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hδ]; exact l.le
  · rw [div_lt_iff₀ hδ]; exact r

/-- A point of two consecutive intervals is `ε`-close to their common joint. -/
theorem abs_sub_joint_lt {a δ ε x : ℝ} {n : ℤ}
    (h₁ : x ∈ Ioo (a + n * δ - ε) (a + (n + 1) * δ + ε))
    (h₂ : x ∈ Ioo (a + ((n + 1 : ℤ) : ℝ) * δ - ε) (a + (((n + 1 : ℤ) : ℝ) + 1) * δ + ε)) :
    |x - (a + (n + 1) * δ)| < ε := by
  push_cast at h₂
  rw [abs_sub_lt_iff]
  constructor <;> linarith [h₁.2, h₂.1]

/-- Odd multiples of `δ / 2` have absolute value at least `δ / 2`. -/
theorem half_le_abs_half_add_mul {δ : ℝ} (hδ : 0 < δ) (n : ℤ) : δ / 2 ≤ |δ / 2 + n * δ| := by
  rcases le_or_gt 0 n with h | h
  · have : (0 : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    rw [abs_of_neg (by nlinarith)]
    nlinarith

/-- A real number off the lattice `δℤ` keeps a positive distance from it. -/
theorem exists_pos_le_abs_sub_mul {δ x : ℝ} (hδ : 0 < δ) (hx : ∀ n : ℤ, x ≠ n * δ) :
    ∃ η > 0, ∀ n : ℤ, η ≤ |x - n * δ| := by
  set q := x / δ with hq
  have hqδ : x = q * δ := by rw [hq]; field_simp
  have hf : 0 < Int.fract q := by
    rw [Int.fract_pos]
    intro h
    exact hx ⌊q⌋ (by rw [hqδ, ← h])
  have hf1 : Int.fract q < 1 := Int.fract_lt_one q
  have hdec : q = ⌊q⌋ + Int.fract q := (Int.floor_add_fract q).symm
  refine ⟨δ * min (Int.fract q) (1 - Int.fract q), by
    have : 0 < min (Int.fract q) (1 - Int.fract q) := lt_min hf (by linarith)
    positivity, fun n => ?_⟩
  rcases le_or_gt n ⌊q⌋ with h | h
  · have hn : (n : ℝ) ≤ ⌊q⌋ := by exact_mod_cast h
    have hpos : Int.fract q ≤ q - n := by linarith
    have : δ * min (Int.fract q) (1 - Int.fract q) ≤ δ * (q - n) :=
      mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hpos) hδ.le
    have e : x - n * δ = δ * (q - n) := by rw [hqδ]; ring
    rw [e, abs_of_nonneg (by nlinarith)]
    exact this
  · have hn : (⌊q⌋ : ℝ) + 1 ≤ n := by exact_mod_cast h
    have hpos : 1 - Int.fract q ≤ n - q := by linarith
    have : δ * min (Int.fract q) (1 - Int.fract q) ≤ δ * (n - q) :=
      mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hpos) hδ.le
    have e : x - n * δ = -(δ * (n - q)) := by rw [hqδ]; ring
    rw [e, abs_neg, abs_of_nonneg (by nlinarith)]
    exact this

/-- For finitely many points and a step `c > 0` there is an offset `t` such that no
`f z - t` (with `z ∈ B₀`) lies on the lattice `cℤ`. -/
theorem exists_offset (B₀ : Finset ℂ) (f : ℂ → ℝ) (c : ℝ) :
    ∃ t : ℝ, ∀ z ∈ B₀, ∀ n : ℤ, f z - t ≠ n * c := by
  have hc : (⋃ z ∈ (B₀ : Set ℂ), range (fun n : ℤ => f z - n * c)).Countable :=
    B₀.finite_toSet.countable.biUnion fun _ _ => countable_range _
  by_contra h
  push Not at h
  refine Cardinal.not_countable_real (hc.mono fun t _ => ?_)
  obtain ⟨z, hz, n, hn⟩ := h t
  exact mem_biUnion (x := z) hz ⟨n, by simp only; linarith⟩

/-- The brick `p = (j, k)` of the brick wall with offsets `u`, `t`, mesh `δ` and overlap `ε`. -/
def brick (u t δ ε : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  Ioo (u + p.1 * (δ / 2) + p.2 * δ - ε) (u + p.1 * (δ / 2) + (p.2 + 1) * δ + ε) ×ℂ
    Ioo (t + p.1 * δ - ε) (t + (p.1 + 1) * δ + ε)

theorem mem_brick {u t δ ε : ℝ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ brick u t δ ε p ↔
      z.re ∈ Ioo (u + p.1 * (δ / 2) + p.2 * δ - ε) (u + p.1 * (δ / 2) + (p.2 + 1) * δ + ε) ∧
      z.im ∈ Ioo (t + p.1 * δ - ε) (t + (p.1 + 1) * δ + ε) :=
  mem_reProdIm

/-- Two points of one brick are at distance at most `3δ` when `ε < δ / 4`. -/
theorem dist_le_of_mem_brick {u t δ ε : ℝ} (hε : ε < δ / 4) {p : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ brick u t δ ε p) (hw : w ∈ brick u t δ ε p) : dist z w ≤ 3 * δ := by
  rw [mem_brick] at hz hw
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : ((p.2 : ℝ) + 1) * δ = p.2 * δ + δ := by ring
  have e2 : ((p.1 : ℝ) + 1) * δ = p.1 * δ + δ := by ring
  have hre : |(z - w).re| ≤ 3 / 2 * δ := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have him : |(z - w).im| ≤ 3 / 2 * δ := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  linarith

/-- No point lies in four distinct bricks. -/
theorem not_forall_mem_brick {u t δ ε : ℝ} (hδ : 0 < δ) (hε : ε < δ / 4) (z : ℂ) (m c c' : ℤ)
    (h₁ : z ∈ brick u t δ ε (m, c)) (h₂ : z ∈ brick u t δ ε (m, c + 1))
    (h₃ : z ∈ brick u t δ ε (m + 1, c')) (h₄ : z ∈ brick u t δ ε (m + 1, c' + 1)) : False := by
  rw [mem_brick] at h₁ h₂ h₃ h₄
  have j₁ := abs_sub_joint_lt (a := u + m * (δ / 2)) (n := c) h₁.1 h₂.1
  have j₂ := abs_sub_joint_lt (a := u + ((m + 1 : ℤ) : ℝ) * (δ / 2)) (n := c') h₃.1 h₄.1
  have key := half_le_abs_half_add_mul hδ (c' - c)
  have e : δ / 2 + ((c' - c : ℤ) : ℝ) * δ =
      (z.re - (u + m * (δ / 2) + (c + 1) * δ)) -
        (z.re - (u + ((m + 1 : ℤ) : ℝ) * (δ / 2) + (c' + 1) * δ)) := by push_cast; ring
  rw [e] at key
  have := abs_sub (z.re - (u + m * (δ / 2) + (c + 1) * δ))
    (z.re - (u + ((m + 1 : ℤ) : ℝ) * (δ / 2) + (c' + 1) * δ))
  linarith

end BrickCover

open BrickCover in
/-- **Brick-wall cover of a square.** For a finite `B₀ ⊆ ℂ`, `R : ℝ` and `ρ > 0`, the open square
`(-R, R) ×ℂ (-R, R)` is covered by finitely many open rectangles intersected with the square, of
order at most `3` (no four distinct members meet) and diameter `< ρ`, such that every point of
`B₀` lies in exactly one member, every member contains at most one point of `B₀`, and distinct
members meeting `B₀` are disjoint. -/
theorem exists_brick_cover (B₀ : Finset ℂ) (R : ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (ι : Type) (_ : Fintype ι) (V : ι → Set ℂ),
      (∀ i, ∃ a b c d : ℝ,
        V i = (Ioo a b ×ℂ Ioo c d) ∩ (Ioo (-R) R ×ℂ Ioo (-R) R)) ∧
      (⋃ i, V i) = Ioo (-R) R ×ℂ Ioo (-R) R ∧
      (∀ s : Finset ι, 3 < s.card → ⋂ i ∈ s, V i = ∅) ∧
      (∀ i, Metric.diam (V i) < ρ) ∧
      (∀ z ∈ B₀, ∀ i j, z ∈ V i → z ∈ V j → i = j) ∧
      (∀ i, (V i ∩ B₀).Subsingleton) ∧
      (∀ i j, i ≠ j → (V i ∩ B₀).Nonempty → (V j ∩ B₀).Nonempty → Disjoint (V i) (V j)) := by
  -- the separation `m` of the points of `B₀`
  obtain ⟨m, hmB, hm⟩ : ∃ m : ℝ, (∀ z ∈ B₀, ∀ w ∈ B₀, z ≠ w → m ≤ dist z w) ∧ 0 < m := by
    have : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ z ∈ B₀, ∀ w ∈ B₀, z ≠ w → η ≤ dist z w := by
      rw [eventually_all_finset]
      intro z _
      rw [eventually_all_finset]
      intro w _
      by_cases hzw : z = w
      · exact Eventually.of_forall fun _ h => absurd hzw h
      · filter_upwards [Ioc_mem_nhdsGT (dist_pos.2 hzw)] with η hη _ using hη.2
    exact (this.and self_mem_nhdsWithin).exists
  -- the mesh `δ`
  obtain ⟨δ, hδρ, hδm, hδ⟩ : ∃ δ : ℝ, 4 * δ < ρ ∧ 7 * δ < m ∧ 0 < δ := by
    have : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 4 * δ < ρ ∧ 7 * δ < m := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (ρ / 4) (m / 7) by positivity)]
        with δ hδ
      exact ⟨by linarith [hδ.2.trans_le (min_le_left _ _)],
        by linarith [hδ.2.trans_le (min_le_right _ _)]⟩
    obtain ⟨δ, h, hδ⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨δ, h.1, h.2, hδ⟩
  -- the offsets `t` (rows) and `u` (joints)
  obtain ⟨t, ht⟩ := exists_offset B₀ Complex.im δ
  obtain ⟨u, hu⟩ := exists_offset B₀ Complex.re (δ / 2)
  -- the overlap `ε`
  obtain ⟨ε, ⟨hεδ, hεim, hεre⟩, hε⟩ : ∃ ε : ℝ, (ε < δ / 4 ∧
      (∀ z ∈ B₀, ∀ n : ℤ, ε ≤ |z.im - t - n * δ|) ∧
      (∀ z ∈ B₀, ∀ n : ℤ, ε ≤ |z.re - u - n * (δ / 2)|)) ∧ 0 < ε := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ / 4 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ / 4 by positivity)] with ε hε
      exact hε.2
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ B₀, ∀ n : ℤ, ε ≤ |z.im - t - n * δ| := by
      rw [eventually_all_finset]
      intro z hz
      obtain ⟨η, hη, h⟩ := exists_pos_le_abs_sub_mul hδ (ht z hz)
      filter_upwards [Ioc_mem_nhdsGT hη] with ε hε n using hε.2.trans (h n)
    have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ B₀, ∀ n : ℤ, ε ≤ |z.re - u - n * (δ / 2)| := by
      rw [eventually_all_finset]
      intro z hz
      obtain ⟨η, hη, h⟩ := exists_pos_le_abs_sub_mul (half_pos hδ) (hu z hz)
      filter_upwards [Ioc_mem_nhdsGT hη] with ε hε n using hε.2.trans (h n)
    exact ((h1.and (h2.and h3)).and self_mem_nhdsWithin).exists
  -- the index set
  set S : Set ℂ := Ioo (-R) R ×ℂ Ioo (-R) R with hS
  set J₀ : ℤ := ⌊(-R - t) / δ⌋
  set J₁ : ℤ := ⌊(R - t) / δ⌋
  set K₀ : ℤ := ⌊(-R - u - J₁ * (δ / 2)) / δ⌋
  set K₁ : ℤ := ⌊(R - u - J₀ * (δ / 2)) / δ⌋
  let T : Finset (ℤ × ℤ) := Finset.Icc J₀ J₁ ×ˢ Finset.Icc K₀ K₁
  let V : T → Set ℂ := fun i => brick u t δ ε i.1 ∩ S
  have hdist : ∀ i, ∀ z ∈ V i, ∀ w ∈ V i, dist z w ≤ 3 * δ := fun i z hz w hw =>
    dist_le_of_mem_brick hεδ hz.1 hw.1
  have huniq : ∀ z ∈ B₀, ∀ i j : T, z ∈ V i → z ∈ V j → i = j := by
    intro z hz i j hi hj
    have row : ∀ p : ℤ × ℤ, z ∈ brick u t δ ε p → p.1 = ⌊(z.im - t) / δ⌋ := by
      intro p hp
      rw [mem_brick] at hp
      refine eq_floor_of_mem_Ioo hδ hε hp.2 (hεim z hz _) ?_
      have := hεim z hz (p.1 + 1)
      push_cast at this
      exact this
    have col : ∀ p : ℤ × ℤ, z ∈ brick u t δ ε p →
        p.2 = ⌊(z.re - (u + p.1 * (δ / 2))) / δ⌋ := by
      intro p hp
      rw [mem_brick] at hp
      refine eq_floor_of_mem_Ioo hδ hε hp.1 ?_ ?_
      · have := hεre z hz (p.1 + 2 * p.2)
        convert this using 2
        push_cast
        ring
      · have := hεre z hz (p.1 + 2 * p.2 + 2)
        convert this using 2
        push_cast
        ring
    have h1 := row _ hi.1
    have h2 := row _ hj.1
    have h3 := col _ hi.1
    have h4 := col _ hj.1
    have e : i.1.1 = j.1.1 := by rw [h1, h2]
    apply Subtype.ext
    apply Prod.ext e
    rw [h3, h4, e]
  have hunion : (⋃ i, V i) = S := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_right
    · intro z hz
      have hz' := hz
      rw [hS, mem_reProdIm] at hz'
      obtain ⟨⟨hre1, hre2⟩, him1, him2⟩ := hz'
      set j : ℤ := ⌊(z.im - t) / δ⌋ with hjdef
      set k : ℤ := ⌊(z.re - u - j * (δ / 2)) / δ⌋ with hkdef
      have hj0 : J₀ ≤ j := Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 (by linarith))
      have hj1 : j ≤ J₁ := Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 (by linarith))
      have hj0r : (J₀ : ℝ) * (δ / 2) ≤ j * (δ / 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj0) (by positivity)
      have hj1r : (j : ℝ) * (δ / 2) ≤ J₁ * (δ / 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj1) (by positivity)
      have hk0 : K₀ ≤ k := Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 (by linarith))
      have hk1 : k ≤ K₁ := Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 (by linarith))
      have hjl : (j : ℝ) * δ ≤ z.im - t := by
        have := Int.floor_le ((z.im - t) / δ)
        rwa [le_div_iff₀ hδ] at this
      have hju : z.im - t < (j + 1) * δ := by
        have := Int.lt_floor_add_one ((z.im - t) / δ)
        rwa [div_lt_iff₀ hδ] at this
      have hkl : (k : ℝ) * δ ≤ z.re - u - j * (δ / 2) := by
        have := Int.floor_le ((z.re - u - j * (δ / 2)) / δ)
        rwa [le_div_iff₀ hδ] at this
      have hku : z.re - u - j * (δ / 2) < (k + 1) * δ := by
        have := Int.lt_floor_add_one ((z.re - u - j * (δ / 2)) / δ)
        rwa [div_lt_iff₀ hδ] at this
      refine mem_iUnion.2 ⟨⟨(j, k), Finset.mem_product.2
        ⟨Finset.mem_Icc.2 ⟨hj0, hj1⟩, Finset.mem_Icc.2 ⟨hk0, hk1⟩⟩⟩, ?_, hz⟩
      rw [mem_brick]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only <;> linarith
  have horder : ∀ s : Finset T, 3 < s.card → ⋂ i ∈ s, V i = ∅ := by
    intro s hs
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_iInter₂] at hz
    let m : ℤ := ⌊(z.im - t - ε) / δ⌋
    let c : ℤ → ℤ := fun j => ⌊(z.re - (u + j * (δ / 2)) - ε) / δ⌋
    let Q : Finset (ℤ × ℤ) :=
      {(m, c m), (m, c m + 1), (m + 1, c (m + 1)), (m + 1, c (m + 1) + 1)}
    have hQ : ∀ i ∈ s, (i : ℤ × ℤ) ∈ Q := by
      rintro ⟨⟨j, k⟩, hjk⟩ hi
      have hb := (hz _ hi).1
      rw [mem_brick] at hb
      have hr : j = m ∨ j = m + 1 := eq_floor_or_eq_floor_add_one hδ (by linarith) hb.2
      have hc : k = c j ∨ k = c j + 1 := eq_floor_or_eq_floor_add_one hδ (by linarith) hb.1
      simp only [Q, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      rcases hr with rfl | rfl <;> rcases hc with rfl | rfl <;> simp
    have hnot : ∃ q ∈ Q, ∀ i ∈ s, (i : ℤ × ℤ) ≠ q := by
      by_contra h
      push Not at h
      have mem : ∀ q ∈ Q, z ∈ brick u t δ ε q := by
        intro q hq
        obtain ⟨i, hi, rfl⟩ := h q hq
        exact (hz i hi).1
      exact not_forall_mem_brick hδ hεδ z m (c m) (c (m + 1)) (mem _ (by simp [Q]))
        (mem _ (by simp [Q])) (mem _ (by simp [Q])) (mem _ (by simp [Q]))
    obtain ⟨q, hq, hqs⟩ := hnot
    have h1 : s.card ≤ (Q.erase q).card := by
      refine Finset.card_le_card_of_injOn (fun i => (i : ℤ × ℤ)) ?_ Subtype.val_injective.injOn
      intro i hi
      exact Finset.mem_erase.2 ⟨hqs i hi, hQ i hi⟩
    have h2 : (Q.erase q).card = Q.card - 1 := Finset.card_erase_of_mem hq
    have h3 : Q.card ≤ 4 := Finset.card_le_four
    omega
  refine ⟨T, inferInstance, V, fun i => ⟨_, _, _, _, rfl⟩, hunion, horder, fun i =>
    (Metric.diam_le_of_forall_dist_le (by positivity) (hdist i)).trans_lt (by linarith),
    huniq, ?_, ?_⟩
  · intro i z hz w hw
    by_contra hzw
    have := hmB z hz.2 w hw.2 hzw
    have := hdist i z hz.1 w hw.1
    linarith
  · rintro i j hij ⟨z, hzi, hzB⟩ ⟨w, hwj, hwB⟩
    rw [Set.disjoint_left]
    intro x hxi hxj
    by_cases hzw : z = w
    · subst hzw
      exact hij (huniq z hzB i j hzi hwj)
    · have := hmB z hzB w hwB hzw
      have := hdist i z hzi x hxi
      have := hdist j x hxj w hwj
      have := dist_triangle z x w
      linarith

end Complex
