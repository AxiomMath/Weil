module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedAlternatingComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.VanishingAboveCardinality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisForAbelianSheaves

/-!
# Cohomology of intervals with constant coefficients

Let `T ⊆ ℝ` be order-connected (an interval of any kind: open, closed, half-open, bounded or not)
and let `A` be an abelian group. Then the sheaf cohomology of the constant sheaf `A` on `T`
vanishes in every positive degree, and its global sections are `A` when `T` is nonempty. In
particular `Hⁿ([0, 1], A) = 0` for `n ≥ 1` and `H⁰([0, 1], A) ≅ A`, and the same holds for every
compact interval `[a, b]` with `a ≤ b`.

The proof is Cartan's criterion on a basis (Stacks 01EW): for the basis of order-connected opens
of `T`, which is closed under finite intersections, it suffices to exhibit a cofinal family of
covers by members of the basis with vanishing positive-degree Čech cohomology. The family used is
that of *chain covers*: covers `(U k)_{k ∈ ℤ}` by order-connected opens with `U i ∩ U j = ∅` as soon
as `i + 2 ≤ j`.

* Cofinality. Given an open cover `O` of an order-connected open `V`, a Lebesgue radius
  `radius O : T → ℝ` is `1`-Lipschitz and positive on `V`. Stepping from a base point by a quarter
  of the radius in both directions gives a strictly increasing `t : ℤ → ℝ` which exhausts `V`, and
  the sets `{x ∈ T | t (k - 1) < x < t (k + 1)}` form a chain cover of `V` refining `O`.
* Čech vanishing. The ordered Čech complex of a chain cover (Stacks 01FJ) has zero terms in
  degrees `≥ 2`, the intersections being empty, and in degree `1` every cochain is a coboundary,
  by solving `b (k + 1) - b k = c (k, k + 1)` recursively along `ℤ`. This uses only that
  restriction of the sheaf from `U k` and from `U (k + 1)` onto `U k ∩ U (k + 1)` is surjective,
  which holds for the constant sheaf because every section of a constant sheaf over a
  preconnected open is constant.

## Main results

* `Weil.ConstantSheafSections.exists_eq_constSection`: over a preconnected open, every section
  of a constant abelian sheaf is constant; `constSection_bijective` for connected opens.
* `Weil.ChainCech.isZero_orderedCechComplex_homology`: positive-degree Čech cohomology of a
  chain cover vanishes.
* `Weil.IntervalCohomology.chainCovers_cofinal`: chain covers are cofinal among covers of
  order-connected opens of an interval.
* `Weil.IntervalCohomology.isZero_H'_constantSheaf`: `Hⁿ(V, A) = 0`, `n > 0`, for every
  order-connected open `V` of an interval `T`.
* `Weil.IntervalCohomology.subsingleton_H_constantSheaf` and
  `Weil.IntervalCohomology.constantSheafHZeroAddEquiv`: `Hⁿ(T, A) = 0` for `n > 0`
  and `H⁰(T, A) ≃+ A` for a nonempty interval `T`.
* `unitInterval.subsingleton_H_constantSheaf`, `unitInterval.constantSheafHZeroAddEquiv`:
  the case of `[0, 1]`.
* `Set.Icc.subsingleton_H_constantSheaf`, `Set.Icc.constantSheafHZeroAddEquiv`: the case of
  a compact interval `[a, b]`, `a ≤ b`.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext` groups out of the constant sheaf
`ℤ`, for abelian sheaves on the site of opens and coefficients in `AddCommGrpCat.{0}`. The
statements over an open `V` use `CategoryTheory.Sheaf.H'`, and the passage to `Sheaf.H` at the
top open is `Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top`.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u



namespace Weil.ConstantSheafSections

variable {X : TopCat.{u}} (A : AddCommGrpCat.{u})

/-- The constant presheaf. -/
abbrev constPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const _).obj A

/-- The constant sheaf, as a sheaf on the opens of `X`. -/
noncomputable abbrev constSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A

/-- The comparison map from the constant presheaf to the constant sheaf. -/
noncomputable abbrev toConst : constPresheaf (X := X) A ⟶ (constSheaf (X := X) A).presheaf :=
  toSheafify (Opens.grothendieckTopology X) (constPresheaf A)

/-- The section of the constant sheaf over `U` with constant value `a`. -/
noncomputable def constSection (U : Opens X) (a : A) :
    (constSheaf (X := X) A).presheaf.obj (op U) :=
  (toConst A).app (op U) a

/-- Restricting a constant section gives the constant section with the same value. -/
theorem constSection_res {U V : Opens X} (h : V ≤ U) (a : A) :
    (constSheaf (X := X) A).presheaf.map (homOfLE h).op (constSection A U a) =
      constSection A V a := by
  have := ConcreteCategory.congr_hom ((toConst (X := X) A).naturality (homOfLE h).op) a
  simpa [constSection] using this.symm

/-- The stalk of the constant presheaf with value `A` is `A`. -/
theorem constPresheaf_germ_top_bijective (x : X) :
    Function.Bijective ((constPresheaf (X := X) A).germ ⊤ x (Opens.mem_top x)) := by
  constructor
  · intro a b hab
    obtain ⟨W, _, iU, iV, e⟩ :=
      (constPresheaf (X := X) A).germ_eq x (Opens.mem_top x) (Opens.mem_top x) a b hab
    simpa using e
  · intro t
    obtain ⟨U, hx, s, rfl⟩ := (constPresheaf (X := X) A).exists_germ_eq t
    refine ⟨s, ?_⟩
    have := (constPresheaf (X := X) A).germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx s
    simpa using this.symm

/-- The germ of a constant section only depends on its value. -/
theorem germ_constSection (U : Opens X) (x : X) (hx : x ∈ U) (a : A) :
    (constSheaf (X := X) A).presheaf.germ U x hx (constSection A U a) =
      (constSheaf (X := X) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ a) := by
  rw [← constSection_res A (le_top : U ≤ ⊤) a, TopCat.Presheaf.germ_res_apply]

/-- The germ at `x` of the constant section with value `a`, as a map out of `A`: it is a
bijection onto the stalk. -/
theorem germ_constSection_top_bijective (x : X) :
    Function.Bijective (fun a : A =>
      (constSheaf (X := X) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ a)) := by
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (constPresheaf (X := X) A)
  have hb := ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (constPresheaf (X := X) A)))
  have hfun : (fun a : A =>
      (constSheaf (X := X) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ a)) =
      (fun t => ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) (constPresheaf (X := X) A))) t) ∘
      (fun a => (constPresheaf (X := X) A).germ ⊤ x (Opens.mem_top x) a) := by
    funext a
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply' (F := constPresheaf (X := X) A)
      (G := sheafify (Opens.grothendieckTopology X) (constPresheaf (X := X) A)) ⊤ x
      (Opens.mem_top x) (toSheafify (Opens.grothendieckTopology X) (constPresheaf (X := X) A))
      a).symm
  rw [hfun]
  exact hb.comp (constPresheaf_germ_top_bijective A x)

/-- Two constant sections with the same germ at a point have the same value. -/
theorem eq_of_germ_constSection_eq {U V : Opens X} {x : X} (hU : x ∈ U) (hV : x ∈ V) {a b : A}
    (h : (constSheaf (X := X) A).presheaf.germ U x hU (constSection A U a) =
      (constSheaf (X := X) A).presheaf.germ V x hV (constSection A V b)) : a = b := by
  rw [germ_constSection A U, germ_constSection A V] at h
  exact (germ_constSection_top_bijective A x).1 h

/-- Every germ of the constant sheaf is the germ of a constant section. -/
theorem exists_germ_eq_germ_constSection {U : Opens X} {x : X} (hx : x ∈ U)
    (s : (constSheaf (X := X) A).presheaf.obj (op U)) :
    ∃ a : A, (constSheaf (X := X) A).presheaf.germ U x hx s =
      (constSheaf (X := X) A).presheaf.germ U x hx (constSection A U a) := by
  obtain ⟨a, ha⟩ := (germ_constSection_top_bijective A x).2
    ((constSheaf (X := X) A).presheaf.germ U x hx s)
  exact ⟨a, by rw [germ_constSection]; exact ha.symm⟩

/-- Over a preconnected open, every section of the constant sheaf is constant. -/
theorem exists_eq_constSection {U : Opens X} (hU : IsPreconnected (U : Set X))
    (s : (constSheaf (X := X) A).presheaf.obj (op U)) :
    ∃ a : A, s = constSection A U a := by
  classical
  by_cases hne : (U : Set X).Nonempty
  swap
  · refine ⟨0, TopCat.Presheaf.section_ext (constSheaf (X := X) A) U _ _ fun x hx => ?_⟩
    exact absurd ⟨x, hx⟩ hne
  obtain ⟨x₀, hx₀⟩ := hne
  choose f hf using fun y : U => exists_germ_eq_germ_constSection A y.2 s
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨W, hyW, iU, iV, e⟩ := (constSheaf (X := X) A).presheaf.germ_eq y.1 y.2 y.2 s
      (constSection A U (f y)) (hf y)
    refine ⟨Subtype.val ⁻¹' (W : Set X), W.2.preimage continuous_subtype_val, hyW, ?_⟩
    intro z hz
    have h1 := hf z
    have h2 : (constSheaf (X := X) A).presheaf.germ U z.1 z.2 s =
        (constSheaf (X := X) A).presheaf.germ U z.1 z.2 (constSection A U (f y)) := by
      rw [← TopCat.Presheaf.germ_res_apply _ iU z.1 hz, e, TopCat.Presheaf.germ_res_apply]
    have := h1.symm.trans h2
    exact eq_of_germ_constSection_eq A z.2 z.2 this
  have : PreconnectedSpace U := Subtype.preconnectedSpace hU
  refine ⟨f ⟨x₀, hx₀⟩, TopCat.Presheaf.section_ext (constSheaf (X := X) A) U _ _ fun x hx => ?_⟩
  rw [hf ⟨x, hx⟩, hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x₀, hx₀⟩]

/-- Restriction of the constant sheaf onto a preconnected open is surjective. -/
theorem res_surjective {U V : Opens X} (h : V ≤ U) (hV : IsPreconnected (V : Set X)) :
    Function.Surjective ((constSheaf (X := X) A).presheaf.map (homOfLE h).op) := by
  intro s
  obtain ⟨a, rfl⟩ := exists_eq_constSection A hV s
  exact ⟨constSection A U a, constSection_res A h a⟩

/-- Over a nonempty open, constant sections with different values differ. -/
theorem constSection_injective {U : Opens X} (hU : (U : Set X).Nonempty) :
    Function.Injective (constSection (X := X) A U) := by
  obtain ⟨x, hx⟩ := hU
  intro a b hab
  exact eq_of_germ_constSection_eq A hx hx (congrArg _ hab)

/-- Over a connected open, the sections of the constant sheaf are the elements of `A`. -/
theorem constSection_bijective {U : Opens X} (hU : IsConnected (U : Set X)) :
    Function.Bijective (constSection (X := X) A U) :=
  ⟨constSection_injective A hU.1, fun s => (exists_eq_constSection A hU.2 s).imp fun _ h => h.symm⟩

end Weil.ConstantSheafSections




namespace Weil.ChainCech

open Stacks.Cech CechCochains

/-- **Solving `β (k + 1) - β k = c k` along `ℤ`.** If the maps `r k : G k → H k` and
`l k : G (k + 1) → H k` are surjective, every family `c` has the form
`l k (β (k + 1)) - r k (β k)`. -/
theorem exists_chain_primitive {G H : ℤ → Type*} [∀ k, AddCommGroup (G k)]
    [∀ k, AddCommGroup (H k)] (r : ∀ k, G k →+ H k) (l : ∀ k, G (k + 1) →+ H k)
    (hr : ∀ k, Function.Surjective (r k)) (hl : ∀ k, Function.Surjective (l k))
    (c : ∀ k, H k) : ∃ β : ∀ k, G k, ∀ k, l k (β (k + 1)) - r k (β k) = c k := by
  choose rinv hrinv using hr
  choose linv hlinv using hl
  let P : (n : ℕ) → G (n : ℤ) := fun n => Nat.rec (motive := fun n => G (n : ℤ)) 0
    (fun n p => linv (n : ℤ) (c n + r n p)) n
  let Q : (n : ℕ) → G (Int.negSucc n) := fun n => Nat.rec (motive := fun n => G (Int.negSucc n))
    (rinv (-1) (l (-1) (P 0) - c (-1)))
    (fun n q => rinv (Int.negSucc (n + 1)) (l (Int.negSucc (n + 1)) q - c (Int.negSucc (n + 1)))) n
  let β : ∀ k, G k := fun k => match k with
    | Int.ofNat n => P n
    | Int.negSucc n => Q n
  refine ⟨β, fun k => ?_⟩
  rcases k with n | n
  · change l n (linv n (c n + r n (P n))) - r n (P n) = c n
    rw [hlinv]; abel
  · rcases n with _ | n
    · change l (-1) (P 0) - r (-1) (rinv (-1) (l (-1) (P 0) - c (-1))) = c (-1)
      rw [hrinv]; abel
    · change l (Int.negSucc (n + 1)) (Q n) - r (Int.negSucc (n + 1))
        (rinv (Int.negSucc (n + 1)) (l (Int.negSucc (n + 1)) (Q n) - c (Int.negSucc (n + 1)))) =
          c (Int.negSucc (n + 1))
      rw [hrinv]; abel

variable {X : TopCat.{u}} (U : ℤ → Opens X)

/-- The one-element increasing tuple `(k)`. -/
def single (k : ℤ) : OrdIndex (I := ℤ) 0 :=
  ⟨fun _ => k, fun a b hab => (lt_irrefl a (Subsingleton.elim (α := Fin 1) a b ▸ hab)).elim⟩

/-- The increasing pair `(k, k + 1)`. -/
def pair (k : ℤ) : OrdIndex (I := ℤ) 1 :=
  ⟨![k, k + 1], by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simp⟩

/-- The intersection indexed by `(k)` is `U k`. -/
theorem inter_single (k : ℤ) : inter U (single k).1 = U k := by
  simp [inter, single]

/-- The intersection indexed by `(k, k + 1)` is `U k ⊓ U (k + 1)`. -/
theorem inter_pair (k : ℤ) : inter U (pair k).1 = U k ⊓ U (k + 1) := by
  apply le_antisymm
  · exact le_inf (iInf_le (fun j => U ((pair k).1 j)) 0) (iInf_le (fun j => U ((pair k).1 j)) 1)
  · refine le_iInf fun j => ?_
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

/-- Every one-element increasing tuple is `single`. -/
theorem eq_single (σ : OrdIndex (I := ℤ) 0) : σ = single (σ.1 0) := by
  apply Subtype.ext
  funext j
  rw [Subsingleton.elim (α := Fin 1) j 0]
  rfl

/-- An increasing pair of consecutive integers is `pair`. -/
theorem eq_pair (p : OrdIndex (I := ℤ) 1) (h : p.1 1 = p.1 0 + 1) : p = pair (p.1 0) := by
  apply Subtype.ext
  funext j
  fin_cases j
  · rfl
  · exact h

variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- A sheaf has a single section over the empty open. -/
theorem subsingleton_sections_of_eq_bot {V : Opens X} (h : V = ⊥) :
    Subsingleton (F.presheaf.obj (op V)) :=
  AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero

/-- **Čech acyclicity of a chain cover.** Let `U : ℤ → Opens X` be a family in which `U i` and
`U j` are disjoint whenever `i + 2 ≤ j`, and let `F` be an abelian sheaf whose restrictions from
`U k` and from `U (k + 1)` to `U k ⊓ U (k + 1)` are surjective. Then the Čech cohomology of `F`
for the family `U` vanishes in every positive degree. -/
theorem isZero_orderedCechComplex_homology
    (hdisj : ∀ i j, i + 2 ≤ j → U i ⊓ U j = ⊥)
    (hsurj : ∀ (k : ℤ) (V W : Opens X) (h : V ≤ W), (W = U k ∨ W = U (k + 1)) →
      V = U k ⊓ U (k + 1) → Function.Surjective (F.presheaf.map (homOfLE h).op))
    (n : ℕ) (hn : 0 < n) :
    IsZero ((orderedCechComplex U F.presheaf).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · -- degree one: every cochain is a coboundary
    rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
    rw [ShortComplex.ab_exact_iff]
    intro c _
    change OrdCochain U F.presheaf 1 at c
    have hr : ∀ k, inter U (pair k).1 ≤ inter U (single k).1 := fun k => by
      rw [inter_pair, inter_single]; exact inf_le_left
    have hl : ∀ k, inter U (pair k).1 ≤ inter U (single (k + 1)).1 := fun k => by
      rw [inter_pair, inter_single]; exact inf_le_right
    obtain ⟨β, hβ⟩ := exists_chain_primitive
      (G := fun k => F.presheaf.obj (op (inter U (single k).1)))
      (H := fun k => F.presheaf.obj (op (inter U (pair k).1)))
      (fun k => restr F.presheaf (hr k)) (fun k => restr F.presheaf (hl k))
      (fun k => hsurj k _ _ (hr k) (Or.inl (inter_single U k)) (inter_pair U k))
      (fun k => hsurj k _ _ (hl k) (Or.inr (inter_single U (k + 1))) (inter_pair U k))
      (fun k => c (pair k))
    let b : OrdCochain U F.presheaf 0 := fun σ =>
      (eq_single σ).symm ▸ β (σ.1 0)
    have hb : ∀ (σ τ : OrdIndex (I := ℤ) 0) (e : σ = τ) {V : Opens X} (h : V ≤ inter U σ.1)
        (h' : V ≤ inter U τ.1), restr F.presheaf h (b σ) = restr F.presheaf h' (b τ) := by
      intro σ τ e V h h'
      subst e
      rfl
    have hbs : ∀ (k : ℤ) {V : Opens X} (h : V ≤ inter U (single k).1),
        restr F.presheaf h (b (single k)) = restr F.presheaf h (β k) := fun k V h => rfl
    have hd : ∀ p : OrdIndex (I := ℤ) 1, ordD U F.presheaf 0 b p =
        restr F.presheaf (show inter U p.1 ≤ inter U (single (p.1 1)).1 by
            rw [inter_single]; exact iInf_le (fun j => U (p.1 j)) 1) (β (p.1 1)) -
          restr F.presheaf (show inter U p.1 ≤ inter U (single (p.1 0)).1 by
            rw [inter_single]; exact iInf_le (fun j => U (p.1 j)) 0) (β (p.1 0)) := by
      intro p
      have hface0 : (⟨p.1 ∘ (0 : Fin 2).succAbove, strictMono_omit p.2 0⟩ :
          OrdIndex (I := ℤ) 0) = single (p.1 1) := by
        apply Subtype.ext; funext j; rw [Subsingleton.elim (α := Fin 1) j 0]; rfl
      have hface1 : (⟨p.1 ∘ (1 : Fin 2).succAbove, strictMono_omit p.2 1⟩ :
          OrdIndex (I := ℤ) 0) = single (p.1 0) := by
        apply Subtype.ext; funext j; rw [Subsingleton.elim (α := Fin 1) j 0]; rfl
      change (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • restr F.presheaf (inter_le_omit U p.1 j)
        (b ⟨p.1 ∘ j.succAbove, strictMono_omit p.2 j⟩)) = _
      rw [Fin.sum_univ_two, hb _ _ hface0, hb _ _ hface1, hbs, hbs]
      · simp [sub_eq_add_neg]
      · rw [inter_single]; exact iInf_le (fun j => U (p.1 j)) 0
      · rw [inter_single]; exact iInf_le (fun j => U (p.1 j)) 1
    refine ⟨b, ?_⟩
    change ordD U F.presheaf 0 b = c
    funext p
    have hlt : p.1 0 < p.1 1 := p.2 (by decide)
    by_cases hp : p.1 1 = p.1 0 + 1
    · rw [eq_pair p hp, hd]
      exact hβ _
    · have hle : inter U p.1 ≤ U (p.1 0) ⊓ U (p.1 1) :=
        le_inf (iInf_le (fun j => U (p.1 j)) 0) (iInf_le (fun j => U (p.1 j)) 1)
      have := subsingleton_sections_of_eq_bot F
        (eq_bot_iff.2 (hle.trans (hdisj _ _ (by omega)).le))
      exact Subsingleton.elim _ _
  · -- degrees `≥ 2`: the cochain groups vanish
    rw [HomologicalComplex.exactAt_iff' _ (m + 1) (m + 2) (m + 3) (by simp) (by simp)]
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero (AddCommGrpCat.of (OrdCochain U F.presheaf (m + 2)))
    suffices Subsingleton (OrdCochain U F.presheaf (m + 2)) from
      AddCommGrpCat.isZero_of_subsingleton _
    refine ⟨fun s t => funext fun i => ?_⟩
    let j0 : Fin (m + 3) := ⟨0, by omega⟩
    let j1 : Fin (m + 3) := ⟨1, by omega⟩
    let j2 : Fin (m + 3) := ⟨2, by omega⟩
    have hle : inter U i.1 ≤ U (i.1 j0) ⊓ U (i.1 j2) :=
      le_inf (iInf_le (fun j => U (i.1 j)) j0) (iInf_le (fun j => U (i.1 j)) j2)
    have h02 : i.1 j0 + 2 ≤ i.1 j2 := by
      have h1 : i.1 j0 < i.1 j1 := i.2 (Fin.mk_lt_mk.2 (by omega))
      have h2 : i.1 j1 < i.1 j2 := i.2 (Fin.mk_lt_mk.2 (by omega))
      omega
    have := subsingleton_sections_of_eq_bot F (eq_bot_iff.2 (hle.trans (hdisj _ _ h02).le))
    exact Subsingleton.elim _ _

end Weil.ChainCech


namespace Weil.ChainRefinement

variable {ι : Type*} (P : ι → ℝ → Prop) (T : Set ℝ)

/-- `Good P T a b`: one member `P i` contains every point of `T` strictly between `a` and `b`. -/
def Good (a b : ℝ) : Prop := ∃ i, ∀ x ∈ T, a < x → x < b → P i x

variable {P T}

/-- `Good` holds vacuously when no point of `T` lies strictly between `a` and `b`. -/
theorem good_of_forall [Nonempty ι] {a b : ℝ} (h : ∀ x ∈ T, ¬ (a < x ∧ x < b)) : Good P T a b :=
  ⟨Classical.arbitrary ι, fun x hx h1 h2 => absurd ⟨h1, h2⟩ (h x hx)⟩

/-- `Good` passes to intervals whose points in `T` lie in the original interval. -/
theorem Good.mono {a b a' b' : ℝ} (h : Good P T a b)
    (hab : ∀ x ∈ T, a' < x → x < b' → a < x ∧ x < b) : Good P T a' b' := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun x hx h1 h2 => hi x hx (hab x hx h1 h2).1 (hab x hx h1 h2).2⟩

/-- **One-sided chain.** Starting from `x₀ ∈ S` and stepping to the right by a quarter of a
`1`-Lipschitz positive radius function `δ`, one obtains a strictly increasing sequence whose
consecutive two-step intervals are each contained in one member, and which passes every point
of `S` to the right of `x₀`. -/
theorem exists_chain_right [Nonempty ι] {S : Set ℝ} (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hST : S ⊆ T) {δ : ℝ → ℝ} (hpos : ∀ c ∈ S, 0 < δ c)
    (hlip : ∀ x ∈ S, ∀ y ∈ S, δ x ≤ δ y + |x - y|)
    (hstay : ∀ c ∈ S, ∀ y ∈ T, |y - c| < δ c → y ∈ S)
    (hgood : ∀ c ∈ S, ∀ r, r < δ c → Good P T (c - r) (c + r)) {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ s : ℕ → ℝ, s 0 = x₀ ∧ s 1 = x₀ + δ x₀ / 4 ∧ StrictMono s ∧
      (∀ n, Good P T (s n) (s (n + 2))) ∧
      (∀ y ∈ S, x₀ ≤ y → ∃ n, s n ≤ y ∧ y < s (n + 1)) := by
  classical
  let g : ℝ → ℝ := fun y => if y ∈ S then δ y / 4 else 1
  have hg : ∀ y, 0 < g y := fun y => by
    by_cases hy : y ∈ S
    · simp only [g, hy, ite_true]; linarith [hpos y hy]
    · simp only [g, hy, ite_false]; norm_num
  let s : ℕ → ℝ := fun n => Nat.rec x₀ (fun _ y => y + g y) n
  have hs0 : s 0 = x₀ := rfl
  have hsucc : ∀ n, s (n + 1) = s n + g (s n) := fun n => rfl
  have hsuccS : ∀ n, s n ∈ S → s (n + 1) = s n + δ (s n) / 4 := fun n h => by
    rw [hsucc]; simp only [g, h, ite_true]
  have hmono : StrictMono s := strictMono_nat_of_lt_succ fun n => by
    rw [hsucc]; linarith [hg (s n)]
  -- once the sequence leaves `S`, it lies above all of `T`
  have hout : ∀ n, s n ∈ S ∨ ∀ t ∈ T, t < s n := by
    intro n
    induction n with
    | zero => exact Or.inl hx₀
    | succ n ih =>
      rcases ih with h | h
      · by_cases hT' : s (n + 1) ∈ T
        · left
          refine hstay _ h _ hT' ?_
          rw [hsuccS n h, abs_of_pos (by linarith [hpos _ h])]
          linarith [hpos _ h]
        · right
          intro t ht
          by_contra hle
          push Not at hle
          exact hT' (hT.out (hST h) ht ⟨(hmono (Nat.lt_succ_self n)).le, hle⟩)
      · exact Or.inr fun t ht => (h t ht).trans (hmono (Nat.lt_succ_self n))
  refine ⟨s, hs0, by simpa [hs0] using hsuccS 0 (hs0 ▸ hx₀), hmono, ?_, ?_⟩
  · intro n
    rcases hout (n + 1) with h1 | h1
    · -- the middle point is in `S`: centre there
      have h0 : s n ∈ S := by
        rcases hout n with h0 | h0
        · exact h0
        · exact absurd (h0 _ (hST h1)) (not_lt.2 (hmono (Nat.lt_succ_self n)).le)
      have e1 := hsuccS n h0
      have e2 : s (n + 2) = s (n + 1) + δ (s (n + 1)) / 4 := hsuccS (n + 1) h1
      have hl := hlip _ h0 _ h1
      have habs : |s n - s (n + 1)| = δ (s n) / 4 := by
        rw [e1, show s n - (s n + δ (s n) / 4) = -(δ (s n) / 4) by ring, abs_neg,
          abs_of_pos (by linarith [hpos _ h0])]
      rw [habs] at hl
      have hp1 := hpos _ h1
      refine (hgood _ h1 (δ (s (n + 1)) / 2) (by linarith)).mono fun x _ hx1 hx2 => ⟨?_, ?_⟩
      · linarith [hpos _ h0]
      · linarith
    · rcases hout n with h0 | h0
      · -- the middle point lies above `T`: centre at the first point
        have e1 := hsuccS n h0
        have hp0 := hpos _ h0
        refine (hgood _ h0 (δ (s n) / 2) (by linarith)).mono fun x hx hx1 _ => ⟨?_, ?_⟩
        · linarith
        · have := h1 x hx; linarith
      · exact good_of_forall fun x hx hx' => absurd hx'.1 (not_lt.2 (h0 x hx).le)
  · intro y hy hxy
    have hex : ∃ n, y < s (n + 1) := by
      by_contra hne
      push Not at hne
      have hle : ∀ n, s n ≤ y := fun n => by
        rcases n with _ | n
        · exact hs0 ▸ hxy
        · exact hne n
      have hbdd : BddAbove (Set.range s) := ⟨y, by rintro _ ⟨n, rfl⟩; exact hle n⟩
      set L := sSup (Set.range s)
      have hsL : ∀ n, s n ≤ L := fun n => le_csSup hbdd ⟨n, rfl⟩
      have hLy : L ≤ y := csSup_le (Set.range_nonempty s) (by rintro _ ⟨n, rfl⟩; exact hle n)
      have hsS : ∀ n, s n ∈ S := fun n =>
        hS.out (hs0 ▸ hx₀) hy ⟨hs0 ▸ hmono.monotone (Nat.zero_le n), hle n⟩
      have hLS : L ∈ S := hS.out hx₀ hy ⟨hs0 ▸ hsL 0, hLy⟩
      have hpL := hpos _ hLS
      obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty s)
        (show L - δ L / 8 < L by linarith)
      have hl := hlip _ hLS _ (hsS N)
      rw [abs_of_nonneg (by linarith [hsL N])] at hl
      have := hsL (N + 1)
      rw [hsuccS N (hsS N)] at this
      linarith
    let m := Nat.find hex
    refine ⟨m, ?_, Nat.find_spec hex⟩
    rcases hm : m with _ | k
    · exact hs0 ▸ hxy
    · have := Nat.find_min hex (show k < m by omega)
      exact not_lt.1 this

/-- The reflection of an order-connected subset of `ℝ` is order-connected. -/
theorem ordConnected_neg_preimage {S : Set ℝ} (hS : S.OrdConnected) :
    (Neg.neg ⁻¹' S : Set ℝ).OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hS.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩

/-- **Bi-infinite chain.** Under the hypotheses of `exists_chain_right`, there is a strictly
increasing `t : ℤ → ℝ` such that each interval `(t (k - 1), t (k + 1))` is contained (on `T`) in
one member, and these intervals cover `S`. -/
theorem exists_chain [Nonempty ι] {S : Set ℝ} (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hST : S ⊆ T) {δ : ℝ → ℝ} (hpos : ∀ c ∈ S, 0 < δ c)
    (hlip : ∀ x ∈ S, ∀ y ∈ S, δ x ≤ δ y + |x - y|)
    (hstay : ∀ c ∈ S, ∀ y ∈ T, |y - c| < δ c → y ∈ S)
    (hgood : ∀ c ∈ S, ∀ r, r < δ c → Good P T (c - r) (c + r)) {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ t : ℤ → ℝ, StrictMono t ∧ (∀ k, Good P T (t (k - 1)) (t (k + 1))) ∧
      (∀ y ∈ S, ∃ k, t (k - 1) < y ∧ y < t (k + 1)) := by
  classical
  obtain ⟨s, hs0, hs1, hsm, hsg, hsc⟩ :=
    exists_chain_right hS hT hST hpos hlip hstay hgood hx₀
  obtain ⟨s', hs'0, hs'1, hs'm, hs'g, hs'c⟩ := exists_chain_right (P := fun i x => P i (-x))
    (T := Neg.neg ⁻¹' T) (S := Neg.neg ⁻¹' S) (δ := fun x => δ (-x))
    (ordConnected_neg_preimage hS) (ordConnected_neg_preimage hT)
    (fun x hx => hST hx) (fun c hc => hpos _ hc)
    (fun x hx y hy => by
      have := hlip _ hx _ hy
      rwa [neg_sub_neg, abs_sub_comm] at this)
    (fun c hc y hy h => by
      refine hstay _ hc _ hy ?_
      rwa [neg_sub_neg, abs_sub_comm])
    (fun c hc r hr => by
      obtain ⟨i, hi⟩ := hgood _ hc r hr
      exact ⟨i, fun x hx h1 h2 => hi _ hx (by linarith) (by linarith)⟩)
    (show -x₀ ∈ Neg.neg ⁻¹' S by simpa using hx₀)
  simp only [neg_neg] at hs'1
  let t : ℤ → ℝ := fun k => if 0 ≤ k then s k.toNat else -s' (-k).toNat
  have htn : ∀ n : ℕ, t n = s n := fun n => by simp [t]
  have htm : ∀ n : ℕ, t (-n) = -s' n := fun n => by
    rcases n with _ | n
    · simp [t, hs0, hs'0]
    · have : ¬ (0 ≤ -((n + 1 : ℕ) : ℤ)) := by omega
      simp only [t, this, ite_false, neg_neg, Int.toNat_natCast]
  have hgoodneg : ∀ m : ℕ, Good P T (-s' (m + 2)) (-s' m) := fun m => by
    obtain ⟨i, hi⟩ := hs'g m
    exact ⟨i, fun x hx h1 h2 => by
      simpa using hi (-x) (by simpa using hx) (by linarith) (by linarith)⟩
  have htmono : StrictMono t := strictMono_int_of_lt_succ fun k => by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [htn, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, htn]
      exact hsm (Nat.lt_succ_self n)
    · rcases n with _ | n
      · rw [show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by simp, htn,
          show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num, htn]
        exact hsm Nat.zero_lt_one
      · rw [htm, show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, htm]
        exact neg_lt_neg (hs'm (Nat.lt_succ_self n))
  refine ⟨t, htmono, fun k => ?_, fun y hy => ?_⟩
  · obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rcases n with _ | n
      · rw [show ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) by norm_num, htm,
          show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num, htn, hs1, hs'1]
        have h := hgood _ hx₀ (δ x₀ / 4) (by linarith [hpos _ hx₀])
        exact h.mono fun x _ h1 h2 => ⟨by linarith, by linarith⟩
      · rw [show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) by push_cast; ring, htn,
          show ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, htn]
        exact hsg n
    · rcases n with _ | n
      · rw [show -((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) by norm_num, htm,
          show -((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num, htn, hs1, hs'1]
        have h := hgood _ hx₀ (δ x₀ / 4) (by linarith [hpos _ hx₀])
        exact h.mono fun x _ h1 h2 => ⟨by linarith, by linarith⟩
      · rw [show -((n + 1 : ℕ) : ℤ) - 1 = -((n + 2 : ℕ) : ℤ) by push_cast; ring, htm,
          show -((n + 1 : ℕ) : ℤ) + 1 = -((n : ℕ) : ℤ) by push_cast; ring, htm]
        exact hgoodneg n
  · by_cases hxy : x₀ ≤ y
    · obtain ⟨n, h1, h2⟩ := hsc y hy hxy
      refine ⟨n, ?_, ?_⟩
      · have : t ((n : ℤ) - 1) < t n := htmono (by omega)
        rw [htn] at this; linarith
      · rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, htn]; exact h2
    · obtain ⟨m, h1, h2⟩ := hs'c (-y) (by simpa using hy) (by linarith)
      refine ⟨-(m : ℤ), ?_, ?_⟩
      · rw [show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by push_cast; ring, htm]; linarith
      · have : t (-(m : ℤ)) < t (-(m : ℤ) + 1) := htmono (by omega)
        rw [htm] at this; linarith

end Weil.ChainRefinement

namespace Weil.IntervalCohomology

open Stacks.Cohomology.Basis (OpenCover)
open Weil.ConstantSheafSections Weil.ChainRefinement

variable {T : Set ℝ}

/-- The order-connected open subsets of a subset `T` of the real line. -/
def ordConnectedOpens (T : Set ℝ) : Set (Opens T) := {V | (V : Set T).OrdConnected}

/-- An order-connected subset of an interval is order-connected in `ℝ`. -/
theorem ordConnected_image_val (hT : T.OrdConnected) {V : Set T} (hV : V.OrdConnected) :
    (Subtype.val '' V : Set ℝ).OrdConnected := by
  refine ⟨?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
  exact ⟨⟨z, hT.out x.2 y.2 hz⟩, hV.out hx hy ⟨hz.1, hz.2⟩, rfl⟩

/-- An order-connected subset of an interval is preconnected. -/
theorem isPreconnected_of_ordConnected (hT : T.OrdConnected) {V : Set T} (hV : V.OrdConnected) :
    _root_.IsPreconnected V :=
  Topology.IsInducing.subtypeVal.isPreconnected_image.1
    (ordConnected_image_val hT hV).isPreconnected

/-- The order-connected opens of `T` form a basis of its topology. -/
theorem isBasis_ordConnectedOpens : Opens.IsBasis (ordConnectedOpens T) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 U.2 x hx
  refine ⟨⟨Metric.ball x ε, Metric.isOpen_ball⟩, ⟨fun a ha b hb z hz => ?_⟩,
    Metric.mem_ball_self hε, hball⟩
  have h1 : (a : ℝ) ≤ z := hz.1
  have h2 : (z : ℝ) ≤ b := hz.2
  change dist a x < ε at ha
  change dist b x < ε at hb
  change dist z x < ε
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff] at ha hb ⊢
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- A finite intersection of order-connected opens is order-connected. -/
theorem iInf_mem_ordConnectedOpens {p : ℕ} (f : Fin (p + 1) → Opens T)
    (hf : ∀ k, f k ∈ ordConnectedOpens T) : (⨅ k, f k) ∈ ordConnectedOpens T := by
  change (((⨅ k, f k : Opens T)) : Set T).OrdConnected
  rw [Opens.coe_iInf]
  exact Set.ordConnected_iInter hf

/-! ### A Lebesgue radius -/

section Radius

variable {ι : Type*} (O : ι → Opens T)

/-- The supremum of the radii `r ≤ 1` of the balls around `x` contained in one member of `O`. -/
noncomputable def radius (x : T) : ℝ :=
  sSup {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ i, Metric.ball x r ⊆ (O i : Set T)}

variable {O}

/-- The radii defining `radius` are bounded above by `1`. -/
theorem radius_bddAbove (x : T) :
    BddAbove {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ i, Metric.ball x r ⊆ (O i : Set T)} :=
  ⟨1, fun _ hr => hr.1.2⟩

variable [Nonempty ι]

/-- The radius `0` is admissible. -/
theorem radius_set_nonempty (x : T) :
    {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ i, Metric.ball x r ⊆ (O i : Set T)}.Nonempty :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, Classical.arbitrary ι, by simp⟩

/-- `radius O` is nonnegative. -/
theorem radius_nonneg (x : T) : 0 ≤ radius O x :=
  le_csSup (radius_bddAbove x) ⟨⟨le_rfl, zero_le_one⟩, Classical.arbitrary ι, by simp⟩

/-- `radius O` is at most `1`. -/
theorem radius_le_one (x : T) : radius O x ≤ 1 :=
  csSup_le (radius_set_nonempty x) fun _ hr => hr.1.2

/-- Every ball of radius smaller than `radius O x` lies in one member of `O`. -/
theorem exists_ball_subset_of_lt_radius {x : T} {r : ℝ} (h : r < radius O x) :
    ∃ i, Metric.ball x r ⊆ (O i : Set T) := by
  obtain ⟨r', ⟨_, i, hi⟩, hr'⟩ := exists_lt_of_lt_csSup (radius_set_nonempty x) h
  exact ⟨i, (Metric.ball_subset_ball hr'.le).trans hi⟩

omit [Nonempty ι] in
/-- `radius O` is positive at every point covered by `O`. -/
theorem radius_pos {x : T} {i : ι} (hx : x ∈ O i) : 0 < radius O x := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (O i).2 x hx
  refine lt_of_lt_of_le (lt_min hε one_pos) (le_csSup (radius_bddAbove x)
    ⟨⟨(lt_min hε one_pos).le, min_le_right _ _⟩, i, ?_⟩)
  exact (Metric.ball_subset_ball (min_le_left _ _)).trans hb

/-- `radius O` is `1`-Lipschitz. -/
theorem radius_le_radius_add_dist (x y : T) : radius O x ≤ radius O y + dist x y := by
  by_contra h
  push Not at h
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  obtain ⟨i, hi⟩ := exists_ball_subset_of_lt_radius hr2
  have hd := dist_nonneg (x := x) (y := y)
  have : r - dist x y ≤ radius O y := by
    refine le_csSup (radius_bddAbove y) ⟨⟨by linarith [radius_nonneg (O := O) y],
      by linarith [radius_le_one (O := O) x]⟩, i, ?_⟩
    refine (Metric.ball_subset_ball' ?_).trans hi
    rw [dist_comm]; linarith
  linarith

end Radius

/-! ### Chain refinements -/

/-- **Chain refinements.** Every open cover of a nonempty order-connected open `V` of an
interval `T` is refined by a chain cover of `V` by order-connected opens. -/
theorem exists_chain_refinement (hT : T.OrdConnected) {ι : Type*} (O : ι → Opens T)
    {V : Opens T} (hV : V ∈ ordConnectedOpens T) (hO : ⨆ i, O i = V) {x₀ : T} (hx₀ : x₀ ∈ V) :
    ∃ U : ℤ → Opens T, (⨆ k, U k = V) ∧ (∀ k, U k ∈ ordConnectedOpens T) ∧
      (∀ i j, i + 2 ≤ j → U i ⊓ U j = ⊥) ∧ ∀ k, ∃ i, U k ≤ O i := by
  classical
  have hOV : ∀ i, O i ≤ V := fun i => hO ▸ le_iSup O i
  have hmemV : ∀ x : T, x ∈ V → ∃ i, x ∈ O i := fun x hx => by
    rw [← hO] at hx; exact Opens.mem_iSup.1 hx
  have : Nonempty ι := ⟨(hmemV x₀ hx₀).choose⟩
  let S : Set ℝ := {y | ∃ h : y ∈ T, (⟨y, h⟩ : T) ∈ V}
  let P : ι → ℝ → Prop := fun i y => ∃ h : y ∈ T, (⟨y, h⟩ : T) ∈ O i
  let δ : ℝ → ℝ := fun y => if h : y ∈ T then radius O ⟨y, h⟩ else 0
  have hδ : ∀ (y : ℝ) (h : y ∈ T), δ y = radius O ⟨y, h⟩ := fun y h => by simp [δ, h]
  have hS : S.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨hxT, hxV⟩ := hx
    obtain ⟨hyT, hyV⟩ := hy
    exact ⟨hT.out hxT hyT hz, (show (V : Set T).OrdConnected from hV).out hxV hyV ⟨hz.1, hz.2⟩⟩
  have hST : S ⊆ T := fun y hy => hy.1
  obtain ⟨t, htm, htg, htc⟩ := exists_chain (P := P) (T := T) (S := S) (δ := δ) hS hT hST
    (fun c hc => by
      obtain ⟨hcT, hcV⟩ := hc
      obtain ⟨i, hi⟩ := hmemV _ hcV
      rw [hδ c hcT]; exact radius_pos hi)
    (fun x hx y hy => by
      rw [hδ x hx.1, hδ y hy.1]
      have := radius_le_radius_add_dist (O := O) ⟨x, hx.1⟩ ⟨y, hy.1⟩
      rwa [Subtype.dist_eq, Real.dist_eq] at this)
    (fun c hc y hy h => by
      rw [hδ c hc.1] at h
      obtain ⟨i, hi⟩ := exists_ball_subset_of_lt_radius (O := O) (x := ⟨c, hc.1⟩)
        (r := (|y - c| + radius O ⟨c, hc.1⟩) / 2) (by linarith)
      have hyb : (⟨y, hy⟩ : T) ∈
          Metric.ball (⟨c, hc.1⟩ : T) ((|y - c| + radius O ⟨c, hc.1⟩) / 2) := by
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]; linarith
      exact ⟨hy, hOV i (hi hyb)⟩)
    (fun c hc r hr => by
      rw [hδ c hc.1] at hr
      obtain ⟨i, hi⟩ := exists_ball_subset_of_lt_radius (O := O) hr
      refine ⟨i, fun x hx h1 h2 => ⟨hx, hi ?_⟩⟩
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> simp only <;> linarith)
    (x₀ := x₀.1) ⟨x₀.2, hx₀⟩
  choose i hi using htg
  let U : ℤ → Opens T := fun k =>
    ⟨Subtype.val ⁻¹' Set.Ioo (t (k - 1)) (t (k + 1)), isOpen_Ioo.preimage continuous_subtype_val⟩
  have hUO : ∀ k, U k ≤ O (i k) := fun k x hx => by
    obtain ⟨h, hmem⟩ := hi k x.1 x.2 hx.1 hx.2
    exact hmem
  refine ⟨U, le_antisymm (iSup_le fun k => (hUO k).trans (hOV _)) fun x hx => ?_,
    fun k => ⟨fun a ha b hb z hz => ⟨lt_of_lt_of_le ha.1 hz.1, lt_of_le_of_lt hz.2 hb.2⟩⟩,
    fun j k hjk => ?_, fun k => ⟨i k, hUO k⟩⟩
  · obtain ⟨k, hk1, hk2⟩ := htc x.1 ⟨x.2, hx⟩
    exact Opens.mem_iSup.2 ⟨k, hk1, hk2⟩
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨_, h1⟩, ⟨h2, _⟩⟩ := hx
    have : t (j + 1) ≤ t (k - 1) := htm.monotone (by omega)
    exact absurd (h2.trans h1) (not_lt.2 this)

/-! ### Chain covers and Cartan's criterion -/

/-- Open covers of an order-connected open of `T` by order-connected opens which are either
empty or chains indexed by `ℤ` in which members two or more steps apart are disjoint. -/
def chainCovers (T : Set ℝ) : Set (OpenCover T) :=
  {W | W.carrier ∈ ordConnectedOpens T ∧ (∀ i, W.obj i ∈ ordConnectedOpens T) ∧
    (IsEmpty W.ι ∨ ∃ (C : Opens T) (U : ℤ → Opens T) (h : ⨆ k, U k = C),
      W = ⟨ℤ, C, U, h⟩ ∧ ∀ i j, i + 2 ≤ j → U i ⊓ U j = ⊥)}

/-- **Chain covers are cofinal** among the open covers of order-connected opens of `T`. -/
theorem chainCovers_cofinal (hT : T.OrdConnected) (V : Opens T) (hV : V ∈ ordConnectedOpens T)
    (W : OpenCover T) (hW : W.carrier = V) :
    ∃ W' ∈ chainCovers T, W'.carrier = V ∧ W'.Refines W := by
  classical
  by_cases hne : (V : Set T).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨U, hU, hUB, hdisj, href⟩ :=
      exists_chain_refinement hT W.obj hV (W.iSup_eq.trans hW) hx₀
    exact ⟨⟨ℤ, V, U, hU⟩, ⟨hV, hUB, Or.inr ⟨V, U, hU, rfl, hdisj⟩⟩, rfl, hW.symm, href⟩
  · have hV0 : V = ⊥ := by
      apply Opens.ext; rw [Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.1 hne
    by_cases hι : IsEmpty W.ι
    · refine ⟨W, ⟨hW ▸ hV, fun i => isEmptyElim i, Or.inl hι⟩, hW, rfl, fun j => ⟨j, le_rfl⟩⟩
    · rw [not_isEmpty_iff] at hι
      obtain ⟨i₀⟩ := hι
      have hbot : (⨆ _ : ℤ, (⊥ : Opens T)) = V := by rw [iSup_const, hV0]
      have hbotB : (⊥ : Opens T) ∈ ordConnectedOpens T := by
        change ((⊥ : Opens T) : Set T).OrdConnected
        rw [Opens.coe_bot]; exact Set.ordConnected_empty
      exact ⟨⟨ℤ, V, fun _ => ⊥, hbot⟩, ⟨hV, fun _ => hbotB,
        Or.inr ⟨V, fun _ => ⊥, hbot, rfl, fun _ _ _ => inf_idem _⟩⟩, rfl, hW.symm,
        fun _ => ⟨i₀, bot_le⟩⟩

variable (A : AddCommGrpCat.{0})

/-- **Čech vanishing for chain covers**, with coefficients in a constant sheaf. -/
theorem isZero_cech_homology_constSheaf (hT : T.OrdConnected) (W : OpenCover T)
    (hW : W ∈ chainCovers T) (n : ℕ) (hn : 0 < n) :
    IsZero (((cechComplexFunctor W.obj).obj
      (constSheaf (X := TopCat.of T) A).presheaf).homology n) := by
  obtain ⟨_, hmem, hW | ⟨C, U, h, rfl, hdisj⟩⟩ := hW
  · let : LinearOrder W.ι := LinearOrder.lift' (fun i => (isEmptyElim i : ℕ)) fun a => isEmptyElim a
    let : Fintype W.ι := Fintype.ofIsEmpty
    exact Stacks.Cech.isZero_homology_cechComplexFunctor (X := TopCat.of T) W.obj _
      (by simp)
  · have h1 := Weil.ChainCech.isZero_orderedCechComplex_homology (X := TopCat.of T) U
      (constSheaf (X := TopCat.of T) A) hdisj (fun k V W' hle _ hV => by
        apply res_surjective
        apply isPreconnected_of_ordConnected hT
        rw [hV]
        exact (hmem k).inter (hmem (k + 1))) n hn
    have e := Stacks.Cech.orderedCechHomologyIso.{0, 0, 0} (X := TopCat.of T) (I := ℤ) U
      (constSheaf (X := TopCat.of T) A).presheaf n
    exact h1.of_iso e.symm

/-- The whole space is order-connected. -/
theorem top_mem_ordConnectedOpens : (⊤ : Opens T) ∈ ordConnectedOpens T := by
  change ((⊤ : Opens T) : Set T).OrdConnected
  rw [Opens.coe_top]; exact Set.ordConnected_univ

/-- **Higher cohomology of an interval vanishes on its order-connected opens.** For an
order-connected `T ⊆ ℝ` and an abelian group `A`, the cohomology `Hⁿ(V, A)` of the constant sheaf
vanishes in every positive degree over every order-connected open `V` of `T`. -/
theorem isZero_H'_constantSheaf (hT : T.OrdConnected) (V : Opens T)
    (hV : V ∈ ordConnectedOpens T) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{0, 0, 0}
      ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj A) n V) :=
  Stacks.Cohomology.AbelianBasis.cechToCohomologyOnBasis _ (ordConnectedOpens T)
    isBasis_ordConnectedOpens (chainCovers T)
    (fun _ hW => ⟨hW.1, hW.2.1, fun _ _ => iInf_mem_ordConnectedOpens _ fun _ => hW.2.1 _⟩)
    (fun V hV W hW => chainCovers_cofinal hT V hV W hW)
    (fun W hW n hn => isZero_cech_homology_constSheaf A hT W hW n hn) V hV n hn

/-- **The cohomology of an interval with constant coefficients vanishes in positive degrees.**
For every order-connected subset `T` of `ℝ` (an interval of any kind) and every abelian group `A`,
`Hⁿ(T, A) = 0` for `n ≥ 1`. -/
theorem subsingleton_H_constantSheaf (hT : T.OrdConnected) (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj A) n) :=
  (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top _ n).2
    (AddCommGrpCat.subsingleton_of_isZero
      (isZero_H'_constantSheaf A hT ⊤ top_mem_ordConnectedOpens n hn))

/-- A nonempty interval is a connected space. -/
theorem connectedSpace_of_ordConnected (hT : T.OrdConnected) (hne : T.Nonempty) :
    ConnectedSpace T :=
  isConnected_iff_connectedSpace.1 ⟨hne, hT.isPreconnected⟩

/-- **Global sections of the constant sheaf on a nonempty interval.** The constant section map
`A → Γ(T, A)` is an isomorphism. -/
noncomputable def constantSheafSectionsTopAddEquiv (hT : T.OrdConnected) (hne : T.Nonempty) :
    A ≃+ ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj A).obj.obj
      (op ⊤) :=
  have : ConnectedSpace T := connectedSpace_of_ordConnected hT hne
  AddEquiv.ofBijective ((toConst (X := TopCat.of T) A).app (op ⊤)).hom
    (constSection_bijective (X := TopCat.of T) A (U := ⊤) (by
      rw [Opens.coe_top]; exact isConnected_univ))

/-- **`H⁰` of a nonempty interval with constant coefficients is the coefficient group.** -/
noncomputable def constantSheafHZeroAddEquiv (hT : T.OrdConnected) (hne : T.Nonempty) :
    Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj A) 0 ≃+ A :=
  (Sheaf.H.equiv₀ _ Stacks.Cohomology.TerminalCohomology.topIsTerminal).trans
    (constantSheafSectionsTopAddEquiv A hT hne).symm

end Weil.IntervalCohomology

namespace unitInterval

open Weil.IntervalCohomology

variable (A : AddCommGrpCat.{0})

/-- **`Hⁿ([0, 1], A) = 0` for `n ≥ 1`.** -/
theorem subsingleton_H_constantSheaf (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
        AddCommGrpCat.{0}).obj A) n) :=
  Weil.IntervalCohomology.subsingleton_H_constantSheaf A Set.ordConnected_Icc n hn

/-- **`H⁰([0, 1], A) ≅ A`.** -/
noncomputable def constantSheafHZeroAddEquiv :
    Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
      AddCommGrpCat.{0}).obj A) 0 ≃+ A :=
  Weil.IntervalCohomology.constantSheafHZeroAddEquiv A Set.ordConnected_Icc
    ⟨0, unitInterval.zero_mem⟩

end unitInterval

namespace Set.Icc

variable (A : AddCommGrpCat.{0}) {a b : ℝ}

/-- **`Hⁿ([a, b], A) = 0` for `n ≥ 1`**, for every compact interval. -/
theorem subsingleton_H_constantSheaf (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H.{0}
      ((constantSheaf (Opens.grothendieckTopology (Set.Icc a b)) AddCommGrpCat.{0}).obj A) n) :=
  Weil.IntervalCohomology.subsingleton_H_constantSheaf A Set.ordConnected_Icc n hn

/-- **`H⁰([a, b], A) ≅ A`** for `a ≤ b`. -/
noncomputable def constantSheafHZeroAddEquiv (hab : a ≤ b) :
    Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (Set.Icc a b))
      AddCommGrpCat.{0}).obj A) 0 ≃+ A :=
  Weil.IntervalCohomology.constantSheafHZeroAddEquiv A Set.ordConnected_Icc ⟨a, le_rfl, hab⟩

end Set.Icc

end
