module

public import WeilFrontier.Geometry.Manifold.Complex.MeromorphicSection
public import WeilFrontier.Geometry.Manifold.Sheaf.HolomorphicCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# The analytic divisor sequence of a Riemann surface

Let `M` be a Riemann surface. A meromorphic function on an open subset `U ⊆ M` which vanishes
identically near no point of `U` is a *meromorphic unit* on `U`; two of them are identified when
they agree off a discrete subset of `U`. Under multiplication they form a sheaf of abelian groups
`𝓜_M^×`. A *divisor* on `U` is a function `U → ℤ` with locally finite support; divisors form the
sheaf `Div_M`. Taking orders of meromorphic units gives the divisor map `𝓜_M^× ⟶ Div_M`, and a
nowhere vanishing holomorphic function is a meromorphic unit. The *divisor sequence*

`0 ⟶ 𝒪_M^× ⟶ 𝓜_M^× ⟶ Div_M ⟶ 0`

is a short exact sequence of abelian sheaves:
* a meromorphic unit of order zero everywhere agrees, off a discrete set, with its limit function
  `y ↦ lim_{z → y, z ≠ y} f z`, which is holomorphic and nowhere vanishing;
* near every point a divisor is the divisor of a rational function `∏ₐ (z - z(a)) ^ D a` of a
  chart coordinate `z`.

On a compact Riemann surface `H¹(M, 𝓜_M^×) = 0`. A class of `H¹` is the class of a torsor;
trivialise it on a finite cover by chart domains. The transition functions `F i j` form a
meromorphic cocycle. After shrinking the cover, the closures of the pairwise intersections are
compact, so the divisors of the `F i j` there have finite support; assigning each point to one
member of the cover splits these divisors as `D i - D j`, and with rational functions `φ i` of the
charts of divisors `D i`, the cocycle `F i j * φ j / φ i` is holomorphic and nowhere vanishing.
That cocycle splits meromorphically by Theorem K (`RiemannSurface.exists_meromorphic_splitting_eq`),
so `F i j` is a quotient `h i / h j` of meromorphic units and the torsor has a global section.

Consequently, the connecting map of the divisor sequence on global divisors,
`M →₀ ℤ ⟶ H¹(M, 𝒪_M^×)`, is surjective (every holomorphic line bundle comes from a divisor), and its
kernel consists of the divisors of global meromorphic functions.

## Main definitions

* `RiemannSurface.meromorphicUnits U`: the group of meromorphic units on `U` modulo equality off
  discrete subsets; `RiemannSurface.meromorphicUnitsMk` builds an element from a function.
* `RiemannSurface.meromorphicUnitsSheaf M`: the sheaf `𝓜_M^×`, written additively.
* `RiemannSurface.divisorSheaf M`: the sheaf `Div_M`, `U ↦ Function.locallyFinsuppWithin U ℤ`.
* `RiemannSurface.holomorphicUnitsToMeromorphicUnits M`: `𝒪_M^× ⟶ 𝓜_M^×`.
* `RiemannSurface.meromorphicUnitsToDivisor M`: `𝓜_M^× ⟶ Div_M`, `f ↦ divisorOn f U`.
* `RiemannSurface.divisorSequence M`: the short complex `𝒪_M^× ⟶ 𝓜_M^× ⟶ Div_M`.
* `RiemannSurface.globalDivisorBoundary M`: the connecting map `Γ(M, Div_M) → H¹(M, 𝒪_M^×)`.
* `RiemannSurface.globalDivisorEquiv M`: `(M →₀ ℤ) ≃+ Γ(M, Div_M)` for compact `M`.
* `RiemannSurface.analyticDivisorBoundary M`: the connecting map `(M →₀ ℤ) → H¹(M, 𝒪_M^×)`.

## Main results

* `RiemannSurface.shortExact_divisorSequence`: the divisor sequence is short exact.
* `RiemannSurface.exists_meromorphic_coboundary`: on a compact Riemann surface a meromorphic
  cocycle on a finite cover by chart domains is a coboundary after shrinking the cover.
* `RiemannSurface.nonempty_globalSections_of_meromorphicUnitsTorsor`: every `𝓜_M^×`-torsor on a
  compact Riemann surface has a global section.
* `RiemannSurface.subsingleton_sheafH_meromorphicUnitsSheaf_one`: `H¹(M, 𝓜_M^×) = 0` for compact
  `M`.
* `RiemannSurface.surjective_analyticDivisorBoundary`: every class in `H¹(M, 𝒪_M^×)` is the class
  of a divisor.
* `RiemannSurface.analyticDivisorBoundary_eq_zero_iff`: a divisor has trivial class iff it is the
  divisor of a global meromorphic function vanishing identically near no point.

## Implementation notes

The sections of `𝓜_M^×` over `U` are the subgroup `RiemannSurface.meromorphicUnits U` of the units
of the ring of germs of functions `M → ℂ` along the filter `Filter.codiscreteWithin U`, consisting
of the germs of meromorphic units; restriction is restriction of germs to a finer filter. Gluing
uses the limit functions `y ↦ limUnder (𝓝[≠] y) f`, which depend only on the germ. Meromorphy and
orders are those of `RiemannSurface.MeromorphicAt` and `RiemannSurface.orderAt` (read in charts),
and divisors those of `RiemannSurface.divisorOn`. Only `IsManifold 𝓘(ℂ) 1 M` and `T2Space M` are
assumed, besides compactness where it is needed.

First cohomology is Mathlib's `Sheaf.H`, the `Ext` group out of the constant sheaf `ℤ`, at an
arbitrary `Ext` universe; its vanishing is read off the bijection between torsor classes and `H¹`
(`Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1`, [Stacks, Tag 03AJ]). The connecting map is
the extension class of the divisor sequence composed with `Sheaf.H.equiv₀`, exactly as for the
étale divisor sequence (`Stacks.EtaleCohomology.divisorBoundary`).

## References

* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], Ch. 2
* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Ch. I, §11
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public section

open Set Filter Topology CategoryTheory TopologicalSpace Opposite
open scoped Manifold

namespace RiemannSurface

section Germs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {f g : M → ℂ} {x : M} {U V : Set M}

theorem orderAt_ne_top_iff (hf : MeromorphicAt f x) :
    orderAt f x ≠ ⊤ ↔ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  rw [Ne, orderAt_eq_top_iff]
  constructor
  · intro h
    rcases hf.eventually_eq_zero_or_eventually_ne_zero with h' | h'
    · exact absurd h' h
    · exact h'
  · intro h h'
    have := nhdsNE_neBot x
    obtain ⟨y, hy, hy'⟩ := (h.and h').exists
    exact hy hy'

theorem MeromorphicAt.eventually_continuousAt (hf : MeromorphicAt f x) :
    ∀ᶠ y in 𝓝[≠] x, ContinuousAt f y := by
  set e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have h : ∀ᶠ z in 𝓝[≠] (e x), AnalyticAt ℂ (f ∘ e.symm) z :=
    _root_.MeromorphicAt.eventually_analyticAt (f := f ∘ e.symm) hf
  have hsrc : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source :=
    mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hx)
  have h' : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source → ContinuousAt f y := by
    rw [eventually_nhdsNE_iff_of_mem_source e hx]
    have htgt : ∀ᶠ z in 𝓝[≠] (e x), z ∈ e.target :=
      mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source hx))
    filter_upwards [h, htgt] with z hz hzt _
    have h1 : ContinuousAt ((f ∘ e.symm) ∘ e) (e.symm z) := by
      refine ContinuousAt.comp ?_ (e.continuousAt (e.map_target hzt))
      rw [e.right_inv hzt]
      exact hz.continuousAt
    refine h1.congr ?_
    filter_upwards [e.open_source.mem_nhds (e.map_target hzt)] with y hy
    simp [e.left_inv hy]
  filter_upwards [h', hsrc] with y hy hy' using hy hy'

theorem limUnder_nhdsNE_eq_of_continuousAt {y : M} (h : ContinuousAt f y) :
    limUnder (𝓝[≠] y) f = f y := by
  have := nhdsNE_neBot y
  exact (h.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

omit [ChartedSpace ℂ M] in
theorem limUnder_nhdsNE_congr {y : M} (h : f =ᶠ[𝓝[≠] y] g) :
    limUnder (𝓝[≠] y) f = limUnder (𝓝[≠] y) g := by
  unfold limUnder
  rw [map_congr h]

omit [ChartedSpace ℂ M] in
theorem eventuallyEq_nhdsNE_of_codiscreteWithin (h : f =ᶠ[codiscreteWithin U] g) (hU : IsOpen U)
    (hx : x ∈ U) : f =ᶠ[𝓝[≠] x] g := by
  have h' := eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.1 h x hx
  filter_upwards [h', mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)] with y hy hy' using hy hy'

omit [ChartedSpace ℂ M] in
theorem eventuallyEq_codiscreteWithin_of_nhdsNE (h : ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g) :
    f =ᶠ[codiscreteWithin U] g :=
  eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun x hx =>
    (h x hx).mono fun _ hy _ => hy

/-- `f` is a meromorphic function on `U` vanishing identically near no point of `U`. -/
def IsMeromorphicUnitOn (f : M → ℂ) (U : Set M) : Prop :=
  MeromorphicOn f U ∧ ∀ x ∈ U, orderAt f x ≠ ⊤

theorem IsMeromorphicUnitOn.eventually_ne_zero (hf : IsMeromorphicUnitOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 :=
  (orderAt_ne_top_iff (hf.1 x hx)).1 (hf.2 x hx)

theorem IsMeromorphicUnitOn.eventually_codiscreteWithin_ne_zero (hf : IsMeromorphicUnitOn f U) :
    ∀ᶠ y in codiscreteWithin U, f y ≠ 0 :=
  eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun _ hx =>
    (hf.eventually_ne_zero hx).mono fun _ hy _ => hy

theorem isMeromorphicUnitOn_one : IsMeromorphicUnitOn (1 : M → ℂ) U :=
  ⟨fun x _ => meromorphicAt_const 1 x, fun x _ =>
    (orderAt_ne_top_iff (meromorphicAt_const 1 x)).2 (Eventually.of_forall fun _ => one_ne_zero)⟩

theorem IsMeromorphicUnitOn.mul (hf : IsMeromorphicUnitOn f U) (hg : IsMeromorphicUnitOn g U) :
    IsMeromorphicUnitOn (f * g) U :=
  ⟨hf.1.mul hg.1, fun x hx => (orderAt_ne_top_iff ((hf.1 x hx).mul (hg.1 x hx))).2 <|
    (hf.eventually_ne_zero hx).and (hg.eventually_ne_zero hx) |>.mono fun _ h =>
      mul_ne_zero h.1 h.2⟩

theorem IsMeromorphicUnitOn.inv (hf : IsMeromorphicUnitOn f U) : IsMeromorphicUnitOn f⁻¹ U :=
  ⟨hf.1.inv, fun x hx => (orderAt_ne_top_iff (hf.1 x hx).inv).2 <|
    (hf.eventually_ne_zero hx).mono fun _ h => inv_ne_zero h⟩

theorem IsMeromorphicUnitOn.mono (hf : IsMeromorphicUnitOn f U) (h : V ⊆ U) :
    IsMeromorphicUnitOn f V :=
  ⟨hf.1.mono h, fun x hx => hf.2 x (h hx)⟩

theorem IsMeromorphicUnitOn.congr (hf : IsMeromorphicUnitOn f U) (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) : IsMeromorphicUnitOn g U :=
  ⟨fun x hx => (hf.1 x hx).congr (eventuallyEq_nhdsNE_of_codiscreteWithin h hU hx),
    fun x hx => by
      rw [← orderAt_congr (eventuallyEq_nhdsNE_of_codiscreteWithin h hU hx)]
      exact hf.2 x hx⟩

/-- The germ along `codiscreteWithin U` of a meromorphic unit, as a unit of the germ ring. -/
noncomputable def germUnit (hf : IsMeromorphicUnitOn f U) : (Germ (codiscreteWithin U) ℂ)ˣ where
  val := f
  inv := (f⁻¹ : M → ℂ)
  val_inv := by
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    filter_upwards [hf.eventually_codiscreteWithin_ne_zero] with y hy
    simp [hy]
  inv_val := by
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    filter_upwards [hf.eventually_codiscreteWithin_ne_zero] with y hy
    simp [hy]

variable (U) in
/-- The group of meromorphic functions on `U` vanishing identically near no point of `U`, up to
equality off a discrete subset of `U`: a subgroup of the units of the germs along
`codiscreteWithin U`. -/
def meromorphicUnits : Subgroup (Germ (codiscreteWithin U) ℂ)ˣ where
  carrier := {u | ∃ f : M → ℂ, IsMeromorphicUnitOn f U ∧ (u : Germ (codiscreteWithin U) ℂ) = f}
  one_mem' := ⟨1, isMeromorphicUnitOn_one, (Germ.coe_one).symm⟩
  mul_mem' := by
    rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
    exact ⟨f * g, hf.mul hg, by rw [Units.val_mul, ha, hb, Germ.coe_mul]⟩
  inv_mem' := by
    rintro a ⟨f, hf, ha⟩
    refine ⟨f⁻¹, hf.inv, ?_⟩
    have h1 : ((germUnit hf : (Germ (codiscreteWithin U) ℂ)ˣ) : Germ (codiscreteWithin U) ℂ) =
        a := ha.symm
    have h2 : germUnit hf = a := Units.ext h1
    rw [← h2]
    rfl

/-- The meromorphic unit defined by a function. -/
noncomputable def meromorphicUnitsMk (hf : IsMeromorphicUnitOn f U) : meromorphicUnits U :=
  ⟨germUnit hf, f, hf, rfl⟩

theorem exists_eq_meromorphicUnitsMk (s : meromorphicUnits U) :
    ∃ (f : M → ℂ) (hf : IsMeromorphicUnitOn f U), s = meromorphicUnitsMk hf := by
  obtain ⟨f, hf, h⟩ := s.2
  exact ⟨f, hf, Subtype.ext (Units.ext h)⟩

theorem meromorphicUnitsMk_eq_iff (hf : IsMeromorphicUnitOn f U) (hg : IsMeromorphicUnitOn g U) :
    meromorphicUnitsMk hf = meromorphicUnitsMk hg ↔ f =ᶠ[codiscreteWithin U] g := by
  rw [← Germ.coe_eq, Subtype.ext_iff, Units.ext_iff]
  rfl

theorem meromorphicUnitsMk_mul (hf : IsMeromorphicUnitOn f U) (hg : IsMeromorphicUnitOn g U) :
    meromorphicUnitsMk (hf.mul hg) = meromorphicUnitsMk hf * meromorphicUnitsMk hg :=
  Subtype.ext (Units.ext rfl)

theorem meromorphicUnitsMk_inv (hf : IsMeromorphicUnitOn f U) :
    meromorphicUnitsMk hf.inv = (meromorphicUnitsMk hf)⁻¹ :=
  Subtype.ext (Units.ext rfl)

theorem meromorphicUnitsMk_one :
    meromorphicUnitsMk (isMeromorphicUnitOn_one (U := U)) = 1 :=
  Subtype.ext (Units.ext rfl)

/-- Restriction of germs to a finer filter. -/
def germRestrict {l l' : Filter M} (h : l' ≤ l) : Germ l ℂ →* Germ l' ℂ where
  toFun φ := φ.compTendsto id (tendsto_id'.2 h)
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl

/-- Restriction of meromorphic units from `U` to `V ⊆ U`. -/
noncomputable def meromorphicUnitsRestrict (h : V ⊆ U) :
    meromorphicUnits U →* meromorphicUnits V where
  toFun s := ⟨Units.map (germRestrict (codiscreteWithin_mono h)) s.1, by
    obtain ⟨f, hf, hs⟩ := s.2
    exact ⟨f, hf.mono h, by rw [Units.coe_map, hs]; rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

@[simp]
theorem meromorphicUnitsRestrict_mk (h : V ⊆ U) (hf : IsMeromorphicUnitOn f U) :
    meromorphicUnitsRestrict h (meromorphicUnitsMk hf) = meromorphicUnitsMk (hf.mono h) :=
  Subtype.ext (Units.ext rfl)

end Germs

section DivisorSheaf

variable {M : Type} [TopologicalSpace M]

variable (M) in
/-- The presheaf `U ↦ Div(U)` of divisors: integer-valued functions with locally finite support
in `U`. -/
noncomputable def divisorPresheaf : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) where
  obj U := AddCommGrpCat.of (Function.locallyFinsuppWithin (U.unop : Set M) ℤ)
  map {U V} i := AddCommGrpCat.ofHom
    (Function.locallyFinsuppWithin.restrictMonoidHom (Y := ℤ) (SetLike.coe_subset_coe.2 i.unop.le))
  map_id U := AddCommGrpCat.ext fun D => Function.locallyFinsuppWithin.ext fun x => by
    classical
    let D' : Function.locallyFinsuppWithin (U.unop : Set M) ℤ := D
    change (D'.restrict (subset_refl _)) x = D' x
    rw [Function.locallyFinsuppWithin.restrict_apply]
    split_ifs with h
    · rfl
    · exact (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D' h).symm
  map_comp {U V W} i j := AddCommGrpCat.ext fun D => Function.locallyFinsuppWithin.ext fun x => by
    classical
    let D' : Function.locallyFinsuppWithin (U.unop : Set M) ℤ := D
    change (D'.restrict (SetLike.coe_subset_coe.2 (j.unop.le.trans i.unop.le))) x =
      ((D'.restrict (SetLike.coe_subset_coe.2 i.unop.le)).restrict
        (SetLike.coe_subset_coe.2 j.unop.le)) x
    rw [Function.locallyFinsuppWithin.restrict_apply, Function.locallyFinsuppWithin.restrict_apply,
      Function.locallyFinsuppWithin.restrict_apply]
    by_cases hW : x ∈ (W.unop : Set M)
    · simp [hW, j.unop.le hW]
    · simp [hW]

/-- A section of `divisorPresheaf M`, read as a divisor. -/
abbrev divisorSection {U : (Opens (TopCat.of M))ᵒᵖ} (D : (divisorPresheaf M).obj U) :
    Function.locallyFinsuppWithin (U.unop : Set M) ℤ := D

open scoped Classical in
theorem divisorPresheaf_map_apply {U V : (Opens (TopCat.of M))ᵒᵖ} (i : U ⟶ V)
    (D : (divisorPresheaf M).obj U) (x : M) :
    divisorSection ((divisorPresheaf M).map i D) x =
      if x ∈ (V.unop : Set M) then divisorSection D x else 0 :=
  Function.locallyFinsuppWithin.restrict_apply (divisorSection D)
    (SetLike.coe_subset_coe.2 i.unop.le) x

theorem divisorSection_injective {U : (Opens (TopCat.of M))ᵒᵖ} :
    Function.Injective (divisorSection (M := M) (U := U)) := fun _ _ h => h

theorem isSheaf_divisorPresheaf : (divisorPresheaf M).IsSheaf := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let D : ∀ i, Function.locallyFinsuppWithin (U i : Set M) ℤ := fun i => divisorSection (sf i)
  have hcompat : ∀ i j, ∀ x ∈ (U i : Set M), x ∈ (U j : Set M) → D i x = D j x := by
    intro i j x hi hj
    have h := (divisorPresheaf_map_apply _ (sf i) x).symm.trans
      ((congrArg (fun E => divisorSection E x) (hsf i j)).trans
        (divisorPresheaf_map_apply _ (sf j) x))
    simpa [hi, hj] using h
  let G : M → ℤ := fun y => if h : ∃ i, y ∈ U i then D h.choose y else 0
  have hG : ∀ i, ∀ y ∈ (U i : Set M), G y = D i y := by
    intro i y hy
    have h : ∃ i, y ∈ U i := ⟨i, hy⟩
    simp only [G, h, dite_true]
    exact hcompat _ _ y h.choose_spec hy
  let Glued : Function.locallyFinsuppWithin ((iSup U : Opens (TopCat.of M)) : Set M) ℤ :=
    { toFun := G
      supportWithinDomain' := by
        intro y hy
        by_contra h'
        apply hy
        have : ¬∃ i, y ∈ U i := fun ⟨i, hi⟩ => h' (Opens.mem_iSup.2 ⟨i, hi⟩)
        simp only [G, this, dite_false]
      supportLocallyFiniteWithinDomain' := by
        intro z hz
        obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hz
        obtain ⟨t, ht, htf⟩ := (D i).supportLocallyFiniteWithinDomain' z hi
        refine ⟨t ∩ U i, inter_mem ht ((U i).isOpen.mem_nhds hi), htf.subset ?_⟩
        rintro y ⟨⟨hyt, hyU⟩, hy⟩
        refine ⟨hyt, ?_⟩
        change D i y ≠ 0
        rw [← hG i y hyU]
        exact hy }
  let Glued' : (divisorPresheaf M).obj (op (iSup U)) := Glued
  refine ⟨Glued', ?_, ?_⟩
  · intro i
    apply divisorSection_injective
    ext y
    refine (divisorPresheaf_map_apply _ Glued' y).trans ?_
    change (if y ∈ (U i : Set M) then G y else 0) = D i y
    split_ifs with hy
    · exact hG i y hy
    · exact (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem (D i) hy).symm
  · intro E hE
    apply divisorSection_injective
    ext y
    change divisorSection E y = G y
    by_cases hy : ∃ i, y ∈ U i
    · obtain ⟨i, hi⟩ := hy
      have h := (divisorPresheaf_map_apply _ E y).symm.trans
        (congrArg (fun E => divisorSection E y) (hE i))
      rw [hG i y hi]
      simpa [show y ∈ (U i : Set M) from hi] using h
    · have hy' : y ∉ ((iSup U : Opens (TopCat.of M)) : Set M) :=
        fun h => hy (Opens.mem_iSup.1 h)
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hy']
      simp only [G, hy, dite_false]

variable (M) in
/-- The sheaf `Div_M` of divisors, `U ↦ Function.locallyFinsuppWithin U ℤ`. -/
noncomputable def divisorSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} :=
  ⟨divisorPresheaf M, isSheaf_divisorPresheaf⟩

end DivisorSheaf

section Sheaves

variable (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M]

theorem meromorphicUnitsRestrict_id (U : Set M) :
    meromorphicUnitsRestrict (subset_refl U) = MonoidHom.id (meromorphicUnits U) := by
  ext1 s
  obtain ⟨f, hf, rfl⟩ := exists_eq_meromorphicUnitsMk s
  rfl

variable {M} in
theorem meromorphicUnitsRestrict_comp {U V W : Set M} (hVU : V ⊆ U) (hWV : W ⊆ V) :
    meromorphicUnitsRestrict (hWV.trans hVU) =
      (meromorphicUnitsRestrict hWV).comp (meromorphicUnitsRestrict hVU) := by
  ext1 s
  obtain ⟨f, hf, rfl⟩ := exists_eq_meromorphicUnitsMk s
  rfl

/-- The presheaf `U ↦ 𝓜_M^×(U)` of meromorphic functions vanishing identically near no point,
modulo equality off discrete subsets, written additively. -/
noncomputable def meromorphicUnitsPresheaf : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) where
  obj U := AddCommGrpCat.of (Additive (meromorphicUnits (U.unop : Set M)))
  map i := AddCommGrpCat.ofHom (MonoidHom.toAdditive (meromorphicUnitsRestrict i.unop.le))
  map_id U := AddCommGrpCat.ext fun s => congrArg Additive.ofMul
    (DFunLike.congr_fun (meromorphicUnitsRestrict_id M (U.unop : Set M)) (Additive.toMul s))
  map_comp i j := AddCommGrpCat.ext fun s => congrArg Additive.ofMul
    (DFunLike.congr_fun (meromorphicUnitsRestrict_comp i.unop.le j.unop.le) (Additive.toMul s))

variable {M}

theorem meromorphicUnitsPresheaf_map_apply {U V : (Opens (TopCat.of M))ᵒᵖ} (i : U ⟶ V)
    (s : (meromorphicUnitsPresheaf M).obj U) :
    Additive.toMul ((meromorphicUnitsPresheaf M).map i s) =
      meromorphicUnitsRestrict i.unop.le (Additive.toMul s) := rfl

theorem meromorphicUnitsPresheaf_map_ofMul_mk {U V : (Opens (TopCat.of M))ᵒᵖ} (i : U ⟶ V)
    {f : M → ℂ} (hf : IsMeromorphicUnitOn f (U.unop : Set M)) :
    (meromorphicUnitsPresheaf M).map i (Additive.ofMul (meromorphicUnitsMk hf)) =
      Additive.ofMul (meromorphicUnitsMk (hf.mono i.unop.le)) := rfl

theorem isSheaf_meromorphicUnitsPresheaf : (meromorphicUnitsPresheaf M).IsSheaf := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  choose f hf hsfeq using fun i => exists_eq_meromorphicUnitsMk (Additive.toMul (sf i))
  have hsf' : ∀ i, sf i = Additive.ofMul (meromorphicUnitsMk (hf i)) := fun i => by
    rw [← hsfeq i]; rfl
  have hcompat : ∀ i j, f i =ᶠ[codiscreteWithin ((U i : Set M) ∩ U j)] f j := by
    intro i j
    have h := hsf i j
    rw [hsf' i, hsf' j] at h
    have h2 := (meromorphicUnitsPresheaf_map_ofMul_mk _ _).symm.trans
      (h.trans (meromorphicUnitsPresheaf_map_ofMul_mk _ _))
    exact (meromorphicUnitsMk_eq_iff _ _).1 (Additive.ofMul.injective h2)
  let F : M → ℂ := fun y => if h : ∃ i, y ∈ U i then limUnder (𝓝[≠] y) (f h.choose) else 0
  have hF : ∀ i, ∀ x ∈ U i, F =ᶠ[𝓝[≠] x] f i := by
    intro i x hx
    filter_upwards [((hf i).1 x hx).eventually_continuousAt,
      mem_nhdsWithin_of_mem_nhds ((U i).isOpen.mem_nhds hx)] with y hyc hyU
    have h : ∃ i, y ∈ U i := ⟨i, hyU⟩
    simp only [F, h, dite_true]
    rw [limUnder_nhdsNE_congr (eventuallyEq_nhdsNE_of_codiscreteWithin (hcompat h.choose i)
      ((U h.choose).isOpen.inter (U i).isOpen) ⟨h.choose_spec, hyU⟩),
      limUnder_nhdsNE_eq_of_continuousAt hyc]
  have hFu : IsMeromorphicUnitOn F ((iSup U : Opens (TopCat.of M)) : Set M) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
      exact ((hf i).1 x hi).congr (hF i x hi).symm
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
      rw [orderAt_congr (hF i x hi)]
      exact (hf i).2 x hi
  refine ⟨Additive.ofMul (meromorphicUnitsMk hFu), ?_, ?_⟩
  · intro i
    rw [hsf' i]
    refine (meromorphicUnitsPresheaf_map_ofMul_mk _ _).trans (congrArg Additive.ofMul ?_)
    rw [meromorphicUnitsMk_eq_iff]
    exact eventuallyEq_codiscreteWithin_of_nhdsNE (hF i)
  · intro t ht
    obtain ⟨G, hG, hGt⟩ := exists_eq_meromorphicUnitsMk (Additive.toMul t)
    have ht' : t = Additive.ofMul (meromorphicUnitsMk hG) := by rw [← hGt]; rfl
    subst ht'
    have hGi : ∀ i, G =ᶠ[codiscreteWithin (U i : Set M)] f i := by
      intro i
      have h := ht i
      rw [hsf' i] at h
      exact (meromorphicUnitsMk_eq_iff _ _).1
        (Additive.ofMul.injective ((meromorphicUnitsPresheaf_map_ofMul_mk _ _).symm.trans h))
    refine congrArg Additive.ofMul ((meromorphicUnitsMk_eq_iff _ _).2 ?_)
    refine eventuallyEq_codiscreteWithin_of_nhdsNE fun x hx => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact (eventuallyEq_nhdsNE_of_codiscreteWithin (hGi i) (U i).isOpen hi).trans (hF i x hi).symm

variable (M) in
/-- The sheaf `𝓜_M^×` of meromorphic functions vanishing identically near no point, modulo
equality off discrete subsets, as a sheaf of abelian groups (written additively). -/
noncomputable def meromorphicUnitsSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} :=
  ⟨meromorphicUnitsPresheaf M, isSheaf_meromorphicUnitsPresheaf⟩

end Sheaves

section Analytic

theorem eventually_eventuallyEq_nhdsNE {X β : Type*} [TopologicalSpace X] [T1Space X]
    {f k : X → β} {x : X} (h : f =ᶠ[𝓝[≠] x] k) : ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝[≠] y] k := by
  have h' : ∀ᶠ z in 𝓝 x, z ≠ x → f z = k z := eventually_nhdsWithin_iff.1 h
  filter_upwards [h'.eventually_nhds] with y hy
  by_cases hyx : y = x
  · subst hyx
    exact h
  · have : ∀ᶠ z in 𝓝 y, f z = k z := by
      filter_upwards [hy, isOpen_ne.mem_nhds hyx] with z hz hz' using hz hz'
    exact this.filter_mono nhdsWithin_le_nhds

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {f g : M → ℂ} {x : M} {U V : Set M}

theorem eq_of_eventuallyEq_nhdsNE (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f =ᶠ[𝓝[≠] x] g) : f x = g x := by
  have := nhdsNE_neBot x
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- The limit of `f` along the punctured neighbourhoods: the normal form of a meromorphic function
without poles. -/
noncomputable def limNhdsNE (f : M → ℂ) : M → ℂ := fun y => limUnder (𝓝[≠] y) f

variable [IsManifold 𝓘(ℂ) 1 M]

/-- A function holomorphic near `x` and nonzero at `x` has order `0` at `x`. -/
theorem orderAt_eq_zero_of_eventually_mdifferentiableAt
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (h0 : f x ≠ 0) : orderAt f x = 0 := by
  have ha := analyticAt_comp_symm_of_eventually_mdifferentiableAt (chart_mem_atlas ℂ x)
    (mem_chart_source ℂ x) hf
  have h := (meromorphicOrderAt_eq_int_iff ha.meromorphicAt (n := 0)).2
    ⟨_, ha, by simpa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using h0,
      Eventually.of_forall fun z => by simp⟩
  exact h

variable [T2Space M]

/-- A meromorphic function of order `0` at `x` agrees near `x` (off `x`) with its limit function,
which is holomorphic near `x` and nonzero at `x`. -/
theorem MeromorphicAt.limNhdsNE_spec (hf : MeromorphicAt f x) (h0 : orderAt f x = 0) :
    (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (limNhdsNE f) y) ∧ limNhdsNE f x ≠ 0 ∧
      limNhdsNE f =ᶠ[𝓝[≠] x] f := by
  set e := chartAt ℂ x
  have he : e ∈ atlas ℂ M := chart_mem_atlas ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hf' : _root_.MeromorphicAt (f ∘ e.symm) (e x) := hf
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf' (n := 0)).1
    (by rw [WithTop.coe_zero]; exact h0)
  have hcont : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have := e.continuousAt_symm (e.map_source hx)
    rwa [ContinuousAt, e.left_inv hx] at this
  have hk_cont : ∀ᶠ y in 𝓝 x, ContinuousAt (g ∘ e) y := by
    filter_upwards [(e.continuousAt hx).eventually hg.eventually_analyticAt,
      e.open_source.mem_nhds hx] with y hy hys
    exact hy.continuousAt.comp (e.continuousAt hys)
  have hfk : f =ᶠ[𝓝[≠] x] g ∘ e := by
    rw [EventuallyEq, eventually_nhdsNE_iff_of_mem_source e hx]
    have htgt : ∀ᶠ z in 𝓝[≠] (e x), z ∈ e.target :=
      mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source hx))
    filter_upwards [hfg, htgt] with z hz hzt
    simp only [zpow_zero, one_smul, Function.comp_apply] at hz
    simp only [Function.comp_apply, e.right_inv hzt]
    exact hz
  have hlim : limNhdsNE f =ᶠ[𝓝 x] g ∘ e := by
    filter_upwards [eventually_eventuallyEq_nhdsNE hfk, hk_cont] with y hy hyc
    exact (limUnder_nhdsNE_congr hy).trans (limUnder_nhdsNE_eq_of_continuousAt hyc)
  refine ⟨?_, ?_, ?_⟩
  · refine eventually_mdifferentiableAt_of_analyticAt_comp_symm he hx (hg.congr ?_)
    filter_upwards [hcont.eventually hlim, e.open_target.mem_nhds (e.map_source hx)] with z hz hzt
    simp only [Function.comp_apply] at hz ⊢
    rw [hz, e.right_inv hzt]
  · rw [hlim.self_of_nhds]
    simpa [e.left_inv hx] using hg0
  · exact (hlim.filter_mono nhdsWithin_le_nhds).trans hfk.symm

end Analytic

section ChartRational

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]

open scoped Classical in
/-- The exponents `D`, read in the chart `e`: `z ↦ D (e.symm z)` on the target of `e`. -/
noncomputable def chartExponents (e : OpenPartialHomeomorph M ℂ) (D : M → ℤ) : ℂ → ℤ :=
  fun z => if z ∈ e.target then D (e.symm z) else 0

/-- The function `y ↦ ∏ₐ (e y - e a) ^ D a`: in the chart `e` it is the factorized rational
function with exponents `D`. -/
noncomputable def chartRational (e : OpenPartialHomeomorph M ℂ) (D : M → ℤ) : M → ℂ :=
  fun y => (∏ᶠ u, (fun z => z - u) ^ chartExponents e D u) (e y)

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] in
theorem hasFiniteSupport_chartExponents (e : OpenPartialHomeomorph M ℂ) {D : M → ℤ}
    (hD : D.support.Finite) : Function.HasFiniteSupport (chartExponents e D) := by
  refine (hD.image e).subset ?_
  intro z hz
  simp only [Function.mem_support, chartExponents, ne_eq, ite_eq_right_iff, Classical.not_imp] at hz
  exact ⟨e.symm z, hz.2, e.right_inv hz.1⟩

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] in
theorem chartRational_comp_symm_eventuallyEq (e : OpenPartialHomeomorph M ℂ) (D : M → ℤ)
    {y : M} (hy : y ∈ e.source) :
    chartRational e D ∘ e.symm =ᶠ[𝓝 (e y)] ∏ᶠ u, (fun z => z - u) ^ chartExponents e D u := by
  filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with z hz
  simp [chartRational, e.right_inv hz]

theorem meromorphicAt_chartRational {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (D : M → ℤ) {y : M} (hy : y ∈ e.source) : MeromorphicAt (chartRational e D) y := by
  rw [meromorphicAt_iff_of_mem_atlas he hy]
  exact ((Function.FactorizedRational.meromorphicNFOn (chartExponents e D) univ).meromorphicOn
    (e y) (mem_univ _)).congr
    ((chartRational_comp_symm_eventuallyEq e D hy).symm.filter_mono nhdsWithin_le_nhds)

theorem orderAt_chartRational {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    {D : M → ℤ} (hD : D.support.Finite) {y : M} (hy : y ∈ e.source) :
    orderAt (chartRational e D) y = D y := by
  rw [orderAt_eq_of_mem_atlas he hy, meromorphicOrderAt_congr
    ((chartRational_comp_symm_eventuallyEq e D hy).filter_mono nhdsWithin_le_nhds),
    Function.FactorizedRational.meromorphicOrderAt_eq _ (hasFiniteSupport_chartExponents e hD)]
  simp [chartExponents, e.map_source hy, e.left_inv hy]

theorem isMeromorphicUnitOn_chartRational {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    {D : M → ℤ} (hD : D.support.Finite) {U : Set M} (hU : U ⊆ e.source) :
    IsMeromorphicUnitOn (chartRational e D) U :=
  ⟨fun _ hy => meromorphicAt_chartRational he D (hU hy), fun _ hy => by
    rw [orderAt_chartRational he hD (hU hy)]
    exact WithTop.coe_ne_top⟩

end ChartRational

section DivisorSequence

open scoped ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] in
theorem eventuallyEq_codiscreteWithin_of_eqOn {U : Set M} {f g : M → ℂ} (h : EqOn f g U) :
    f =ᶠ[codiscreteWithin U] g :=
  eventually_of_mem (self_mem_codiscreteWithin U) h

/-! ### The map `𝒪_M^× ⟶ 𝓜_M^×` -/

open Classical in
/-- A nowhere vanishing holomorphic function on `U`, extended by `1` to `M`. -/
noncomputable def unitsExtend {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) : M → ℂ :=
  fun y => if h : y ∈ U then ((u ⟨y, h⟩ : ℂˣ) : ℂ) else 1

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem unitsExtend_of_mem {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) {y : M} (hy : y ∈ U) :
    unitsExtend u y = ((u ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  simp [unitsExtend, hy]

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem unitsExtend_ne_zero {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) (y : M) :
    unitsExtend u y ≠ 0 := by
  by_cases hy : y ∈ U
  · rw [unitsExtend_of_mem u hy]
    exact Units.ne_zero _
  · simp [unitsExtend, hy]

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem mdifferentiableAt_unitsExtend {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) {y : M}
    (hy : y ∈ U) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (unitsExtend u) y := by
  have h1 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (fun z : U => ((u z : ℂˣ) : ℂ)) :=
    Units.contMDiff_val.comp u.contMDiff
  have h2 : (fun z : U => unitsExtend u z) = fun z : U => ((u z : ℂˣ) : ℂ) :=
    funext fun z => unitsExtend_of_mem u z.2
  have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (unitsExtend u) (⟨y, hy⟩ : U) :=
    contMDiffAt_subtype_iff.1 (by rw [h2]; exact h1 _)
  exact h3.mdifferentiableAt (by simp)

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem eventually_mdifferentiableAt_unitsExtend {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯)
    {y : M} (hy : y ∈ U) : ∀ᶠ z in 𝓝 y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (unitsExtend u) z :=
  eventually_of_mem (U.isOpen.mem_nhds hy) fun _ hz => mdifferentiableAt_unitsExtend u hz

theorem orderAt_unitsExtend {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) {y : M} (hy : y ∈ U) :
    orderAt (unitsExtend u) y = 0 :=
  orderAt_eq_zero_of_eventually_mdifferentiableAt (eventually_mdifferentiableAt_unitsExtend u hy)
    (unitsExtend_ne_zero u y)

theorem isMeromorphicUnitOn_unitsExtend {U : Opens M} (u : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) :
    IsMeromorphicUnitOn (unitsExtend u) (U : Set M) :=
  ⟨fun _ hy => meromorphicAt_of_eventually_mdifferentiableAt
      (eventually_mdifferentiableAt_unitsExtend u hy),
    fun _ hy => by rw [orderAt_unitsExtend u hy]; exact WithTop.zero_ne_top⟩

/-- On sections over `U`: a nowhere vanishing holomorphic function is a meromorphic unit. -/
noncomputable def unitsToMeromorphicUnits (U : Opens M) :
    Additive C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯ →+ Additive (meromorphicUnits (U : Set M)) where
  toFun u := Additive.ofMul (meromorphicUnitsMk (isMeromorphicUnitOn_unitsExtend u.toMul))
  map_zero' := by
    refine congrArg Additive.ofMul ((meromorphicUnitsMk_eq_iff _ isMeromorphicUnitOn_one).2
      (Eventually.of_forall fun y => ?_) |>.trans meromorphicUnitsMk_one)
    by_cases hy : y ∈ U
    · rw [unitsExtend_of_mem _ hy]
      rfl
    · simp [unitsExtend, hy]
  map_add' u v := by
    refine congrArg Additive.ofMul (((meromorphicUnitsMk_eq_iff _
      ((isMeromorphicUnitOn_unitsExtend u.toMul).mul (isMeromorphicUnitOn_unitsExtend v.toMul))).2
      (Eventually.of_forall fun y => ?_)).trans (meromorphicUnitsMk_mul _ _))
    by_cases hy : y ∈ U
    · simp only [Pi.mul_apply, unitsExtend_of_mem _ hy]
      rfl
    · simp [unitsExtend, hy]

theorem unitsToMeromorphicUnits_apply (U : Opens M) (u : Additive C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂˣ⟯) :
    unitsToMeromorphicUnits U u =
      Additive.ofMul (meromorphicUnitsMk (isMeromorphicUnitOn_unitsExtend u.toMul)) := rfl

variable (M) in
/-- The inclusion `𝒪_M^× ⟶ 𝓜_M^×` of nowhere vanishing holomorphic functions into the
meromorphic units. -/
noncomputable def holomorphicUnitsToMeromorphicUnits :
    ComplexManifold.holomorphicUnitsSheaf 𝓘(ℂ) M ⟶ meromorphicUnitsSheaf M :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (unitsToMeromorphicUnits U.unop)
    naturality := fun U V i => AddCommGrpCat.ext fun u => by
      let u' : C^∞⟮𝓘(ℂ), U.unop; 𝓘(ℂ), ℂˣ⟯ := Additive.toMul u
      let v' : C^∞⟮𝓘(ℂ), V.unop; 𝓘(ℂ), ℂˣ⟯ :=
        Additive.toMul ((ComplexManifold.holomorphicUnitsSheaf 𝓘(ℂ) M).obj.map i u)
      have hv : ∀ y (hy : y ∈ V.unop), (v' ⟨y, hy⟩ : ℂˣ) = u' ⟨y, i.unop.le hy⟩ := fun _ _ => rfl
      exact congrArg Additive.ofMul ((meromorphicUnitsMk_eq_iff (isMeromorphicUnitOn_unitsExtend v')
        ((isMeromorphicUnitOn_unitsExtend u').mono (SetLike.coe_subset_coe.2 i.unop.le))).2
        (eventuallyEq_codiscreteWithin_of_eqOn fun y hy => by
          rw [unitsExtend_of_mem _ hy, unitsExtend_of_mem _ (i.unop.le hy), hv])) }

/-! ### The map `𝓜_M^× ⟶ Div_M` -/

theorem divisorOn_congr_codiscreteWithin {U : Set M} (hU : IsOpen U) {f g : M → ℂ}
    (hf : MeromorphicOn f U) (h : f =ᶠ[codiscreteWithin U] g) : divisorOn f U = divisorOn g U := by
  have hg : MeromorphicOn g U := fun x hx =>
    (hf x hx).congr (eventuallyEq_nhdsNE_of_codiscreteWithin h hU hx)
  ext x
  by_cases hx : x ∈ U
  · rw [divisorOn_apply hf hx, divisorOn_apply hg hx,
      orderAt_congr (eventuallyEq_nhdsNE_of_codiscreteWithin h hU hx)]
  · rw [divisorOn_apply_of_notMem hx, divisorOn_apply_of_notMem hx]

/-- The divisor of a meromorphic unit. -/
noncomputable def divisorOfMeromorphicUnit {U : Set M} (s : meromorphicUnits U) :
    Function.locallyFinsuppWithin U ℤ :=
  divisorOn (exists_eq_meromorphicUnitsMk s).choose U

theorem divisorOfMeromorphicUnit_mk {U : Set M} (hU : IsOpen U) {f : M → ℂ}
    (hf : IsMeromorphicUnitOn f U) :
    divisorOfMeromorphicUnit (meromorphicUnitsMk hf) = divisorOn f U := by
  obtain ⟨hg, hs⟩ := (exists_eq_meromorphicUnitsMk (meromorphicUnitsMk hf)).choose_spec
  exact (divisorOn_congr_codiscreteWithin hU hf.1 ((meromorphicUnitsMk_eq_iff _ _).1 hs)).symm

theorem divisorOn_one {U : Set M} : divisorOn (1 : M → ℂ) U = 0 := by
  ext x
  by_cases hx : x ∈ U
  · have h1 : MeromorphicOn (1 : M → ℂ) U := meromorphicOn_const 1 U
    rw [divisorOn_apply h1 hx, orderAt_eq_zero_of_eventually_mdifferentiableAt (f := (1 : M → ℂ))
      (Eventually.of_forall fun _ => mdifferentiableAt_const) one_ne_zero]
    rfl
  · rw [divisorOn_apply_of_notMem hx]
    rfl

/-- On sections over `U`: the divisor of a meromorphic unit. -/
noncomputable def meromorphicUnitsToDivisors (U : Opens M) :
    Additive (meromorphicUnits (U : Set M)) →+ Function.locallyFinsuppWithin (U : Set M) ℤ where
  toFun s := divisorOfMeromorphicUnit s.toMul
  map_zero' := by
    change divisorOfMeromorphicUnit 1 = 0
    rw [← meromorphicUnitsMk_one, divisorOfMeromorphicUnit_mk U.isOpen, divisorOn_one]
  map_add' s t := by
    obtain ⟨f, hf, hs⟩ := exists_eq_meromorphicUnitsMk s.toMul
    obtain ⟨g, hg, ht⟩ := exists_eq_meromorphicUnitsMk t.toMul
    change divisorOfMeromorphicUnit (s.toMul * t.toMul) = _ + _
    rw [hs, ht, ← meromorphicUnitsMk_mul, divisorOfMeromorphicUnit_mk U.isOpen,
      divisorOfMeromorphicUnit_mk U.isOpen, divisorOfMeromorphicUnit_mk U.isOpen,
      divisorOn_mul hf.1 hg.1 hf.2 hg.2]

theorem meromorphicUnitsToDivisors_ofMul_mk (U : Opens M) {f : M → ℂ}
    (hf : IsMeromorphicUnitOn f (U : Set M)) :
    meromorphicUnitsToDivisors U (Additive.ofMul (meromorphicUnitsMk hf)) = divisorOn f U :=
  divisorOfMeromorphicUnit_mk U.isOpen hf

variable (M) in
/-- The divisor map `𝓜_M^× ⟶ Div_M`. -/
noncomputable def meromorphicUnitsToDivisor : meromorphicUnitsSheaf M ⟶ divisorSheaf M :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (meromorphicUnitsToDivisors U.unop)
    naturality := fun U V i => AddCommGrpCat.ext fun s => by
      classical
      obtain ⟨f, hf, hs⟩ := exists_eq_meromorphicUnitsMk (Additive.toMul s)
      have hs' : s = Additive.ofMul (meromorphicUnitsMk hf) := by rw [← hs]; rfl
      subst hs'
      apply divisorSection_injective
      ext x
      refine Eq.trans ?_ (divisorPresheaf_map_apply i _ x).symm
      change divisorSection (meromorphicUnitsToDivisors V.unop (Additive.ofMul
        (meromorphicUnitsMk (hf.mono (SetLike.coe_subset_coe.2 i.unop.le))))) x =
        if x ∈ (V.unop : Set M) then divisorSection (meromorphicUnitsToDivisors U.unop
          (Additive.ofMul (meromorphicUnitsMk hf))) x else 0
      rw [meromorphicUnitsToDivisors_ofMul_mk, meromorphicUnitsToDivisors_ofMul_mk]
      by_cases hx : x ∈ (V.unop : Set M)
      · rw [ite_eq_left hx, divisorOn_apply (hf.1.mono (SetLike.coe_subset_coe.2 i.unop.le)) hx,
          divisorOn_apply hf.1 (i.unop.le hx)]
      · rw [ite_eq_right hx, divisorOn_apply_of_notMem hx] }

theorem holomorphicUnitsToMeromorphicUnits_app_apply (U : (Opens (TopCat.of M))ᵒᵖ)
    (u : C^∞⟮𝓘(ℂ), U.unop; 𝓘(ℂ), ℂˣ⟯) :
    (holomorphicUnitsToMeromorphicUnits M).hom.app U (Additive.ofMul u) =
      Additive.ofMul (meromorphicUnitsMk (isMeromorphicUnitOn_unitsExtend u)) := rfl

theorem meromorphicUnitsToDivisor_app_ofMul_mk (U : (Opens (TopCat.of M))ᵒᵖ) {f : M → ℂ}
    (hf : IsMeromorphicUnitOn f (U.unop : Set M)) :
    divisorSection ((meromorphicUnitsToDivisor M).hom.app U
      (Additive.ofMul (meromorphicUnitsMk hf))) = divisorOn f U.unop :=
  meromorphicUnitsToDivisors_ofMul_mk U.unop hf

variable (M) in
theorem holomorphicUnitsToMeromorphicUnits_comp_meromorphicUnitsToDivisor :
    holomorphicUnitsToMeromorphicUnits M ≫ meromorphicUnitsToDivisor M = 0 := by
  ext U u
  apply divisorSection_injective
  ext x
  let u' : C^∞⟮𝓘(ℂ), U.unop; 𝓘(ℂ), ℂˣ⟯ := Additive.toMul u
  change divisorSection (meromorphicUnitsToDivisors U.unop
    (Additive.ofMul (meromorphicUnitsMk (isMeromorphicUnitOn_unitsExtend u')))) x = 0
  rw [meromorphicUnitsToDivisors_ofMul_mk]
  by_cases hx : x ∈ (U.unop : Set M)
  · rw [divisorOn_apply (isMeromorphicUnitOn_unitsExtend _).1 hx, orderAt_unitsExtend _ hx]
    rfl
  · rw [divisorOn_apply_of_notMem hx]

variable (M) in
/-- The **divisor sequence** `0 ⟶ 𝒪_M^× ⟶ 𝓜_M^× ⟶ Div_M ⟶ 0` of a Riemann surface. -/
noncomputable abbrev divisorSequence :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk (holomorphicUnitsToMeromorphicUnits M) (meromorphicUnitsToDivisor M)
    (holomorphicUnitsToMeromorphicUnits_comp_meromorphicUnitsToDivisor M)

theorem injective_unitsToMeromorphicUnits (U : Opens M) :
    Function.Injective (unitsToMeromorphicUnits U) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  have h1 : meromorphicUnitsMk (isMeromorphicUnitOn_unitsExtend u.toMul) =
      meromorphicUnitsMk (isMeromorphicUnitOn_one (U := (U : Set M))) :=
    (Additive.ofMul.injective hu).trans meromorphicUnitsMk_one.symm
  have h2 := (meromorphicUnitsMk_eq_iff _ _).1 h1
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun z => Units.ext ?_
  have h3 := eq_of_eventuallyEq_nhdsNE (mdifferentiableAt_unitsExtend u.toMul z.2).continuousAt
    continuousAt_const (eventuallyEq_nhdsNE_of_codiscreteWithin h2 U.isOpen z.2)
  rw [unitsExtend_of_mem _ z.2] at h3
  exact h3

variable (M) in
instance mono_holomorphicUnitsToMeromorphicUnits :
    Mono (holomorphicUnitsToMeromorphicUnits M) := by
  have : Mono ((sheafToPresheaf _ _).map (holomorphicUnitsToMeromorphicUnits M)) := by
    have hU : ∀ U, Mono (((sheafToPresheaf _ _).map
        (holomorphicUnitsToMeromorphicUnits M)).app U) := by
      intro U
      rw [AddCommGrpCat.mono_iff_injective]
      exact injective_unitsToMeromorphicUnits U.unop
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

variable (M) in
instance epi_meromorphicUnitsToDivisor : Epi (meromorphicUnitsToDivisor M) := by
  classical
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi (X := TopCat.of M) _).mp ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  let D : Function.locallyFinsuppWithin (U : Set M) ℤ := t
  set e := chartAt ℂ x
  obtain ⟨T, hT, hTf⟩ := D.supportLocallyFiniteWithinDomain' x hx
  obtain ⟨W, hWT, hWo, hxW⟩ := mem_nhds_iff.1 hT
  let V : Opens (TopCat.of M) := U ⊓ ⟨e.source, e.open_source⟩ ⊓ ⟨W, hWo⟩
  have hVU : V ≤ U := inf_le_left.trans inf_le_left
  have hVs : (V : Set M) ⊆ e.source := fun y hy => hy.1.2
  let D' : M → ℤ := fun y => if y ∈ (V : Set M) then D y else 0
  have hD'f : D'.support.Finite := by
    refine hTf.subset fun y hy => ?_
    simp only [Function.mem_support, D', ne_eq, ite_eq_right_iff, Classical.not_imp] at hy
    exact ⟨hWT hy.1.2, hy.2⟩
  have hφ := isMeromorphicUnitOn_chartRational (chart_mem_atlas ℂ x) hD'f hVs
  refine ⟨V, hVU, ⟨Additive.ofMul (meromorphicUnitsMk hφ), ?_⟩,
    ⟨⟨hx, mem_chart_source ℂ x⟩, hxW⟩⟩
  apply divisorSection_injective
  ext y
  refine Eq.trans ?_ (divisorPresheaf_map_apply (homOfLE hVU).op t y).symm
  change divisorSection (meromorphicUnitsToDivisors V (Additive.ofMul (meromorphicUnitsMk hφ))) y =
    if y ∈ (V : Set M) then D y else 0
  rw [meromorphicUnitsToDivisors_ofMul_mk]
  by_cases hy : y ∈ (V : Set M)
  · rw [ite_eq_left hy, divisorOn_apply hφ.1 hy,
      orderAt_chartRational (chart_mem_atlas ℂ x) hD'f (hVs hy), WithTop.untop₀_coe]
    exact ite_eq_left hy
  · rw [ite_eq_right hy, divisorOn_apply_of_notMem hy]

variable [T2Space M]

variable (M) in
theorem divisorSequence_exact : (divisorSequence M).Exact := by
  apply TopCat.Sheaf.exact_of_exists_local_preimage
  intro U s hs x hx
  obtain ⟨f, hf, hsf⟩ := exists_eq_meromorphicUnitsMk (Additive.toMul s)
  have hs' : s = Additive.ofMul (meromorphicUnitsMk hf) := by rw [← hsf]; rfl
  subst hs'
  have hdiv : divisorOn f U = 0 := (meromorphicUnitsToDivisors_ofMul_mk U hf).symm.trans hs
  have h0 : ∀ y ∈ (U : Set M), orderAt f y = 0 := fun y hy => by
    have h := congrArg (fun E : Function.locallyFinsuppWithin (U : Set M) ℤ => E y) hdiv
    simp only [divisorOn_apply hf.1 hy] at h
    rw [← WithTop.coe_untop₀_of_ne_top (hf.2 y hy), h]
    rfl
  have hspec := fun y (hy : y ∈ (U : Set M)) => (hf.1 y hy).limNhdsNE_spec (h0 y hy)
  let w : U → ℂˣ := fun y => Units.mk0 (limNhdsNE f y) (hspec y y.2).2.1
  have hw : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ w := by
    refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
    intro y
    have : (Units.val ∘ w) = fun z : U => limNhdsNE f z := rfl
    rw [this]
    exact contMDiffAt_subtype_iff.2 (contMDiffAt_of_eventually_mdifferentiableAt (hspec y y.2).1)
  refine ⟨U, le_rfl, hx, Additive.ofMul ⟨w, hw⟩, ?_⟩
  refine congrArg Additive.ofMul ((meromorphicUnitsMk_eq_iff _ (hf.mono subset_rfl)).2 ?_)
  refine eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun y hy => ?_
  filter_upwards [(hspec y hy).2.2] with z hz hzU
  rw [unitsExtend_of_mem _ hzU]
  exact hz

variable (M) in
/-- **The divisor sequence is short exact**: `𝒪_M^× ⟶ 𝓜_M^×` is injective, its image is the
kernel of the divisor map (a meromorphic function without zeros and poles is holomorphic and
nowhere vanishing after correction on a discrete set), and every divisor is locally the divisor
of a meromorphic function. -/
theorem shortExact_divisorSequence : (divisorSequence M).ShortExact :=
  ShortComplex.ShortExact.mk' (divisorSequence_exact M)
    (mono_holomorphicUnitsToMeromorphicUnits M) (epi_meromorphicUnitsToDivisor M)

end DivisorSequence

section Cech

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] [T2Space M]

/-- **Meromorphic cocycles split.** On a compact Riemann surface, let `W` be a finite open cover
by subsets of chart domains and `F i j` meromorphic functions on `W i ∩ W j`, vanishing
identically near no point, satisfying the cocycle condition `F i k = F i j * F j k` off discrete
sets. Then after shrinking the cover, `F i j = h i / h j` off discrete sets, for meromorphic `h i`
on the shrunken members. -/
theorem exists_meromorphic_coboundary [CompactSpace M] {ι : Type*} [Finite ι]
    (W : ι → Set M) (hWo : ∀ i, IsOpen (W i)) (hcov : ⋃ i, W i = univ)
    (e : ι → OpenPartialHomeomorph M ℂ) (he : ∀ i, e i ∈ atlas ℂ M)
    (hWe : ∀ i, W i ⊆ (e i).source)
    (F : ι → ι → M → ℂ) (hF : ∀ i j, IsMeromorphicUnitOn (F i j) (W i ∩ W j))
    (hcoc : ∀ i j k, F i k =ᶠ[codiscreteWithin (W i ∩ W j ∩ W k)] F i j * F j k) :
    ∃ V : ι → Set M, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ W i) ∧ ⋃ i, V i = univ ∧
      ∃ h : ι → M → ℂ, (∀ i, IsMeromorphicUnitOn (h i) (V i)) ∧
        ∀ i j, F i j =ᶠ[codiscreteWithin (V i ∩ V j)] h i * (h j)⁻¹ := by
  classical
  -- shrink the cover
  obtain ⟨V, hVcov, hVo, hVcl⟩ := exists_subset_iUnion_closure_subset isClosed_univ hWo
    (fun x _ => Set.toFinite _) (by rw [hcov])
  have hVW : ∀ i, V i ⊆ W i := fun i => subset_closure.trans (hVcl i)
  have hVcov' : ⋃ i, V i = univ := univ_subset_iff.1 hVcov
  have hWWo : ∀ i j, IsOpen (W i ∩ W j) := fun i j => (hWo i).inter (hWo j)
  -- the divisors of the cocycle
  let d : ∀ i j, Function.locallyFinsuppWithin (W i ∩ W j) ℤ := fun i j =>
    divisorOn (F i j) (W i ∩ W j)
  have hd : ∀ i j, ∀ x ∈ W i ∩ W j, orderAt (F i j) x = d i j x := fun i j x hx => by
    simp only [d, divisorOn_apply (hF i j).1 hx]
    exact (WithTop.coe_untop₀_of_ne_top ((hF i j).2 x hx)).symm
  have hdcoc : ∀ i j k, ∀ x ∈ W i ∩ W j ∩ W k, d i k x = d i j x + d j k x := by
    intro i j k x hx
    have hik : x ∈ W i ∩ W k := ⟨hx.1.1, hx.2⟩
    have hij : x ∈ W i ∩ W j := hx.1
    have hjk : x ∈ W j ∩ W k := ⟨hx.1.2, hx.2⟩
    have h := orderAt_congr (eventuallyEq_nhdsNE_of_codiscreteWithin (hcoc i j k)
      ((hWWo i j).inter (hWo k)) hx)
    rw [orderAt_mul ((hF i j).1 x hij) ((hF j k).1 x hjk), hd i k x hik, hd i j x hij,
      hd j k x hjk] at h
    exact_mod_cast h
  -- choose a member of the shrunken cover at each point
  have hτ : ∀ x, ∃ i, x ∈ V i := fun x => mem_iUnion.1 (hVcov (mem_univ x))
  choose τ hτ using hτ
  -- local divisors
  let D : ι → M → ℤ := fun i x => if x ∈ V i then d i (τ x) x else 0
  have hDrel : ∀ i j, ∀ x ∈ V i ∩ V j, D i x = d i j x + D j x := by
    intro i j x hx
    simp only [D, ite_eq_left hx.1, ite_eq_left hx.2]
    exact hdcoc i j (τ x) x ⟨⟨hVW i hx.1, hVW j hx.2⟩, hVW _ (hτ x)⟩
  have hDfin : ∀ i, (D i).support.Finite := by
    intro i
    have hK : ∀ k, closure (V i) ∩ closure (V k) ⊆ W i ∩ W k := fun k =>
      inter_subset_inter (hVcl i) (hVcl k)
    refine (Set.finite_iUnion fun k => ((d i k).restrict (hK k)).finiteSupport
      (isClosed_closure.inter isClosed_closure).isCompact).subset ?_
    intro x hx
    simp only [Function.mem_support, D, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    refine mem_iUnion.2 ⟨τ x, ?_⟩
    change ((d i (τ x)).restrict (hK (τ x))) x ≠ 0
    rw [Function.locallyFinsuppWithin.restrict_apply,
      ite_eq_left ⟨subset_closure hx.1, subset_closure (hτ x)⟩]
    exact hx.2
  -- realise the local divisors by rational functions in the charts
  let φ : ι → M → ℂ := fun i => chartRational (e i) (D i)
  have hφ : ∀ i, IsMeromorphicUnitOn (φ i) (W i) := fun i =>
    isMeromorphicUnitOn_chartRational (he i) (hDfin i) (hWe i)
  have hφord : ∀ i, ∀ x ∈ W i, orderAt (φ i) x = D i x := fun i x hx =>
    orderAt_chartRational (he i) (hDfin i) (hWe i hx)
  -- the corrected cocycle, without zeros and poles on the shrunken intersections
  let G : ι → ι → M → ℂ := fun i j => F i j * φ j * (φ i)⁻¹
  have hVV : ∀ i j, V i ∩ V j ⊆ W i ∩ W j := fun i j => inter_subset_inter (hVW i) (hVW j)
  have hVVo : ∀ i j, IsOpen (V i ∩ V j) := fun i j => (hVo i).inter (hVo j)
  have hGu : ∀ i j, IsMeromorphicUnitOn (G i j) (V i ∩ V j) := fun i j =>
    (((hF i j).mono (hVV i j)).mul ((hφ j).mono (inter_subset_right.trans (hVW j)))).mul
      ((hφ i).mono (inter_subset_left.trans (hVW i))).inv
  have hGord : ∀ i j, ∀ x ∈ V i ∩ V j, orderAt (G i j) x = 0 := by
    intro i j x hx
    have hxW := hVV i j hx
    simp only [G]
    rw [orderAt_mul (((hF i j).1 x hxW).mul ((hφ j).1 x hxW.2)) ((hφ i).1 x hxW.1).inv,
      orderAt_mul ((hF i j).1 x hxW) ((hφ j).1 x hxW.2), orderAt_inv, hd i j x hxW,
      hφord j x hxW.2, hφord i x hxW.1, hDrel i j x hx]
    have h0 : d i j x + D j x + -(d i j x + D j x) = 0 := by ring
    calc _ = (((d i j x + D j x + -(d i j x + D j x)) : ℤ) : WithTop ℤ) := rfl
      _ = 0 := by rw [h0]; rfl
  -- normalise: holomorphic, nowhere vanishing transition functions
  let g : ι → ι → M → ℂ := fun i j => limNhdsNE (G i j)
  have hspec : ∀ i j, ∀ x ∈ V i ∩ V j,
      (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (g i j) y) ∧ g i j x ≠ 0 ∧
        g i j =ᶠ[𝓝[≠] x] G i j := fun i j x hx =>
    ((hGu i j).1 x hx).limNhdsNE_spec (hGord i j x hx)
  have hgmd : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (V i ∩ V j) := fun i j x hx =>
    (hspec i j x hx).1.self_of_nhds.mdifferentiableWithinAt
  have hg0 : ∀ i j, ∀ x ∈ V i ∩ V j, g i j x ≠ 0 := fun i j x hx => (hspec i j x hx).2.1
  have hgcoc : ∀ i j k, ∀ x ∈ V i ∩ V j ∩ V k, g i k x = g i j x * g j k x := by
    intro i j k x hx
    have hik : x ∈ V i ∩ V k := ⟨hx.1.1, hx.2⟩
    have hij : x ∈ V i ∩ V j := hx.1
    have hjk : x ∈ V j ∩ V k := ⟨hx.1.2, hx.2⟩
    refine eq_of_eventuallyEq_nhdsNE (hspec i k x hik).1.self_of_nhds.continuousAt
      ((hspec i j x hij).1.self_of_nhds.continuousAt.mul
        (hspec j k x hjk).1.self_of_nhds.continuousAt) ?_
    have hxW : x ∈ W i ∩ W j ∩ W k := ⟨⟨hVW i hx.1.1, hVW j hx.1.2⟩, hVW k hx.2⟩
    filter_upwards [(hspec i k x hik).2.2, (hspec i j x hij).2.2, (hspec j k x hjk).2.2,
      eventuallyEq_nhdsNE_of_codiscreteWithin (hcoc i j k) ((hWWo i j).inter (hWo k)) hxW,
      (hφ j).eventually_ne_zero hxW.1.2] with y h1 h2 h3 h4 h5
    simp only [Pi.mul_apply] at h4 ⊢
    rw [h1, h2, h3]
    simp only [G, Pi.mul_apply, Pi.inv_apply, h4]
    field_simp
  -- Theorem K
  obtain ⟨σ, hσ, hσrel⟩ := exists_meromorphic_splitting_eq V hVo hVcov' g hgmd hg0 hgcoc
  refine ⟨V, hVo, hVW, hVcov', fun i => σ i * φ i,
    fun i => IsMeromorphicUnitOn.mul (hσ i) ((hφ i).mono (hVW i)),
    fun i j => eventuallyEq_codiscreteWithin_of_nhdsNE fun x hx => ?_⟩
  have hσi : IsMeromorphicUnitOn (σ i) (V i) := hσ i
  have hσj : IsMeromorphicUnitOn (σ j) (V j) := hσ j
  filter_upwards [(hspec i j x hx).2.2, mem_nhdsWithin_of_mem_nhds ((hVVo i j).mem_nhds hx),
    hσj.eventually_ne_zero hx.2, (hφ i).eventually_ne_zero (hVW i hx.1),
    (hφ j).eventually_ne_zero (hVW j hx.2)] with y h1 hy h3 h4 h5
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [hσrel i j y hy, h1]
  simp only [G, Pi.mul_apply, Pi.inv_apply]
  field_simp

end Cech

section Torsors

open Stacks.Cohomology.Torsors

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [CompactSpace M]

/-- **Every `𝓜_M^×`-torsor on a compact Riemann surface is trivial**: trivialise it on a finite
cover by chart domains; the transition functions form a meromorphic cocycle, which splits by
`exists_meromorphic_coboundary`, and the corrected local sections glue. -/
theorem nonempty_globalSections_of_meromorphicUnitsTorsor
    (P : AbelianTorsor (meromorphicUnitsSheaf M)) :
    Nonempty (GlobalSections P.1.presheaf) := by
  classical
  let H := meromorphicUnitsSheaf M
  let Q := P.1.presheaf
  -- local sections
  obtain ⟨S, hS, hSsec⟩ := P.2 ⊤
  have hloc : ∀ x : M, ∃ O : Opens (TopCat.of M), x ∈ O ∧ Nonempty (Q.obj (op O)) := by
    intro x
    obtain ⟨O, f, hf, hxO⟩ := (Opens.mem_grothendieckTopology _).1 hS x trivial
    exact ⟨O, hxO, hSsec hf⟩
  choose O hxO hO using hloc
  let W' : M → Opens (TopCat.of M) := fun x =>
    O x ⊓ ⟨(chartAt ℂ x).source, (chartAt ℂ x).open_source⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W' x : Set M))
    (fun x => (W' x).isOpen) (fun x _ => mem_iUnion.2 ⟨x, hxO x, mem_chart_source ℂ x⟩)
  let W : t → Opens (TopCat.of M) := fun i => W' i
  have hWcov : ⋃ i : t, (W i : Set M) = univ := by
    refine univ_subset_iff.1 fun x _ => ?_
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hx⟩
  let p : ∀ i : t, Q.obj (op (W i)) := fun i => Q.map (homOfLE inf_le_left).op (hO i).some
  -- restrictions of the local sections
  let r : ∀ (i : t) (A : Opens (TopCat.of M)), A ≤ W i → Q.obj (op A) := fun i A h =>
    Q.map (homOfLE h).op (p i)
  have hr : ∀ (i : t) (A B : Opens (TopCat.of M)) (hB : B ≤ W i) (hAB : A ≤ B),
      Q.map (homOfLE hAB).op (r i B hB) = r i A (hAB.trans hB) := by
    intro i A B hB hAB
    change Q.map (homOfLE hAB).op (Q.map (homOfLE hB).op (p i)) = Q.map (homOfLE _).op (p i)
    rw [← Functor.map_comp_apply]
    rfl
  -- transition elements
  let c : ∀ i j : t, H.obj.obj (op (W i ⊓ W j)) := fun i j =>
    torsorDifference H P (op (W i ⊓ W j)) (r j _ inf_le_right) (r i _ inf_le_left)
  have hc : ∀ (i j : t) (A : Opens (TopCat.of M)) (h : A ≤ W i ⊓ W j),
      H.obj.map (homOfLE h).op (c i j) =
        torsorDifference H P (op A) (r j A (h.trans inf_le_right))
          (r i A (h.trans inf_le_left)) := by
    intro i j A h
    rw [torsorDifference_naturality, hr, hr]
  choose F hF hcF using fun i j => exists_eq_meromorphicUnitsMk (Additive.toMul (c i j))
  have hc' : ∀ i j, c i j = Additive.ofMul (meromorphicUnitsMk (hF i j)) := fun i j => by
    rw [← hcF i j]; rfl
  -- the cocycle condition
  have hcoc : ∀ i j k, F i k =ᶠ[codiscreteWithin ((W i : Set M) ∩ W j ∩ W k)] F i j * F j k := by
    intro i j k
    let A := W i ⊓ W j ⊓ W k
    have hik : A ≤ W i ⊓ W k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hij : A ≤ W i ⊓ W j := inf_le_left
    have hjk : A ≤ W j ⊓ W k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have h := torsorDifference_trans H P (op A) (r k A (hik.trans inf_le_right))
      (r j A (hij.trans inf_le_right)) (r i A (hik.trans inf_le_left))
    rw [← hc i k A hik, ← hc j k A hjk, ← hc i j A hij, hc', hc', hc'] at h
    have h2 : meromorphicUnitsMk ((hF i k).mono (SetLike.coe_subset_coe.2 hik)) =
        meromorphicUnitsMk ((hF j k).mono (SetLike.coe_subset_coe.2 hjk)) *
          meromorphicUnitsMk ((hF i j).mono (SetLike.coe_subset_coe.2 hij)) := h
    rw [← meromorphicUnitsMk_mul, meromorphicUnitsMk_eq_iff] at h2
    exact h2.trans (Eventually.of_forall fun y => mul_comm _ _)
  -- split the cocycle
  obtain ⟨V, hVo, hVW, hVcov, h, hh, hFh⟩ := exists_meromorphic_coboundary (fun i => (W i : Set M))
    (fun i => (W i).isOpen) hWcov (fun i => chartAt ℂ (i : M)) (fun i => chart_mem_atlas ℂ _)
    (fun i => fun y hy => hy.2) F hF hcoc
  let V' : t → Opens (TopCat.of M) := fun i => ⟨V i, hVo i⟩
  have hV'W : ∀ i, V' i ≤ W i := fun i => hVW i
  let a : ∀ i : t, H.obj.obj (op (V' i)) := fun i => Additive.ofMul (meromorphicUnitsMk (hh i))
  let q : ∀ i : t, Q.obj (op (V' i)) := fun i =>
    P.1.act (op (V' i)) (Multiplicative.ofAdd (a i)) (r i (V' i) (hV'W i))
  have hq : ∀ (i : t) (A : Opens (TopCat.of M)) (hA : A ≤ V' i),
      Q.map (homOfLE hA).op (q i) = P.1.act (op A)
        (Multiplicative.ofAdd (H.obj.map (homOfLE hA).op (a i))) (r i A (hA.trans (hV'W i))) := by
    intro i A hA
    change P.1.presheaf.map (homOfLE hA).op
      (P.1.act (op (V' i)) (Multiplicative.ofAdd (a i)) (r i (V' i) (hV'W i))) = _
    refine (P.1.naturality (homOfLE hA).op _ _).trans ?_
    exact congrArg₂ (P.1.act (op A)) rfl (hr i A (V' i) (hV'W i) hA)
  have hcompat : ∀ i j, Q.map (homOfLE (inf_le_left : V' i ⊓ V' j ≤ V' i)).op (q i) =
      Q.map (homOfLE (inf_le_right : V' i ⊓ V' j ≤ V' j)).op (q j) := by
    intro i j
    let A := V' i ⊓ V' j
    have hAij : A ≤ W i ⊓ W j := inf_le_inf (hV'W i) (hV'W j)
    rw [hq, hq]
    have hpj : r j A (inf_le_right.trans (hV'W j)) = P.1.act (op A)
        (Multiplicative.ofAdd (H.obj.map (homOfLE hAij).op (c i j)))
        (r i A (inf_le_left.trans (hV'W i))) := by
      rw [hc i j A hAij]
      exact (torsorDifference_act H P (op A) _ _).symm
    rw [hpj, ← act_ofAdd_add]
    congr 2
    rw [hc']
    have e : meromorphicUnitsMk ((hh i).mono (SetLike.coe_subset_coe.2 (inf_le_left : A ≤ V' i))) =
        meromorphicUnitsMk ((hh j).mono (SetLike.coe_subset_coe.2 (inf_le_right : A ≤ V' j))) *
          meromorphicUnitsMk ((hF i j).mono (SetLike.coe_subset_coe.2 hAij)) := by
      rw [← meromorphicUnitsMk_mul, meromorphicUnitsMk_eq_iff]
      have hA' : ((A : Opens (TopCat.of M)) : Set M) = V i ∩ V j := rfl
      rw [hA']
      filter_upwards [hFh i j, ((hh j).mono inter_subset_right).eventually_codiscreteWithin_ne_zero]
        with y hy hy0
      simp only [Pi.mul_apply, Pi.inv_apply] at hy ⊢
      rw [hy]
      field_simp
    exact congrArg Additive.ofMul e
  -- glue
  have hQ : TopCat.Presheaf.IsSheaf (Q : TopCat.Presheaf (Type) (TopCat.of M)) := P.1.isSheaf
  obtain ⟨σ, hσ, -⟩ := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).1 hQ V' q hcompat
  have htop : (⊤ : Opens (TopCat.of M)) ≤ iSup V' := by
    intro x _
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hVcov.symm ▸ mem_univ x : x ∈ ⋃ i, V i)
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  let σ' : Q.obj (op ⊤) := Q.map (homOfLE htop).op σ
  refine (nonempty_globalSections_iff_sectionFamily Q).2
    ⟨fun U => Q.map (homOfLE (le_top : U.unop ≤ ⊤)).op σ', fun {U U'} f => ?_⟩
  rw [← Functor.map_comp_apply]
  rfl

universe w

/-- **`H¹(M, 𝓜_M^×) = 0`** on a compact Riemann surface: every `𝓜_M^×`-torsor is trivial. -/
theorem subsingleton_sheafH_meromorphicUnitsSheaf_one
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0})] :
    Subsingleton (Sheaf.H.{w} (meromorphicUnitsSheaf M) 1) := by
  have hz : ∀ x : torsorIsoClasses (meromorphicUnitsSheaf M),
      torsorIsoClassesEquivH1 (meromorphicUnitsSheaf M) x = 0 := by
    intro x
    induction x using Quotient.inductionOn with
    | h F =>
      rw [← (torsor_class_eq_trivial_iff _ F).2
        (nonempty_globalSections_of_meromorphicUnitsTorsor F)]
      exact torsorIsoClassesEquivH1_trivial _
  refine ⟨fun x y => ?_⟩
  rw [← (torsorIsoClassesEquivH1 (meromorphicUnitsSheaf M)).apply_symm_apply x,
    ← (torsorIsoClassesEquivH1 (meromorphicUnitsSheaf M)).apply_symm_apply y, hz, hz]

end Torsors

section Boundary

universe w

open CategoryTheory.Limits

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0})]

variable (M) in
/-- **The connecting map of the divisor sequence on global sections**,
`Γ(M, Div_M) → H¹(M, 𝒪_M^×)`: a global divisor is read as a class in `H⁰` and composed with the
extension class of the divisor sequence. -/
noncomputable def globalDivisorBoundary :
    (divisorSheaf M).obj.obj (op ⊤) →+
      Sheaf.H.{w} (ComplexManifold.holomorphicUnitsSheaf 𝓘(ℂ) M) 1 :=
  ((shortExact_divisorSequence M).extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (divisorSheaf M) isTerminalTop).symm.toAddMonoidHom

/-- **A global divisor has trivial class in `H¹(M, 𝒪_M^×)` exactly when it is the divisor of a
global section of `𝓜_M^×`.** -/
theorem globalDivisorBoundary_eq_zero_iff (s : (divisorSheaf M).obj.obj (op ⊤)) :
    globalDivisorBoundary M s = 0 ↔
      ∃ a, (meromorphicUnitsToDivisor M).hom.app (op ⊤) a = s := by
  have hS := shortExact_divisorSequence M
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS
      ((Sheaf.H.equiv₀ (divisorSheaf M) isTerminalTop).symm s) (zero_add 1) h
    refine ⟨Sheaf.H.equiv₀ _ isTerminalTop y, ?_⟩
    rw [Sheaf.H.equiv₀_naturality]
    exact (congrArg (Sheaf.H.equiv₀ _ isTerminalTop) hy).trans (AddEquiv.apply_symm_apply _ _)
  · rintro ⟨a, rfl⟩
    change ((Sheaf.H.equiv₀ _ _).symm _).comp hS.extClass (zero_add 1) = 0
    rw [← Sheaf.H.equiv₀_symm_naturality]
    exact (Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans
      (by rw [hS.comp_extClass, Abelian.Ext.comp_zero])

variable [CompactSpace M]

/-- **Every class of `H¹(M, 𝒪_M^×)` is the class of a global divisor**, on a compact Riemann
surface: the connecting map of the divisor sequence is onto since `H¹(M, 𝓜_M^×) = 0`. -/
theorem surjective_globalDivisorBoundary : Function.Surjective (globalDivisorBoundary.{w} M) := by
  intro c
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₁ _ (shortExact_divisorSequence M)
    (c : Abelian.Ext _ (divisorSequence M).X₁ 1)
    ((subsingleton_sheafH_meromorphicUnitsSheaf_one.{w} (M := M)).elim _ _) (zero_add 1)
  refine ⟨Sheaf.H.equiv₀ (divisorSheaf M) isTerminalTop x, ?_⟩
  change ((Sheaf.H.equiv₀ _ _).symm (Sheaf.H.equiv₀ _ _ x)).comp _ (zero_add 1) = c
  rwa [AddEquiv.symm_apply_apply]

variable (M) in
/-- On a compact space, the global divisors are the finitely supported functions `M →₀ ℤ`. -/
noncomputable def globalDivisorEquiv : (M →₀ ℤ) ≃+ (divisorSheaf M).obj.obj (op ⊤) where
  toFun D := (⟨D, fun _ _ => trivial, fun _ _ => ⟨univ, univ_mem,
    (D.hasFiniteSupport.subset inter_subset_right)⟩⟩ :
      Function.locallyFinsuppWithin ((⊤ : Opens (TopCat.of M)) : Set M) ℤ)
  invFun E := Finsupp.ofSupportFinite (divisorSection E)
    ((divisorSection E).finiteSupport (by simpa using isCompact_univ))
  left_inv D := by
    ext x
    rfl
  right_inv E := by
    apply divisorSection_injective
    ext x
    rfl
  map_add' D D' := by
    apply divisorSection_injective
    ext x
    rfl

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0})] in
theorem globalDivisorEquiv_apply (D : M →₀ ℤ) (x : M) :
    divisorSection (globalDivisorEquiv M D) x = D x := rfl

variable (M) in
/-- **The analytic divisor boundary** `(M →₀ ℤ) → H¹(M, 𝒪_M^×)` of a compact Riemann surface:
the connecting map of the divisor sequence, on global divisors. -/
noncomputable def analyticDivisorBoundary :
    (M →₀ ℤ) →+ Sheaf.H.{w} (ComplexManifold.holomorphicUnitsSheaf 𝓘(ℂ) M) 1 :=
  (globalDivisorBoundary.{w} M).comp (globalDivisorEquiv M).toAddMonoidHom

/-- **Every holomorphic line bundle on a compact Riemann surface comes from a divisor**: the
analytic divisor boundary is surjective. -/
theorem surjective_analyticDivisorBoundary :
    Function.Surjective (analyticDivisorBoundary.{w} M) := by
  intro c
  obtain ⟨s, hs⟩ := surjective_globalDivisorBoundary.{w} c
  exact ⟨(globalDivisorEquiv M).symm s, by
    simp [analyticDivisorBoundary, hs]⟩

/-- **The kernel of the analytic divisor boundary consists of the principal divisors**: a
divisor `D` has trivial class in `H¹(M, 𝒪_M^×)` iff it is the divisor of a global meromorphic
function vanishing identically near no point. -/
theorem analyticDivisorBoundary_eq_zero_iff (D : M →₀ ℤ) :
    analyticDivisorBoundary.{w} M D = 0 ↔ ∃ f : M → ℂ, MeromorphicOn f univ ∧
      (∀ x, orderAt f x ≠ ⊤) ∧ ∀ x, orderAt f x = D x := by
  change globalDivisorBoundary M (globalDivisorEquiv M D) = 0 ↔ _
  rw [globalDivisorBoundary_eq_zero_iff]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨f, hf, haf⟩ := exists_eq_meromorphicUnitsMk (Additive.toMul a)
    have ha' : a = Additive.ofMul (meromorphicUnitsMk hf) := by rw [← haf]; rfl
    subst ha'
    have hf' : IsMeromorphicUnitOn f univ := hf
    refine ⟨f, hf'.1, fun x => hf'.2 x (mem_univ x), fun x => ?_⟩
    have h := congrArg (fun E => divisorSection E x) ha
    change divisorSection (meromorphicUnitsToDivisors ⊤
      (Additive.ofMul (meromorphicUnitsMk hf))) x =
      D x at h
    rw [meromorphicUnitsToDivisors_ofMul_mk, divisorOn_apply hf.1 (mem_univ x)] at h
    rw [← WithTop.coe_untop₀_of_ne_top (hf'.2 x (mem_univ x)), h]
  · rintro ⟨f, hf, hf0, hfD⟩
    have hf' : IsMeromorphicUnitOn f ((⊤ : Opens (TopCat.of M)) : Set M) :=
      ⟨by simpa using hf, fun x _ => hf0 x⟩
    refine ⟨Additive.ofMul (meromorphicUnitsMk hf'), ?_⟩
    apply divisorSection_injective
    ext x
    change divisorSection (meromorphicUnitsToDivisors ⊤
      (Additive.ofMul (meromorphicUnitsMk hf'))) x =
      D x
    rw [meromorphicUnitsToDivisors_ofMul_mk, divisorOn_apply hf'.1 (mem_univ x), hfD x]
    rfl

end Boundary

end RiemannSurface

end
