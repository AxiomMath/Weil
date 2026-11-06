/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Local
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
public import Weil.AlgebraicGeometry.ComplexPoints.RiemannSurface
public import Weil.AlgebraicGeometry.ComplexPoints.Compact
public import Weil.Geometry.Manifold.Complex.Meromorphic
public import Weil.Geometry.Manifold.Complex.BranchedCover
public import Weil.RingTheory.DedekindDomain.CardPrimesOverLe

/-!
# Rational functions on a smooth curve over `ℂ` as meromorphic functions

Let `C` be a smooth curve over `ℂ`, with structure morphism `y`, function field `K` and complex
points `C(ℂ)`, a Riemann surface for the analytic topology. By the Nullstellensatz the complex
points are the closed points of `C`. A rational function `g ∈ K` is *regular* at `p ∈ C(ℂ)` if it is
the image of a regular function on an open neighbourhood of `p`, and then it has a value
`g(p) ∈ ℂ`. The analytification of `g` is the function on `C(ℂ)` equal to `g(p)` where `g` is
regular and to `0` at the poles of `g`.

The local ring of `C` at `p` is a discrete valuation ring, and a uniformizer is a local coordinate
of the Riemann surface at `p`: in the chart at `p`, given by an étale coordinate `t`, the function
`t - t(p)` is a uniformizer up to a unit, and the analytic order of a regular function is the
algebraic order of vanishing times the analytic order of a uniformizer. Hence the analytification
of `g` is meromorphic, in normal form, and its order at `p` is the order of vanishing
`ord_p(g)`. The analytification is compatible with the field operations away from a discrete set.

For a rational function `t` and `b ∈ ℂ`, the points at which `t` is holomorphic with value `b`
number at most `[K : ℂ(t)]`: each gives a prime of the integral closure of `ℂ[t]` in `K` over
`(t - b)`, distinct points giving distinct primes because the localizations of a Dedekind domain
are valuation rings and the points of a separated scheme are determined by their local rings.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.closedPointsEquiv`: the closed points of a scheme locally
  of finite type over `ℂ` are its complex points.
* `AlgebraicGeometry.Scheme.ComplexPoints.IsRegularAt`: a rational function is regular at a complex
  point.
* `AlgebraicGeometry.Scheme.ComplexPoints.analytifyRat`: the analytification `C(ℂ) → ℂ` of a
  rational function.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.meromorphicNFAt_analytifyRat`: the analytification of a
  rational function is meromorphic in normal form at every point.
* `AlgebraicGeometry.Scheme.ComplexPoints.orderAt_analytifyRat`: its order at `p` is the order of
  vanishing of the rational function at the closed point `p`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analytifyRat_mul_eventuallyEq`,
  `analytifyRat_add_eventuallyEq`, `analytifyRat_sub_eventuallyEq`, `analytifyRat_inv_eventuallyEq`,
  `analytifyRat_one`, `analytifyRat_algebraMap`: compatibility with the field operations and the
  constants.
* `AlgebraicGeometry.Scheme.ComplexPoints.orderAt_analytifyRat_sub_const_ne_top`: a nonconstant
  rational function minus a constant has finite order everywhere.
* `AlgebraicGeometry.Scheme.ComplexPoints.finiteDimensional_ratFunc`: the function field is a
  finite extension of every subfield `ℂ(t)`; `exists_algebra_ratFunc` gives the subfield `ℂ(t)`
  of a transcendental `t`.
* `AlgebraicGeometry.Scheme.ComplexPoints.ncard_regularFibre_le_finrank`: a regular fibre of `t`
  has at most `[K : ℂ(t)]` points.
* `AlgebraicGeometry.Scheme.ComplexPoints.eq_of_forall_isRegularAt_iff`: complex points of a
  separated scheme are determined by the rational functions regular at them.

## Implementation notes

The hypotheses are those of a smooth curve in both forms used in this library: `IsCurve ℂ y` (an
integral separated scheme of finite type and dimension one over `ℂ`, the setting of the divisor
sequence of a curve) and `SmoothOfRelativeDimension 1 y` (for the charts of the Riemann surface).
`IsLocallyNoetherian C`, which follows from `IsCurve ℂ y`, is a separate hypothesis because the
order of vanishing `AlgebraicGeometry.Scheme.ord` is stated under it. Properness is not used.
The `ℂ`-algebra structure on the function field is `AlgebraicGeometry.functionFieldAlgebra`,
induced by `y`; the embedding `ℂ(X) → K` of `ncard_regularFibre_le_finrank` is any embedding over
`ℂ` sending `X` to `t`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
* [For] O. Forster, *Lectures on Riemann Surfaces*, §§1–8.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Filter Manifold
open scoped TensorProduct

/-- **The local ring of a Dedekind domain at a nonzero prime `𝔮` is a valuation ring.** Every
element `g` of the fraction field is a quotient `s / u` with `u ∉ 𝔮`, or else `g⁻¹ u = s` with
`s ∈ 𝔮` and `u ∉ 𝔮`. -/
theorem IsDedekindDomain.exists_eq_mul_inv_or_exists_inv_mul_eq {S K : Type*} [CommRing S]
    [IsDedekindDomain S] [Field K] [Algebra S K] [IsFractionRing S K] {𝔮 : Ideal S} [𝔮.IsPrime]
    (h0 : 𝔮 ≠ ⊥) (g : K) :
    (∃ s u : S, u ∉ 𝔮 ∧ g = algebraMap S K s * (algebraMap S K u)⁻¹) ∨
      (∃ s u : S, s ∈ 𝔮 ∧ u ∉ 𝔮 ∧ g⁻¹ * algebraMap S K u = algebraMap S K s) := by
  have hM : 𝔮.primeCompl ≤ nonZeroDivisors S := fun u hu =>
    mem_nonZeroDivisors_of_ne_zero fun h => hu (h ▸ 𝔮.zero_mem)
  let A := Localization.subalgebra.ofField K 𝔮.primeCompl hM
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S h0 A
  have hA : ∀ a : A, ∃ s u : S, u ∉ 𝔮 ∧ (a : K) = algebraMap S K s * (algebraMap S K u)⁻¹ :=
    fun a => by
      obtain ⟨s, u, hu, hsu⟩ := a.2
      exact ⟨s, u, hu, hsu⟩
  rcases ValuationRing.isInteger_or_isInteger A g with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha' : (a : K) = g := ha
    exact Or.inl (ha' ▸ hA a)
  · have ha' : (a : K) = g⁻¹ := ha
    by_cases hunit : IsUnit a
    · obtain ⟨v, hv⟩ : ∃ v : A, v * a = 1 := ⟨↑hunit.unit⁻¹, hunit.unit.inv_mul⟩
      have hvK : (v : K) = g := by
        have := congrArg (fun z : A => (z : K)) hv
        simp only [Subalgebra.coe_mul, Subalgebra.coe_one, ha'] at this
        exact (eq_inv_of_mul_eq_one_left this).trans (inv_inv g)
      exact Or.inl (hvK ▸ hA v)
    · have hmax : a ∈ IsLocalRing.maximalIdeal A := hunit
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 A] at hmax
      obtain ⟨⟨s, u⟩, hsu⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔮.primeCompl A).1 hmax
      refine Or.inr ⟨s, u, s.2, u.2, ?_⟩
      have := congrArg (fun z : A => (z : K)) hsu
      simp only [Subalgebra.coe_mul, ha'] at this
      exact this

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {C : Scheme.{0}} {y : C ⟶ Spec (.of ℂ)}

/-! ### Complex points and closed points -/

/-- The point of `C` underlying a complex point `p : Spec ℂ ⟶ C`. -/
noncomputable def toPoint (p : ComplexPoints y) : C := p.hom (IsLocalRing.closedPoint ℂ)

theorem mem_iff_toPoint_mem {p : ComplexPoints y} {U : C.Opens} : p.Mem U ↔ p.toPoint ∈ U :=
  mem_iff _

section ClosedPoints

variable [LocallyOfFiniteType y]

/-- **Hilbert's Nullstellensatz for schemes over `ℂ`.** The closed points of a scheme locally of
finite type over `ℂ` are its complex points. -/
noncomputable def closedPointsEquiv : closedPoints C ≃ ComplexPoints y :=
  (pointEquivClosedPoint y).symm

@[simp]
theorem coe_closedPointsEquiv_symm (p : ComplexPoints y) :
    ((closedPointsEquiv (y := y)).symm p : C) = p.toPoint := rfl

theorem toPoint_closedPointsEquiv (x : closedPoints C) :
    (closedPointsEquiv (y := y) x).toPoint = x := by
  rw [← coe_closedPointsEquiv_symm, Equiv.symm_apply_apply]

/-- The point underlying a complex point is closed. -/
theorem isClosed_singleton_toPoint (p : ComplexPoints y) : IsClosed {p.toPoint} :=
  ((closedPointsEquiv (y := y)).symm p).2

/-- Complex points are determined by their underlying points. -/
theorem toPoint_injective : Function.Injective (toPoint (y := y)) := fun _ _ h =>
  (closedPointsEquiv (y := y)).symm.injective (Subtype.ext h)

end ClosedPoints

/-! ### Values of rational functions -/

section Values

variable [IsIntegral C]

/-- The image in the function field of a regular function `s` on an open `V ∋ p`, computed
through the stalk at `p`. It is `C.germToFunctionField V s` (`ratGerm_eq_germToFunctionField`). -/
noncomputable def ratGerm {V : C.Opens} (s : Γ(C, V)) (p : ComplexPoints y) (hp : p.Mem V) :
    C.functionField :=
  algebraMap (C.presheaf.stalk p.toPoint) C.functionField
    (C.presheaf.germ V p.toPoint (mem_iff_toPoint_mem.1 hp) s)

theorem ratGerm_eq_germToFunctionField {V : C.Opens} [Nonempty V] (s : Γ(C, V))
    (p : ComplexPoints y) (hp : p.Mem V) : ratGerm s p hp = C.germToFunctionField V s :=
  Scheme.algebraMap_germ_eq_germToFunctionField C (mem_iff_toPoint_mem.1 hp) s

theorem ratGerm_res {V W : C.Opens} (h : W ≤ V) (s : Γ(C, V)) (p : ComplexPoints y)
    (hp : p.Mem W) : ratGerm (C.presheaf.map (homOfLE h).op s) p hp = ratGerm s p (hp.mono h) := by
  simp only [ratGerm]
  rw [TopCat.Presheaf.germ_res_apply]

theorem ratGerm_mul {V : C.Opens} (s t : Γ(C, V)) (p : ComplexPoints y) (hp : p.Mem V) :
    ratGerm (s * t) p hp = ratGerm s p hp * ratGerm t p hp := by
  simp only [ratGerm, map_mul]

theorem ratGerm_add {V : C.Opens} (s t : Γ(C, V)) (p : ComplexPoints y) (hp : p.Mem V) :
    ratGerm (s + t) p hp = ratGerm s p hp + ratGerm t p hp := by
  simp only [ratGerm, map_add]

theorem ratGerm_sub {V : C.Opens} (s t : Γ(C, V)) (p : ComplexPoints y) (hp : p.Mem V) :
    ratGerm (s - t) p hp = ratGerm s p hp - ratGerm t p hp := by
  simp only [ratGerm, map_sub]

theorem ratGerm_one {V : C.Opens} (p : ComplexPoints y) (hp : p.Mem V) :
    ratGerm (1 : Γ(C, V)) p hp = 1 := by
  simp only [ratGerm, map_one]

theorem ratGerm_zero {V : C.Opens} (p : ComplexPoints y) (hp : p.Mem V) :
    ratGerm (0 : Γ(C, V)) p hp = 0 := by
  simp only [ratGerm, map_zero]

/-- Two regular functions near `p` with the same image in the function field agree on a
neighbourhood of `p`. -/
theorem exists_res_eq_of_ratGerm_eq {V V' : C.Opens} {s : Γ(C, V)} {s' : Γ(C, V')}
    {p : ComplexPoints y} {hp : p.Mem V} {hp' : p.Mem V'} (h : ratGerm s p hp = ratGerm s' p hp') :
    ∃ (W : C.Opens) (_ : p.Mem W) (hWV : W ≤ V) (hWV' : W ≤ V'),
      C.presheaf.map (homOfLE hWV).op s = C.presheaf.map (homOfLE hWV').op s' := by
  have hg := IsFractionRing.injective (C.presheaf.stalk p.toPoint) C.functionField h
  obtain ⟨W, hW, iU, iV, e⟩ := C.presheaf.germ_eq _ _ _ s s' hg
  exact ⟨W, mem_iff_toPoint_mem.2 hW, leOfHom iU, leOfHom iV, e⟩

/-- Two regular functions near `p` with the same image in the function field have the same value
at `p`. -/
theorem eval_eq_of_ratGerm_eq {V V' : C.Opens} {s : Γ(C, V)} {s' : Γ(C, V')}
    {p : ComplexPoints y} {hp : p.Mem V} {hp' : p.Mem V'} (h : ratGerm s p hp = ratGerm s' p hp') :
    eval s p hp = eval s' p hp' := by
  obtain ⟨W, hpW, hWV, hWV', e⟩ := exists_res_eq_of_ratGerm_eq h
  rw [← eval_map hWV s p hpW, ← eval_map hWV' s' p hpW, e]

/-- A rational function `g` is *regular* at a complex point `p` if it is the image of a regular
function on an open neighbourhood of `p`. -/
def IsRegularAt (g : C.functionField) (p : ComplexPoints y) : Prop :=
  ∃ (V : C.Opens) (hp : p.Mem V) (s : Γ(C, V)), ratGerm s p hp = g

/-- **The analytification of a rational function** `g` on `C`: the function on `C(ℂ)` whose value
at `p` is `g(p)` where `g` is regular, and `0` at the poles of `g`. For `C` a smooth curve this
is a meromorphic function in normal form (`meromorphicNFAt_analytifyRat`). -/
noncomputable def analytifyRat (g : C.functionField) : ComplexPoints y → ℂ := fun p =>
  open Classical in
  if h : IsRegularAt g p then eval h.choose_spec.choose_spec.choose p h.choose_spec.choose else 0

theorem analytifyRat_eq_eval {g : C.functionField} {V : C.Opens} (s : Γ(C, V))
    {p : ComplexPoints y} (hp : p.Mem V) (h : ratGerm s p hp = g) :
    analytifyRat g p = eval s p hp := by
  have hr : IsRegularAt g p := ⟨V, hp, s, h⟩
  simp only [analytifyRat, hr, ↓reduceDIte]
  exact eval_eq_of_ratGerm_eq (hr.choose_spec.choose_spec.choose_spec.trans h.symm)

theorem analytifyRat_of_not_isRegularAt {g : C.functionField} {p : ComplexPoints y}
    (h : ¬IsRegularAt g p) : analytifyRat g p = 0 := by
  simp only [analytifyRat, h, ↓reduceDIte]

/-- On `V(ℂ)`, the analytification of the image of `s ∈ Γ(C, V)` is `q ↦ s(q)`. -/
theorem analytifyRat_germToFunctionField {V : C.Opens} [Nonempty V] (s : Γ(C, V))
    {p : ComplexPoints y} (hp : p.Mem V) :
    analytifyRat (C.germToFunctionField V s) p = eval s p hp :=
  analytifyRat_eq_eval s hp (ratGerm_eq_germToFunctionField s p hp)

theorem eqOn_analytifyRat_germToFunctionField {V : C.Opens} [Nonempty V] (s : Γ(C, V)) :
    Set.EqOn (analytifyRat (y := y) (C.germToFunctionField V s)) (evalOrZero V s)
      {q | q.Mem V} := fun _ hq => by
  rw [analytifyRat_germToFunctionField s hq, evalOrZero_of_mem _ hq]

theorem isRegularAt_ratGerm {V : C.Opens} (s : Γ(C, V)) {p q : ComplexPoints y} (hp : p.Mem V)
    (hq : q.Mem V) : IsRegularAt (ratGerm s p hp) q := by
  have : Nonempty V := ⟨⟨p.toPoint, mem_iff_toPoint_mem.1 hp⟩⟩
  exact ⟨V, hq, s, by rw [ratGerm_eq_germToFunctionField, ratGerm_eq_germToFunctionField]⟩

theorem analytifyRat_ratGerm {V : C.Opens} (s : Γ(C, V)) {p q : ComplexPoints y} (hp : p.Mem V)
    (hq : q.Mem V) : analytifyRat (ratGerm s p hp) q = eval s q hq := by
  have : Nonempty V := ⟨⟨p.toPoint, mem_iff_toPoint_mem.1 hp⟩⟩
  rw [ratGerm_eq_germToFunctionField]
  exact analytifyRat_germToFunctionField s hq

/-- Regular functions near `p` restrict to a common neighbourhood. -/
theorem IsRegularAt.exists_of_two {g h : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (hh : IsRegularAt h p) :
    ∃ (V : C.Opens) (hp : p.Mem V) (s t : Γ(C, V)), ratGerm s p hp = g ∧ ratGerm t p hp = h := by
  obtain ⟨V, hpV, s, rfl⟩ := hg
  obtain ⟨V', hpV', s', rfl⟩ := hh
  have hp : p.Mem (V ⊓ V') := mem_iff_toPoint_mem.2
    ⟨mem_iff_toPoint_mem.1 hpV, mem_iff_toPoint_mem.1 hpV'⟩
  exact ⟨V ⊓ V', hp, C.presheaf.map (homOfLE inf_le_left).op s,
    C.presheaf.map (homOfLE inf_le_right).op s', ratGerm_res _ _ _ _, ratGerm_res _ _ _ _⟩

theorem IsRegularAt.mul {g h : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p)
    (hh : IsRegularAt h p) : IsRegularAt (g * h) p := by
  obtain ⟨V, hp, s, t, rfl, rfl⟩ := hg.exists_of_two hh
  exact ⟨V, hp, s * t, ratGerm_mul _ _ _ _⟩

theorem IsRegularAt.add {g h : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p)
    (hh : IsRegularAt h p) : IsRegularAt (g + h) p := by
  obtain ⟨V, hp, s, t, rfl, rfl⟩ := hg.exists_of_two hh
  exact ⟨V, hp, s + t, ratGerm_add _ _ _ _⟩

theorem IsRegularAt.sub {g h : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p)
    (hh : IsRegularAt h p) : IsRegularAt (g - h) p := by
  obtain ⟨V, hp, s, t, rfl, rfl⟩ := hg.exists_of_two hh
  exact ⟨V, hp, s - t, ratGerm_sub _ _ _ _⟩

theorem analytifyRat_mul_of_isRegularAt {g h : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (hh : IsRegularAt h p) :
    analytifyRat (g * h) p = analytifyRat g p * analytifyRat h p := by
  obtain ⟨V, hp, s, t, rfl, rfl⟩ := hg.exists_of_two hh
  rw [analytifyRat_eq_eval s hp rfl, analytifyRat_eq_eval t hp rfl,
    analytifyRat_eq_eval (s * t) hp (ratGerm_mul _ _ _ _), ← evalHom_apply, map_mul]
  rfl

theorem analytifyRat_add_of_isRegularAt {g h : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (hh : IsRegularAt h p) :
    analytifyRat (g + h) p = analytifyRat g p + analytifyRat h p := by
  obtain ⟨V, hp, s, t, rfl, rfl⟩ := hg.exists_of_two hh
  rw [analytifyRat_eq_eval s hp rfl, analytifyRat_eq_eval t hp rfl,
    analytifyRat_eq_eval (s + t) hp (ratGerm_add _ _ _ _), ← evalHom_apply, map_add]
  rfl

theorem analytifyRat_sub_of_isRegularAt {g h : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (hh : IsRegularAt h p) :
    analytifyRat (g - h) p = analytifyRat g p - analytifyRat h p := by
  obtain ⟨V, hp, s, t, rfl, rfl⟩ := hg.exists_of_two hh
  rw [analytifyRat_eq_eval s hp rfl, analytifyRat_eq_eval t hp rfl,
    analytifyRat_eq_eval (s - t) hp (ratGerm_sub _ _ _ _), ← evalHom_apply, map_sub]
  rfl

theorem isRegularAt_one (p : ComplexPoints y) : IsRegularAt (1 : C.functionField) p :=
  ⟨⊤, mem_top p, 1, ratGerm_one _ _⟩

theorem isRegularAt_zero (p : ComplexPoints y) : IsRegularAt (0 : C.functionField) p :=
  ⟨⊤, mem_top p, 0, ratGerm_zero _ _⟩

@[simp]
theorem analytifyRat_one : analytifyRat (y := y) (1 : C.functionField) = 1 := by
  funext p
  rw [analytifyRat_eq_eval (1 : Γ(C, ⊤)) (mem_top p) (ratGerm_one _ _), ← evalHom_apply, map_one]
  rfl

@[simp]
theorem analytifyRat_zero : analytifyRat (y := y) (0 : C.functionField) = 0 := by
  funext p
  rw [analytifyRat_eq_eval (0 : Γ(C, ⊤)) (mem_top p) (ratGerm_zero _ _), ← evalHom_apply,
    map_zero]
  rfl


omit [IsIntegral C] in
theorem eval_eq_zero_iff_germ_mem_maximalIdeal {V : C.Opens} (s : Γ(C, V)) {p : ComplexPoints y}
    (hp : p.Mem V) :
    eval s p hp = 0 ↔ C.presheaf.germ V p.toPoint (mem_iff_toPoint_mem.1 hp) s ∈
      IsLocalRing.maximalIdeal (C.presheaf.stalk p.toPoint) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen,
    ← mem_iff_toPoint_mem, mem_basicOpen_iff hp, not_not]

/-- A rational function is regular at `p` iff it comes from the local ring at `p`. -/
theorem isRegularAt_iff_exists_algebraMap {g : C.functionField} {p : ComplexPoints y} :
    IsRegularAt g p ↔ ∃ a : C.presheaf.stalk p.toPoint,
      algebraMap (C.presheaf.stalk p.toPoint) C.functionField a = g := by
  constructor
  · rintro ⟨V, hp, s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨V, hV, s, rfl⟩ := C.presheaf.exists_germ_eq a
    exact ⟨V, mem_iff_toPoint_mem.2 hV, s, rfl⟩

theorem isRegularAt_algebraMap {p : ComplexPoints y} (a : C.presheaf.stalk p.toPoint) :
    IsRegularAt (algebraMap (C.presheaf.stalk p.toPoint) C.functionField a) p :=
  isRegularAt_iff_exists_algebraMap.2 ⟨a, rfl⟩

/-- An element of the local ring at `p` vanishes at `p` iff it lies in the maximal ideal. -/
theorem analytifyRat_algebraMap_eq_zero_iff {p : ComplexPoints y}
    (a : C.presheaf.stalk p.toPoint) :
    analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField a) p = 0 ↔
      a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk p.toPoint) := by
  obtain ⟨V, hV, s, rfl⟩ := C.presheaf.exists_germ_eq a
  rw [analytifyRat_eq_eval (g := algebraMap _ _ (C.presheaf.germ V p.toPoint hV s)) s
    (mem_iff_toPoint_mem.2 hV) rfl, eval_eq_zero_iff_germ_mem_maximalIdeal]

/-- A rational function regular at `p` is regular near `p`. -/
theorem IsRegularAt.eventually {g : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p) :
    ∀ᶠ q in 𝓝 p, IsRegularAt g q := by
  obtain ⟨V, hp, s, rfl⟩ := hg
  filter_upwards [(isOpen_setOf_mem V).mem_nhds hp] with q hq
  exact isRegularAt_ratGerm s hp hq

theorem analytifyRat_ratGerm_eventuallyEq {V : C.Opens} (s : Γ(C, V)) {p : ComplexPoints y}
    (hp : p.Mem V) : analytifyRat (ratGerm s p hp) =ᶠ[𝓝 p] evalOrZero V s := by
  filter_upwards [(isOpen_setOf_mem V).mem_nhds hp] with q hq
  rw [analytifyRat_ratGerm s hp hq, evalOrZero_of_mem _ hq]

theorem IsRegularAt.pow {g : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p)
    (n : ℕ) : IsRegularAt (g ^ n) p := by
  induction n with
  | zero => simpa using isRegularAt_one p
  | succ n ih => simpa [pow_succ] using ih.mul hg

theorem analytifyRat_pow_of_isRegularAt {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (n : ℕ) : analytifyRat (g ^ n) p = analytifyRat g p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, analytifyRat_mul_of_isRegularAt (hg.pow n) hg, ih, pow_succ]

/-- A rational function regular at `p` with nonzero value there is invertible near `p`. -/
theorem IsRegularAt.inv {g : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p)
    (h : analytifyRat g p ≠ 0) :
    IsRegularAt g⁻¹ p ∧ analytifyRat g⁻¹ p = (analytifyRat g p)⁻¹ := by
  obtain ⟨V, hp, s, rfl⟩ := hg
  rw [analytifyRat_eq_eval s hp rfl] at h ⊢
  have hpD : p.Mem (C.basicOpen s) := (mem_basicOpen_iff hp).2 h
  have hu := C.toRingedSpace.isUnit_res_basicOpen s
  set s' : Γ(C, C.basicOpen s) := C.presheaf.map (homOfLE (C.basicOpen_le s)).op s with hs'
  have hs'eq : ratGerm s' p hpD = ratGerm s p hp := ratGerm_res _ _ _ _
  obtain ⟨w, hmul⟩ : ∃ w : Γ(C, C.basicOpen s), s' * w = 1 := ⟨hu.unit⁻¹.val, hu.mul_val_inv⟩
  have hrat : ratGerm s' p hpD * ratGerm w p hpD = 1 := by
    rw [← ratGerm_mul, hmul, ratGerm_one]
  have hev : eval s' p hpD * eval w p hpD = 1 := by
    rw [← evalHom_apply, ← evalHom_apply, ← map_mul, hmul, map_one]
  have hs'v : eval s' p hpD = eval s p hp := eval_map _ _ _ _
  refine ⟨⟨_, hpD, w, ?_⟩, ?_⟩
  · rw [← hs'eq]
    exact (eq_inv_of_mul_eq_one_right hrat)
  · rw [analytifyRat_eq_eval w hpD (by rw [← hs'eq]; exact eq_inv_of_mul_eq_one_right hrat),
      ← hs'v]
    exact eq_inv_of_mul_eq_one_right hev


theorem germToFunctionField_map {U V : C.Opens} (h : V ≤ U) [Nonempty V] [Nonempty U]
    (s : Γ(C, U)) :
    C.germToFunctionField V (C.presheaf.map (homOfLE h).op s) = C.germToFunctionField U s :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **Complex points of a separated scheme are determined by their local rings.** If the same
rational functions are regular at `p` and at `q`, with the same values, then `p = q`. -/
theorem eq_of_forall_isRegularAt_iff [IsSeparated y] {p q : ComplexPoints y}
    (h₁ : ∀ g : C.functionField, IsRegularAt g p ↔ IsRegularAt g q)
    (h₂ : ∀ g : C.functionField, IsRegularAt g p → analytifyRat g q = analytifyRat g p) :
    p = q := by
  obtain ⟨U, hU, hpU, -⟩ := (Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens)
    (show p.toPoint ∈ (⊤ : C.Opens) from trivial)
  obtain ⟨W, hW, hqW, -⟩ := (Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens)
    (show q.toPoint ∈ (⊤ : C.Opens) from trivial)
  have hpU' : p.Mem U := mem_iff_toPoint_mem.2 hpU
  have hqW' : q.Mem W := mem_iff_toPoint_mem.2 hqW
  have : Nonempty U := ⟨⟨_, hpU⟩⟩
  have : Nonempty W := ⟨⟨_, hqW⟩⟩
  have key : ∀ {V : C.Opens} [Nonempty V] (s : Γ(C, V)) (hp : p.Mem V) (hq : q.Mem V),
      eval s p hp = eval s q hq := by
    intro V _ s hp hq
    rw [← analytifyRat_germToFunctionField s hp, ← analytifyRat_germToFunctionField s hq]
    exact (h₂ _ ⟨V, hp, s, ratGerm_eq_germToFunctionField s p hp⟩).symm
  suffices hpW : p.Mem W from eq_of_eval_eq hW hpW hqW' fun s => key s hpW hqW'
  by_contra hpW
  have hUW : IsAffineOpen (U ⊓ W) := isAffineOpen_inf_of_isSeparated y hU hW
  have hsurj := sectionTensorMap_surjective_of_isSeparated y U W hU hW ⊤
    (isAffineOpen_top _) (by simp) (by simp)
  have : Nonempty (U ⊓ W : C.Opens) := by
    obtain ⟨r, hr⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨_, hpU⟩ ⟨_, hqW⟩
    exact ⟨⟨r, hr⟩⟩
  have hΦ : ∀ k : Γ(C, U) ⊗[ℤ] Γ(C, W),
      IsRegularAt (C.germToFunctionField (U ⊓ W) (sectionTensorMap C U W k)) p ∧
        evalTensor p q hpU' hqW' k =
          analytifyRat (C.germToFunctionField (U ⊓ W) (sectionTensorMap C U W k)) p := by
    intro k
    induction k using TensorProduct.induction_on with
    | zero =>
      exact ⟨by simpa using isRegularAt_zero (y := y) p, by simp⟩
    | add k₁ k₂ h₁' h₂' =>
      rw [map_add, map_add, map_add, analytifyRat_add_of_isRegularAt h₁'.1 h₂'.1, h₁'.2, h₂'.2]
      exact ⟨h₁'.1.add h₂'.1, rfl⟩
    | tmul a b =>
      have hab : C.germToFunctionField (U ⊓ W) (sectionTensorMap C U W (a ⊗ₜ b)) =
          C.germToFunctionField U a * C.germToFunctionField W b := by
        rw [Algebra.TensorProduct.lift_tmul, map_mul]
        exact congrArg₂ (· * ·) (germToFunctionField_map _ a) (germToFunctionField_map _ b)
      have hra : IsRegularAt (C.germToFunctionField U a) p :=
        ⟨U, hpU', a, ratGerm_eq_germToFunctionField a p hpU'⟩
      have hrb : IsRegularAt (C.germToFunctionField W b) p :=
        (h₁ _).2 ⟨W, hqW', b, ratGerm_eq_germToFunctionField b q hqW'⟩
      rw [hab, analytifyRat_mul_of_isRegularAt hra hrb, evalTensor_tmul,
        ← analytifyRat_germToFunctionField a hpU', ← analytifyRat_germToFunctionField b hqW',
        h₂ _ hrb]
      exact ⟨hra.mul hrb, rfl⟩
  have hker : ∀ k ∈ RingHom.ker (sectionTensorMap C U W).toRingHom,
      evalTensor p q hpU' hqW' k = 0 := by
    intro k hk
    rw [(hΦ k).2, show sectionTensorMap C U W k = 0 from hk, map_zero, analytifyRat_zero]
    rfl
  let F := (sectionTensorMap C U W).toRingHom
  let χ : Γ(C, U ⊓ W) →+* ℂ := F.liftOfRightInverse (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj)
    ⟨(evalTensor p q hpU' hqW').toRingHom, fun k hk => (RingHom.mem_ker).2 (hker k hk)⟩
  have hχ : ∀ k, χ (F k) = evalTensor p q hpU' hqW' k := fun k =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hres : ∀ a : Γ(C, U), χ (C.presheaf.map (homOfLE inf_le_left).op a) = eval a p hpU' := by
    intro a
    have := hχ (a ⊗ₜ 1)
    rw [evalTensor_tmul, eval_one, mul_one] at this
    rw [← this]
    congr 1
    simp [F, sectionTensorMap]
  have hc : ∀ c, χ (constHom (y := y) (U ⊓ W) c) = c := by
    intro c
    rw [← map_constHom (inf_le_left : U ⊓ W ≤ U), hres, eval_constHom]
  have hr := ofRingHom_mem hUW hc
  have hrp : ofRingHom hUW hc = p := eq_of_eval_eq hU (hr.mono inf_le_left) hpU' fun a => by
    rw [← eval_map inf_le_left a _ hr, eval_ofRingHom, hres]
  exact hpW (hrp ▸ hr.mono inf_le_right)

end Values

/-! ### The local rings at complex points of a smooth curve -/

section Stalk

variable [IsCurve ℂ y] [Smooth y]

/-- The local ring of a smooth curve over `ℂ` at a complex point is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_toPoint (p : ComplexPoints y) :
    IsDiscreteValuationRing (C.presheaf.stalk p.toPoint) :=
  IsCurve.isDiscreteValuationRing_stalk_of_isClosed ℂ y (isClosed_singleton_toPoint p)

/-- The point underlying a complex point of a smooth curve has codimension one. -/
theorem coheight_toPoint (p : ComplexPoints y) : Order.coheight p.toPoint = 1 := by
  have := isDiscreteValuationRing_stalk_toPoint p
  have h := ringKrullDim_stalk_eq_coheight p.toPoint
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
  exact_mod_cast h.symm

variable [IsLocallyNoetherian C]

/-- **A nonzero rational function is regular at `p` iff its order of vanishing at `p` is
nonnegative.** -/
theorem isRegularAt_iff_ord_nonneg {g : C.functionField} (hg : g ≠ 0) {p : ComplexPoints y} :
    IsRegularAt g p ↔ 0 ≤ C.ord g p.toPoint := by
  have := isDiscreteValuationRing_stalk_toPoint p
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := isRegularAt_iff_exists_algebraMap.1 h
    have ha : a ≠ 0 := by rintro rfl; exact hg (map_zero _)
    exact Stacks.BombieriStepanov.ord_algebraMap_nonneg (coheight_toPoint p) ha
  · intro h
    exact isRegularAt_iff_exists_algebraMap.2
      (Stacks.BombieriStepanov.exists_algebraMap_eq_of_ord_nonneg (coheight_toPoint p) h)

omit [IsCurve ℂ y] [Smooth y] [IsLocallyNoetherian C] in
/-- The order of vanishing of an inverse. -/
theorem ord_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {g : X.functionField}
    (hg : g ≠ 0) (x : X) : X.ord g⁻¹ x = -X.ord g x := by
  have h := Scheme.ord_mul (x := x) hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, Stacks.BombieriStepanov.scheme_ord_one] at h
  omega

end Stalk

/-! ### Constants -/

section Constants

variable [IsCurve ℂ y]

/-- The constants of the function field, for its `ℂ`-algebra structure
`AlgebraicGeometry.functionFieldAlgebra` induced by `y`, are the images of the constant regular
functions. -/
theorem algebraMap_eq_germToFunctionField_constHom [Nonempty (⊤ : C.Opens)] (c : ℂ) :
    letI := functionFieldAlgebra ℂ y
    algebraMap ℂ C.functionField c = C.germToFunctionField ⊤ (constHom (y := y) ⊤ c) := by
  simp only [RingHom.algebraMap_toAlgebra, constHom, Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- **The analytification of a constant is constant.** -/
theorem analytifyRat_algebraMap (c : ℂ) :
    letI := functionFieldAlgebra ℂ y
    analytifyRat (y := y) (algebraMap ℂ C.functionField c) = fun _ => c := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  funext p
  have : Nonempty (⊤ : C.Opens) := ⟨⟨p.toPoint, trivial⟩⟩
  rw [algebraMap_eq_germToFunctionField_constHom, analytifyRat_germToFunctionField _ (mem_top p),
    eval_constHom]

theorem isRegularAt_algebraMap_const (c : ℂ) (p : ComplexPoints y) :
    letI := functionFieldAlgebra ℂ y
    IsRegularAt (algebraMap ℂ C.functionField c) p := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have : Nonempty (⊤ : C.Opens) := ⟨⟨p.toPoint, trivial⟩⟩
  rw [algebraMap_eq_germToFunctionField_constHom]
  exact ⟨⊤, mem_top p, _, ratGerm_eq_germToFunctionField _ _ _⟩

end Constants

/-! ### The function field is a finite extension of `ℂ(t)` -/

section FiniteExtension

variable [IsCurve ℂ y]

/-- The function field of a curve over `ℂ` is essentially of finite type over `ℂ`. -/
theorem essFiniteType_functionField :
    letI := functionFieldAlgebra ℂ y
    Algebra.EssFiniteType ℂ C.functionField := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  obtain ⟨U, hU, hηU, -⟩ := (Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens)
    (show genericPoint C ∈ (⊤ : C.Opens) from trivial)
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  let _ : Algebra ℂ Γ(C, U) := (constHom (y := y) U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(C, U) := finiteType_constHom (z := y) hU
  have : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  have : Algebra.EssFiniteType Γ(C, U) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors _)
  have : IsScalarTower ℂ Γ(C, U) C.functionField := IsScalarTower.of_algebraMap_eq fun c => by
    rw [algebraMap_eq_germToFunctionField_constHom]
    change _ = C.germToFunctionField U (constHom U c)
    rw [← map_constHom (le_top : U ≤ ⊤), germToFunctionField_map]
  exact Algebra.EssFiniteType.comp ℂ Γ(C, U) C.functionField

omit [IsCurve ℂ y] in
/-- `ℂ(X)` has transcendence degree one over `ℂ`. -/
theorem trdeg_ratFunc : Algebra.trdeg ℂ (RatFunc ℂ) = 1 := by
  have h := trdeg_add_eq ℂ (Polynomial ℂ) (A := RatFunc ℂ)
  have : Algebra.IsAlgebraic (Polynomial ℂ) (RatFunc ℂ) :=
    IsLocalization.isAlgebraic (RatFunc ℂ) (nonZeroDivisors (Polynomial ℂ))
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero (R := Polynomial ℂ), add_zero] at h
  exact h.symm

/-- **The function field of a curve over `ℂ` is algebraic over every subfield `ℂ(t)`**: for any
embedding `ℂ(X) → K` over `ℂ`, `K` is algebraic over `ℂ(X)`, since both have transcendence degree
one over `ℂ`. -/
theorem isAlgebraic_ratFunc [Algebra (RatFunc ℂ) C.functionField]
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) :
    Algebra.IsAlgebraic (RatFunc ℂ) C.functionField := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have : IsScalarTower ℂ (RatFunc ℂ) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (hc c).symm
  have h := trdeg_add_eq ℂ (RatFunc ℂ) (A := C.functionField)
  rw [trdeg_ratFunc, trdeg_functionField_eq_one ℂ y] at h
  rw [← trdeg_eq_zero_iff]
  have hle : Algebra.trdeg (RatFunc ℂ) C.functionField ≤ 1 := h ▸ le_add_self
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (hle.trans_lt Cardinal.one_lt_aleph0)
  rw [hn] at h ⊢
  norm_cast at h ⊢
  omega

/-- **The function field of a curve over `ℂ` is a finite extension of every subfield `ℂ(t)`.** -/
theorem finiteDimensional_ratFunc [Algebra (RatFunc ℂ) C.functionField]
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) :
    FiniteDimensional (RatFunc ℂ) C.functionField := by
  have := isAlgebraic_ratFunc hc
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have : IsScalarTower ℂ (RatFunc ℂ) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (hc c).symm
  have := essFiniteType_functionField (y := y)
  have : Algebra.EssFiniteType (RatFunc ℂ) C.functionField :=
    Algebra.EssFiniteType.of_comp ℂ (RatFunc ℂ) C.functionField
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem isSeparable_ratFunc [Algebra (RatFunc ℂ) C.functionField]
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) :
    Algebra.IsSeparable (RatFunc ℂ) C.functionField := by
  have := isAlgebraic_ratFunc hc
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **A transcendental rational function generates a subfield `ℂ(t)`**: the embedding
`ℂ(X) → K` over `ℂ` sending `X` to `t`, in the form taken by `finiteDimensional_ratFunc` and
`ncard_regularFibre_le_finrank`. -/
theorem exists_algebra_ratFunc {t : C.functionField}
    (ht : letI := functionFieldAlgebra ℂ y; Transcendental ℂ t) :
    ∃ _ : Algebra (RatFunc ℂ) C.functionField,
      algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t ∧
        ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
          algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
            algebraMap ℂ C.functionField c := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have hinj : Function.Injective (Polynomial.aeval (R := ℂ) t) :=
    transcendental_iff_injective.1 ht
  let f := RatFunc.liftAlgHom (Polynomial.aeval (R := ℂ) t)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  refine ⟨f.toRingHom.toAlgebra, ?_, fun c => ?_⟩
  · change f RatFunc.X = t
    rw [← RatFunc.algebraMap_X, RatFunc.liftAlgHom_apply]
    simp
  · change f (algebraMap ℂ (RatFunc ℂ) c) = _
    exact f.commutes c

end FiniteExtension

/-! ### Analytic behaviour at regular points -/

section Analytic

variable [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]

/-- A rational function regular at `p` is holomorphic near `p`. -/
theorem IsRegularAt.eventually_mdifferentiableAt {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) : ∀ᶠ q in 𝓝 p, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (analytifyRat g) q := by
  obtain ⟨V, hp, s, rfl⟩ := hg
  filter_upwards [(analytifyRat_ratGerm_eventuallyEq s hp).eventually_nhds,
    (isOpen_setOf_mem V).mem_nhds hp] with q hq hqV
  rw [Filter.EventuallyEq.mdifferentiableAt_iff (show _ =ᶠ[𝓝 q] _ from hq)]
  exact (mdifferentiableOn_evalOrZero V s q hqV).mdifferentiableAt
    ((isOpen_setOf_mem V).mem_nhds hqV)

theorem IsRegularAt.analyticAt {g : C.functionField} {p : ComplexPoints y} (hg : IsRegularAt g p) :
    AnalyticAt ℂ (analytifyRat g ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
  RiemannSurface.analyticAt_comp_symm_of_eventually_mdifferentiableAt (chart_mem_atlas ℂ p)
    (mem_chart_source ℂ p) hg.eventually_mdifferentiableAt

theorem IsRegularAt.meromorphicAt {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) : RiemannSurface.MeromorphicAt (analytifyRat g) p :=
  RiemannSurface.meromorphicAt_of_eventually_mdifferentiableAt hg.eventually_mdifferentiableAt

theorem IsRegularAt.meromorphicNFAt {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) : RiemannSurface.MeromorphicNFAt (analytifyRat g) p :=
  RiemannSurface.meromorphicNFAt_of_eventually_mdifferentiableAt hg.eventually_mdifferentiableAt

omit [IsCurve ℂ y] in
theorem comp_chartAt_symm_apply (f : ComplexPoints y → ℂ) (p : ComplexPoints y) :
    (f ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) = f p := by
  simp only [Function.comp_apply, (chartAt ℂ p).left_inv (mem_chart_source ℂ p)]

theorem IsRegularAt.orderAt_eq_zero {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (h : analytifyRat g p ≠ 0) :
    RiemannSurface.orderAt (analytifyRat g) p = 0 := by
  rw [RiemannSurface.orderAt, hg.analyticAt.meromorphicOrderAt_eq,
    (hg.analyticAt.analyticOrderAt_eq_zero).2 (by rwa [comp_chartAt_symm_apply])]
  rfl

theorem IsRegularAt.one_le_orderAt {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (h : analytifyRat g p = 0) :
    1 ≤ RiemannSurface.orderAt (analytifyRat g) p := by
  rw [RiemannSurface.orderAt, hg.analyticAt.meromorphicOrderAt_eq]
  have hne : analyticOrderAt (analytifyRat g ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) ≠ 0 := by
    rw [Ne, hg.analyticAt.analyticOrderAt_eq_zero, comp_chartAt_symm_apply, not_not]
    exact h
  generalize analyticOrderAt (analytifyRat g ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) = n at hne
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n =>
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hne)
    simp only [ENat.map_natCast]
    exact_mod_cast this

variable [IsLocallyNoetherian C]

/-- In the analytic order at `p`, a rational function regular at `p` counts as many times as its
algebraic order, measured against a uniformizer `ϖ` of the local ring. -/
theorem orderAt_analytifyRat_eq_ord_mul {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (hg0 : g ≠ 0) {ϖ : C.presheaf.stalk p.toPoint} (hϖ : Irreducible ϖ) :
    RiemannSurface.orderAt (analytifyRat g) p =
      (C.ord g p.toPoint : WithTop ℤ) *
        RiemannSurface.orderAt
          (analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ)) p := by
  have := SmoothOfRelativeDimension.smooth 1 y
  have := isDiscreteValuationRing_stalk_toPoint p
  have hco := coheight_toPoint p
  obtain ⟨a, rfl⟩ := isRegularAt_iff_exists_algebraMap.1 hg
  have ha : a ≠ 0 := by rintro rfl; exact hg0 (map_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hreg : ∀ b : C.presheaf.stalk p.toPoint,
      IsRegularAt (algebraMap (C.presheaf.stalk p.toPoint) C.functionField b) p :=
    isRegularAt_algebraMap
  have hval : analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField u) p *
      analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ↑u⁻¹) p = 1 := by
    rw [← analytifyRat_mul_of_isRegularAt (hreg _) (hreg _),
      ← RingHom.map_mul (algebraMap _ C.functionField),
      Units.mul_inv, RingHom.map_one, analytifyRat_one]
    rfl
  have hu0 : analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField u) p ≠ 0 :=
    left_ne_zero_of_mul_eq_one hval
  have hev : analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField a) =ᶠ[𝓝 p]
      analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField u) *
        analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ) ^ n := by
    filter_upwards [(hreg u).eventually, (hreg ϖ).eventually] with q h1 h2
    rw [hu, RingHom.map_mul (algebraMap _ C.functionField),
      RingHom.map_pow (algebraMap _ C.functionField),
      analytifyRat_mul_of_isRegularAt h1 (h2.pow n),
      analytifyRat_pow_of_isRegularAt h2 n]
    rfl
  have hϖ0 : algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (C.presheaf.stalk p.toPoint) C.functionField)).2
      hϖ.ne_zero
  have hu0' : algebraMap (C.presheaf.stalk p.toPoint) C.functionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (C.presheaf.stalk p.toPoint) C.functionField)).2
      u.ne_zero
  have hpow : ∀ m : ℕ,
      C.ord (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ ^ m) p.toPoint = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih,
        Stacks.BombieriStepanov.ord_algebraMap_irreducible hco hϖ]
      push_cast
      ring
  have hordu : C.ord (algebraMap (C.presheaf.stalk p.toPoint) C.functionField u) p.toPoint = 0 := by
    have h1 := Stacks.BombieriStepanov.ord_algebraMap_nonneg hco u.ne_zero
    have h2 := Stacks.BombieriStepanov.ord_algebraMap_nonneg hco (u⁻¹).ne_zero
    have h3 := Scheme.ord_mul (x := p.toPoint) hu0'
      ((map_ne_zero_iff _ (IsFractionRing.injective (C.presheaf.stalk p.toPoint) C.functionField)).2
        (u⁻¹).ne_zero)
    rw [← RingHom.map_mul (algebraMap _ C.functionField), Units.mul_inv,
      RingHom.map_one,
      Stacks.BombieriStepanov.scheme_ord_one] at h3
    omega
  have hord : C.ord (algebraMap (C.presheaf.stalk p.toPoint) C.functionField a) p.toPoint = n := by
    rw [hu, RingHom.map_mul (algebraMap _ C.functionField),
      RingHom.map_pow (algebraMap _ C.functionField),
      Scheme.ord_mul hu0' (pow_ne_zero _ hϖ0),
      hordu, hpow, zero_add]
  rw [RiemannSurface.orderAt_congr (hev.filter_mono nhdsWithin_le_nhds),
    RiemannSurface.orderAt_mul (hreg u).meromorphicAt ((hreg ϖ).meromorphicAt.pow n),
    RiemannSurface.orderAt_pow (hreg ϖ).meromorphicAt, (hreg u).orderAt_eq_zero hu0, zero_add,
    hord]
  rfl

/-- **A uniformizer is a local coordinate.** For an irreducible element `ϖ` of the local ring at
`p`, the analytification of `ϖ` has a simple zero at `p`. -/
theorem orderAt_analytifyRat_irreducible {p : ComplexPoints y}
    {ϖ : C.presheaf.stalk p.toPoint} (hϖ : Irreducible ϖ) :
    RiemannSurface.orderAt
      (analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ)) p = 1 := by
  have := SmoothOfRelativeDimension.smooth 1 y
  have := isDiscreteValuationRing_stalk_toPoint p
  have hco := coheight_toPoint p
  set e := chartAt ℂ p
  obtain ⟨⟨V₀, t, hV₀, heq⟩, -⟩ := isCurveChart_chartAt p
  have hp0 : p.Mem V₀ := hV₀ p (mem_chart_source ℂ p)
  set σ : Γ(C, V₀) := t - constHom V₀ (e p)
  have hσ : ∀ q (hq : q.Mem V₀), q ∈ e.source → eval σ q hq = e q - e p := by
    intro q hq hqs
    rw [← evalHom_apply, map_sub, evalHom_apply, evalHom_apply, eval_constHom,
      ← evalOrZero_of_mem _ hq, ← heq hqs]
  have hτev : analytifyRat (ratGerm σ p hp0) =ᶠ[𝓝 p] fun q => e q - e p := by
    filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ p)] with q hq
    rw [analytifyRat_ratGerm σ hp0 (hV₀ q hq), hσ q _ hq]
  have hτord : RiemannSurface.orderAt (analytifyRat (ratGerm σ p hp0)) p = 1 := by
    rw [RiemannSurface.orderAt_congr (hτev.filter_mono nhdsWithin_le_nhds), RiemannSurface.orderAt]
    rw [meromorphicOrderAt_congr (f₂ := fun z => z - e p)]
    · exact meromorphicOrderAt_id_sub_const
    · filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds (e.map_source
        (mem_chart_source ℂ p)))] with z hz
      exact congrArg (· - _) ((chartAt ℂ p).right_inv hz)
  set a : C.presheaf.stalk p.toPoint := C.presheaf.germ V₀ p.toPoint (mem_iff_toPoint_mem.1 hp0) σ
  have hτ : ratGerm σ p hp0 = algebraMap (C.presheaf.stalk p.toPoint) C.functionField a := rfl
  have ha0 : a ≠ 0 := by
    rintro ha
    rw [hτ, ha, map_zero, analytifyRat_zero, (RiemannSurface.orderAt_eq_top_iff
      (f := (0 : ComplexPoints y → ℂ))).2 (Eventually.of_forall fun _ => rfl)] at hτord
    exact WithTop.top_ne_coe hτord
  have ham : a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk p.toPoint) := by
    rw [← eval_eq_zero_iff_germ_mem_maximalIdeal σ hp0, hσ p hp0 (mem_chart_source ℂ p), sub_self]
  have hm := Stacks.BombieriStepanov.one_le_ord_algebraMap hco ha0 ham
  have hτ0 : algebraMap (C.presheaf.stalk p.toPoint) C.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (C.presheaf.stalk p.toPoint) C.functionField)).2
      ha0
  have key := orderAt_analytifyRat_eq_ord_mul (isRegularAt_algebraMap a) hτ0 hϖ
  rw [← hτ, hτord] at key
  have hk : 1 ≤ RiemannSurface.orderAt
      (analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ)) p :=
    (isRegularAt_algebraMap ϖ).one_le_orderAt ((analytifyRat_algebraMap_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit))
  generalize RiemannSurface.orderAt
    (analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField ϖ)) p = k at key hk ⊢
  rw [← hτ] at hm
  generalize C.ord (ratGerm σ p hp0) p.toPoint = m at key hm
  induction k using WithTop.recTopCoe with
  | top =>
    rw [WithTop.mul_top (by exact_mod_cast (show m ≠ 0 by omega))] at key
    exact absurd key WithTop.coe_ne_top
  | coe k =>
    have hk' : 1 ≤ k := by exact_mod_cast hk
    have hmk : 1 = m * k := by exact_mod_cast key
    have : k = 1 := by nlinarith
    rw [this]
    rfl

/-- **The analytic order of a regular function is its algebraic order.** -/
theorem orderAt_analytifyRat_of_isRegularAt {g : C.functionField} {p : ComplexPoints y}
    (hg : IsRegularAt g p) (hg0 : g ≠ 0) :
    RiemannSurface.orderAt (analytifyRat g) p = C.ord g p.toPoint := by
  have := SmoothOfRelativeDimension.smooth 1 y
  have := isDiscreteValuationRing_stalk_toPoint p
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk p.toPoint)
  rw [orderAt_analytifyRat_eq_ord_mul hg hg0 hϖ, orderAt_analytifyRat_irreducible hϖ, mul_one]

/-- **Every rational function is, near `p`, a quotient of two functions regular at `p`**,
the denominator vanishing nowhere on a punctured neighbourhood of `p`; on that punctured
neighbourhood the rational function is regular and its analytification is the quotient. -/
theorem exists_eventually_eq_div (g : C.functionField) (p : ComplexPoints y) :
    ∃ a b : C.functionField, IsRegularAt a p ∧ IsRegularAt b p ∧ b ≠ 0 ∧ g = a / b ∧
      ∀ᶠ q in 𝓝[≠] p, IsRegularAt g q ∧
        analytifyRat g q = ((analytifyRat a * (analytifyRat b)⁻¹ : ComplexPoints y → ℂ)) q := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (C.presheaf.stalk p.toPoint) g
  have hb0 : algebraMap (C.presheaf.stalk p.toPoint) C.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hb)
  have hrb := isRegularAt_algebraMap b
  have hra := isRegularAt_algebraMap a
  have hne : ∀ᶠ q in 𝓝[≠] p,
      analytifyRat (algebraMap (C.presheaf.stalk p.toPoint) C.functionField b) q ≠ 0 := by
    have hord := orderAt_analytifyRat_of_isRegularAt hrb hb0
    rcases hrb.meromorphicAt.eventually_eq_zero_or_eventually_ne_zero with h | h
    · rw [RiemannSurface.orderAt_eq_top_iff.2 h] at hord
      exact absurd hord.symm WithTop.coe_ne_top
    · exact h
  refine ⟨_, _, hra, hrb, hb0, rfl, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hra.eventually, nhdsWithin_le_nhds hrb.eventually, hne]
    with q h1 h2 h3
  obtain ⟨hinv, hval⟩ := h2.inv h3
  rw [div_eq_mul_inv]
  exact ⟨h1.mul hinv, by rw [analytifyRat_mul_of_isRegularAt h1 hinv, hval]; rfl⟩

/-- A rational function is regular on a punctured neighbourhood of every point. -/
theorem eventually_isRegularAt (g : C.functionField) (p : ComplexPoints y) :
    ∀ᶠ q in 𝓝[≠] p, IsRegularAt g q := by
  obtain ⟨_, _, -, -, -, -, h⟩ := exists_eventually_eq_div g p
  exact h.mono fun _ h => h.1

/-- **The analytification of a rational function is meromorphic.** -/
theorem meromorphicAt_analytifyRat (g : C.functionField) (p : ComplexPoints y) :
    RiemannSurface.MeromorphicAt (analytifyRat g) p := by
  obtain ⟨a, b, ha, hb, -, -, h⟩ := exists_eventually_eq_div g p
  exact (ha.meromorphicAt.mul hb.meromorphicAt.inv).congr (h.mono fun _ h => h.2.symm)

theorem meromorphicOn_analytifyRat (g : C.functionField) (U : Set (ComplexPoints y)) :
    RiemannSurface.MeromorphicOn (analytifyRat g) U := fun p _ => meromorphicAt_analytifyRat g p

/-- **The analytic order of a rational function is its order of vanishing**: at every complex
point `p`, the order of the meromorphic function `analytifyRat g` is `ord_p(g)`, the order of
vanishing of `g` at the closed point `p` of `C`. -/
theorem orderAt_analytifyRat {g : C.functionField} (hg : g ≠ 0) (p : ComplexPoints y) :
    RiemannSurface.orderAt (analytifyRat g) p = C.ord g p.toPoint := by
  obtain ⟨a, b, ha, hb, hb0, rfl, h⟩ := exists_eventually_eq_div g p
  have ha0 : a ≠ 0 := by rintro rfl; exact hg (zero_div b)
  rw [RiemannSurface.orderAt_congr (h.mono fun _ h => h.2),
    RiemannSurface.orderAt_mul ha.meromorphicAt hb.meromorphicAt.inv, RiemannSurface.orderAt_inv,
    orderAt_analytifyRat_of_isRegularAt ha ha0, orderAt_analytifyRat_of_isRegularAt hb hb0,
    div_eq_mul_inv, Scheme.ord_mul ha0 (inv_ne_zero hb0), ord_inv hb0]
  norm_cast

theorem orderAt_analytifyRat_ne_top {g : C.functionField} (hg : g ≠ 0) (p : ComplexPoints y) :
    RiemannSurface.orderAt (analytifyRat g) p ≠ ⊤ := by
  rw [orderAt_analytifyRat hg]
  exact WithTop.coe_ne_top

/-- **The analytification of a rational function is in meromorphic normal form**: its value at a
pole is `0`, and elsewhere it is holomorphic. -/
theorem meromorphicNFAt_analytifyRat (g : C.functionField) (p : ComplexPoints y) :
    RiemannSurface.MeromorphicNFAt (analytifyRat g) p := by
  by_cases hr : IsRegularAt g p
  · exact hr.meromorphicNFAt
  have hg0 : g ≠ 0 := by rintro rfl; exact hr (isRegularAt_zero p)
  have := SmoothOfRelativeDimension.smooth 1 y
  have hneg : C.ord g p.toPoint < 0 := by
    rw [← not_le, ← isRegularAt_iff_ord_nonneg hg0]
    exact hr
  have hord := orderAt_analytifyRat hg0 p
  rw [RiemannSurface.MeromorphicNFAt, meromorphicNFAt_iff_analyticAt_or]
  refine Or.inr ⟨meromorphicAt_analytifyRat g p, ?_, ?_⟩
  · rw [RiemannSurface.orderAt] at hord
    rw [hord]
    exact_mod_cast hneg
  · rw [comp_chartAt_symm_apply, analytifyRat_of_not_isRegularAt hr]

theorem analytifyRat_mul_eventuallyEq (g h : C.functionField) :
    analytifyRat (g * h) =ᶠ[codiscrete (ComplexPoints y)] analytifyRat g * analytifyRat h := by
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro p
  filter_upwards [eventually_isRegularAt g p, eventually_isRegularAt h p] with q h1 h2
  exact analytifyRat_mul_of_isRegularAt h1 h2

theorem analytifyRat_add_eventuallyEq (g h : C.functionField) :
    analytifyRat (g + h) =ᶠ[codiscrete (ComplexPoints y)] analytifyRat g + analytifyRat h := by
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro p
  filter_upwards [eventually_isRegularAt g p, eventually_isRegularAt h p] with q h1 h2
  exact analytifyRat_add_of_isRegularAt h1 h2

theorem analytifyRat_sub_eventuallyEq (g h : C.functionField) :
    analytifyRat (g - h) =ᶠ[codiscrete (ComplexPoints y)] analytifyRat g - analytifyRat h := by
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro p
  filter_upwards [eventually_isRegularAt g p, eventually_isRegularAt h p] with q h1 h2
  exact analytifyRat_sub_of_isRegularAt h1 h2

/-- A nonzero rational function has nonvanishing analytification near every point, away from the
point itself. -/
theorem eventually_analytifyRat_ne_zero {g : C.functionField} (hg : g ≠ 0) (p : ComplexPoints y) :
    ∀ᶠ q in 𝓝[≠] p, analytifyRat g q ≠ 0 := by
  rcases (meromorphicAt_analytifyRat g p).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (RiemannSurface.orderAt_eq_top_iff.2 h) (orderAt_analytifyRat_ne_top hg p)
  · exact h

theorem analytifyRat_inv_eventuallyEq (g : C.functionField) :
    analytifyRat g⁻¹ =ᶠ[codiscrete (ComplexPoints y)] (analytifyRat g)⁻¹ := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact Eventually.of_forall fun q => by simp
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro p
  filter_upwards [eventually_isRegularAt g p, eventually_analytifyRat_ne_zero hg p] with q h1 h2
  exact (h1.inv h2).2

/-- The analytification determines the rational function: `g = 0` as soon as its
analytification vanishes on a punctured neighbourhood of a single point. -/
theorem eq_zero_of_analytifyRat_eventuallyEq_zero {g : C.functionField} {p : ComplexPoints y}
    (h : ∀ᶠ q in 𝓝[≠] p, analytifyRat g q = 0) : g = 0 := by
  by_contra hg
  exact orderAt_analytifyRat_ne_top hg p (RiemannSurface.orderAt_eq_top_iff.2 h)

/-- **A nonconstant rational function minus a constant has finite order everywhere**, the
hypothesis under which a meromorphic function is a branched covering of the sphere. -/
theorem orderAt_analytifyRat_sub_const_ne_top {g : C.functionField}
    (hg : letI := functionFieldAlgebra ℂ y; g ∉ Set.range (algebraMap ℂ C.functionField))
    (p : ComplexPoints y) (c : ℂ) :
    RiemannSurface.orderAt (fun q => analytifyRat g q - c) p ≠ ⊤ := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have hne : g - algebraMap ℂ C.functionField c ≠ 0 := fun h =>
    hg ⟨c, (sub_eq_zero.1 h).symm⟩
  have hev : analytifyRat (g - algebraMap ℂ C.functionField c) =ᶠ[𝓝[≠] p]
      fun q => analytifyRat g q - c := by
    have := (eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1
      (analytifyRat_sub_eventuallyEq (y := y) g (algebraMap ℂ C.functionField c))) p
    filter_upwards [this] with q hq
    rw [hq, Pi.sub_apply, analytifyRat_algebraMap]
  rw [← RiemannSurface.orderAt_congr hev]
  exact orderAt_analytifyRat_ne_top hne p

end Analytic

/-! ### Fibres of a rational function -/

section Fibre

open scoped _root_.Polynomial

variable [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C]

/-- A rational function whose analytification is holomorphic at `p` is regular at `p`. -/
theorem isRegularAt_of_mdifferentiableAt {g : C.functionField} {p : ComplexPoints y}
    (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (analytifyRat g) p) : IsRegularAt g p := by
  by_contra hr
  have hg0 : g ≠ 0 := by rintro rfl; exact hr (isRegularAt_zero p)
  have := SmoothOfRelativeDimension.smooth 1 y
  have hneg : C.ord g p.toPoint < 0 := by
    rw [← not_le, ← isRegularAt_iff_ord_nonneg hg0]
    exact hr
  have han : AnalyticAt ℂ (analytifyRat g ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
    (RiemannSurface.mdifferentiableAt_iff_analyticAt_chart
      (fun x => meromorphicNFAt_analytifyRat g x)).1 h
  have h0 : 0 ≤ RiemannSurface.orderAt (analytifyRat g) p :=
    (_root_.MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt
      (meromorphicNFAt_analytifyRat g p)).2 han
  rw [orderAt_analytifyRat hg0] at h0
  have : (0 : ℤ) ≤ C.ord g p.toPoint := by exact_mod_cast h0
  omega

variable [Algebra ℂ[X] C.functionField] {t : C.functionField}

omit [IsLocallyNoetherian C] in
/-- If `t` is regular at `p`, so is every element of the function field integral over `ℂ[t]`:
the local ring at `p` is integrally closed. -/
theorem isRegularAt_of_isIntegral (ht : algebraMap ℂ[X] C.functionField Polynomial.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap ℂ[X] C.functionField (Polynomial.C c) = algebraMap ℂ C.functionField c)
    {p : ComplexPoints y} (htp : IsRegularAt t p) {s : C.functionField}
    (hs : _root_.IsIntegral ℂ[X] s) : IsRegularAt s p := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have := SmoothOfRelativeDimension.smooth 1 y
  have := isDiscreteValuationRing_stalk_toPoint p
  have : Nonempty (⊤ : C.Opens) := ⟨⟨p.toPoint, trivial⟩⟩
  obtain ⟨a, ha⟩ := isRegularAt_iff_exists_algebraMap.1 htp
  let ψ : ℂ →+* C.presheaf.stalk p.toPoint :=
    (C.presheaf.germ ⊤ p.toPoint (show p.toPoint ∈ (⊤ : C.Opens) from trivial)).hom.comp
      (constHom (y := y) ⊤)
  let φ : ℂ[X] →+* C.presheaf.stalk p.toPoint := Polynomial.eval₂RingHom ψ a
  let _ : Algebra ℂ[X] (C.presheaf.stalk p.toPoint) := φ.toAlgebra
  have hφ : (algebraMap (C.presheaf.stalk p.toPoint) C.functionField).comp φ =
      algebraMap ℂ[X] C.functionField := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, ψ]
      rw [Scheme.algebraMap_germ_eq_germToFunctionField, hc c,
        algebraMap_eq_germToFunctionField_constHom]
    · simp only [RingHom.comp_apply, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, ha, ht]
  have : IsScalarTower ℂ[X] (C.presheaf.stalk p.toPoint) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun P => (RingHom.congr_fun hφ P).symm
  have key : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
      IsIntegrallyClosed R := fun _ _ _ _ => inferInstance
  have : IsIntegrallyClosed (C.presheaf.stalk p.toPoint) := key _
  exact isRegularAt_iff_exists_algebraMap.2
    ((IsIntegrallyClosed.isIntegral_iff (R := C.presheaf.stalk p.toPoint)
      (K := C.functionField)).1 (hs.tower_top (A := C.presheaf.stalk p.toPoint)))

omit [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C] in
/-- The value at `p` of a polynomial in `t` is the polynomial evaluated at `t(p)`. -/
theorem analytifyRat_algebraMap_polynomial (ht : algebraMap ℂ[X] C.functionField Polynomial.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap ℂ[X] C.functionField (Polynomial.C c) = algebraMap ℂ C.functionField c)
    {p : ComplexPoints y} (htp : IsRegularAt t p) (P : ℂ[X]) :
    IsRegularAt (algebraMap ℂ[X] C.functionField P) p ∧
      analytifyRat (algebraMap ℂ[X] C.functionField P) p = P.eval (analytifyRat t p) := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  induction P using Polynomial.induction_on with
  | C c =>
    rw [hc c, analytifyRat_algebraMap, Polynomial.eval_C]
    exact ⟨isRegularAt_algebraMap_const c p, rfl⟩
  | add P Q hP hQ =>
    rw [RingHom.map_add (algebraMap ℂ[X] C.functionField),
      analytifyRat_add_of_isRegularAt hP.1 hQ.1, hP.2, hQ.2,
      Polynomial.eval_add]
    exact ⟨hP.1.add hQ.1, rfl⟩
  | monomial n c h =>
    have e : (Polynomial.C c * Polynomial.X ^ (n + 1) : ℂ[X]) =
        Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by ring
    rw [e, RingHom.map_mul (algebraMap ℂ[X] C.functionField), ht,
      analytifyRat_mul_of_isRegularAt h.1 htp, h.2,
      Polynomial.eval_mul_X]
    exact ⟨h.1.mul htp, rfl⟩

omit [Algebra ℂ[X] C.functionField] in
/-- **A regular fibre of a rational function has at most `[K : ℂ(t)]` points.** Let `t` be a
rational function on `C` and let `ℂ(X) → K` be the embedding of fields over `ℂ` sending `X` to `t`.
For every `b : ℂ`, the points `x ∈ C(ℂ)` at which `t` is holomorphic with `t(x) = b` number at most
`[K : ℂ(t)]`.

Each such point `x` gives the prime `𝔮_x` of the integral closure `S` of `ℂ[t]` in `K` of the
functions of `S` vanishing at `x`; it lies over `(t - b)`. Distinct points give distinct primes:
the local ring of `S` at `𝔮_x` is a discrete valuation ring, so every rational function regular at
`x` is a quotient `s / u` with `u ∉ 𝔮_x`, and `x` is determined by the rational functions regular
at it, `C` being separated. At most `[K : ℂ(t)]` primes of `S` lie over `(t - b)`
(`Polynomial.ncard_primesOver_X_sub_C_le_finrank`). -/
theorem ncard_regularFibre_le_finrank [Algebra (RatFunc ℂ) C.functionField]
    {t : C.functionField} (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c)
    (b : ℂ) :
    (RiemannSurface.regularFibre (analytifyRat (y := y) t) b).ncard ≤
      Module.finrank (RatFunc ℂ) C.functionField := by
  let _ : Algebra ℂ C.functionField := functionFieldAlgebra ℂ y
  have := finiteDimensional_ratFunc hc
  have := isSeparable_ratFunc hc
  let _ : Algebra ℂ[X] C.functionField :=
    ((algebraMap (RatFunc ℂ) C.functionField).comp (algebraMap ℂ[X] (RatFunc ℂ))).toAlgebra
  have : IsScalarTower ℂ[X] (RatFunc ℂ) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htX : algebraMap ℂ[X] C.functionField Polynomial.X = t := by
    change algebraMap (RatFunc ℂ) _ (algebraMap ℂ[X] (RatFunc ℂ) Polynomial.X) = t
    rw [RatFunc.algebraMap_X, ht]
  have hcP : ∀ c : ℂ, algebraMap ℂ[X] C.functionField (Polynomial.C c) =
      algebraMap ℂ C.functionField c := by
    intro c
    change algebraMap (RatFunc ℂ) _ (algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c)) = _
    rw [← hc c, RatFunc.algebraMap_C]
    rfl
  have hinj : Function.Injective (algebraMap ℂ[X] C.functionField) :=
    (algebraMap (RatFunc ℂ) C.functionField).injective.comp
      (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
  let S := integralClosure ℂ[X] C.functionField
  have : IsFractionRing S C.functionField :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℂ[X] (RatFunc ℂ) C.functionField S
  set F := RiemannSurface.regularFibre (analytifyRat (y := y) t) b with hF
  have hregt : ∀ x ∈ F, IsRegularAt t x := fun x hx => isRegularAt_of_mdifferentiableAt hx.1
  have hregS : ∀ x ∈ F, ∀ s : S, IsRegularAt (s : C.functionField) x := fun x hx s =>
    isRegularAt_of_isIntegral htX hcP (hregt x hx) s.2
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ x ∈ F, S →+* ℂ,
      ∀ x (hx : x ∈ F) (s : S), ev x hx s = analytifyRat (s : C.functionField) x :=
    ⟨fun x hx =>
      { toFun := fun s => analytifyRat (s : C.functionField) x
        map_one' := by simp
        map_mul' := fun s s' => analytifyRat_mul_of_isRegularAt (hregS x hx s) (hregS x hx s')
        map_zero' := by simp
        map_add' := fun s s' => analytifyRat_add_of_isRegularAt (hregS x hx s) (hregS x hx s') },
      fun _ _ _ => rfl⟩
  have hevP : ∀ x (hx : x ∈ F) (P : ℂ[X]), ev x hx (algebraMap ℂ[X] S P) = P.eval b := by
    intro x hx P
    rw [hev x hx]
    change analytifyRat (algebraMap ℂ[X] C.functionField P) x = _
    rw [(analytifyRat_algebraMap_polynomial htX hcP (hregt x hx) P).2, hx.2]
  have hker : ∀ x (hx : x ∈ F), Ideal.comap (algebraMap ℂ[X] S) (RingHom.ker (ev x hx)) =
      Ideal.span {Polynomial.X - Polynomial.C b} := by
    intro x hx
    rw [RingHom.comap_ker, ← Polynomial.ker_evalRingHom]
    congr 1
    exact RingHom.ext (hevP x hx)
  have hconst : ∀ x (hx : x ∈ F) (c : ℂ), ev x hx (algebraMap ℂ[X] S (Polynomial.C c)) = c := by
    intro x hx c
    rw [hevP x hx, Polynomial.eval_C]
  have hevEq : ∀ x (hx : x ∈ F) x' (hx' : x' ∈ F), RingHom.ker (ev x hx) = RingHom.ker (ev x' hx') →
      ∀ s, ev x' hx' s = ev x hx s := by
    intro x hx x' hx' h s
    have hmem : s - algebraMap ℂ[X] S (Polynomial.C (ev x hx s)) ∈ RingHom.ker (ev x hx) := by
      rw [RingHom.mem_ker, RingHom.map_sub (ev x hx), hconst x hx, sub_self]
    rw [h, RingHom.mem_ker, RingHom.map_sub (ev x' hx'), hconst x' hx', sub_eq_zero] at hmem
    exact hmem
  have htransfer : ∀ x (hx : x ∈ F) x' (hx' : x' ∈ F),
      RingHom.ker (ev x hx) = RingHom.ker (ev x' hx') →
      ∀ g, IsRegularAt g x → IsRegularAt g x' ∧ analytifyRat g x' = analytifyRat g x := by
    intro x hx x' hx' h g hg
    rcases eq_or_ne g 0 with rfl | hg0
    · exact ⟨isRegularAt_zero x', by simp⟩
    have h𝔮 : (RingHom.ker (ev x hx)).IsPrime := RingHom.ker_isPrime _
    have h𝔮0 : RingHom.ker (ev x hx) ≠ ⊥ := by
      intro h0
      have hmem : algebraMap ℂ[X] S (Polynomial.X - Polynomial.C b) ∈ RingHom.ker (ev x hx) := by
        rw [RingHom.mem_ker, hevP x hx]
        simp
      rw [h0, Ideal.mem_bot] at hmem
      have : algebraMap ℂ[X] C.functionField (Polynomial.X - Polynomial.C b) = 0 := by
        change ((algebraMap ℂ[X] S (Polynomial.X - Polynomial.C b) : S) : C.functionField) = 0
        rw [hmem]
        rfl
      exact Polynomial.X_sub_C_ne_zero b (hinj (this.trans (map_zero _).symm))
    have hval : ∀ s u : S, u ∉ RingHom.ker (ev x hx) →
        IsRegularAt ((s : C.functionField) * (u : C.functionField)⁻¹) x' ∧
          analytifyRat ((s : C.functionField) * (u : C.functionField)⁻¹) x' =
            analytifyRat ((s : C.functionField) * (u : C.functionField)⁻¹) x := by
      intro s u hu
      have hux : ev x hx u ≠ 0 := fun h0 => hu (RingHom.mem_ker.2 h0)
      have hux' : ev x' hx' u ≠ 0 := by rwa [hevEq x hx x' hx' h]
      rw [hev x hx] at hux
      rw [hev x' hx'] at hux'
      obtain ⟨hi', hv'⟩ := (hregS x' hx' u).inv hux'
      obtain ⟨hi, hv⟩ := (hregS x hx u).inv hux
      refine ⟨(hregS x' hx' s).mul hi', ?_⟩
      rw [analytifyRat_mul_of_isRegularAt (hregS x' hx' s) hi',
        analytifyRat_mul_of_isRegularAt (hregS x hx s) hi, hv', hv]
      have e1 := hevEq x hx x' hx' h s
      have e2 := hevEq x hx x' hx' h u
      rw [hev x' hx', hev x hx] at e1 e2
      rw [e1, e2]
    rcases IsDedekindDomain.exists_eq_mul_inv_or_exists_inv_mul_eq h𝔮0 g with
      ⟨s, u, hu, rfl⟩ | ⟨s, u, hs, hu, hK⟩
    · exact hval s u hu
    · exfalso
      have hK' : g⁻¹ * (u : C.functionField) = (s : C.functionField) := hK
      have hgs : g * (s : C.functionField) = (u : C.functionField) := by
        rw [← hK', ← mul_assoc, mul_inv_cancel₀ hg0, one_mul]
      have hv := analytifyRat_mul_of_isRegularAt hg (hregS x hx s)
      rw [hgs] at hv
      have hs0 : ev x hx s = 0 := RingHom.mem_ker.1 hs
      rw [hev x hx] at hs0
      exact hu (RingHom.mem_ker.2 (by rw [hev x hx, hv, hs0, mul_zero]))
  let q : ComplexPoints y → Ideal S := fun x =>
    open Classical in if hx : x ∈ F then RingHom.ker (ev x hx) else ⊥
  have hq : ∀ x (hx : x ∈ F), q x = RingHom.ker (ev x hx) := fun x hx => by
    simp only [q, hx, ↓reduceDIte]
  have := Polynomial.isMaximal_span_X_sub_C b
  refine (Set.ncard_le_ncard_of_injOn q ?_ ?_ ?_).trans
    (Polynomial.ncard_primesOver_X_sub_C_le_finrank C.functionField S b)
  · intro x hx
    rw [hq x hx]
    exact ⟨RingHom.ker_isPrime _, ⟨(hker x hx).symm⟩⟩
  · intro x hx x' hx' hqq
    rw [hq x hx, hq x' hx'] at hqq
    exact eq_of_forall_isRegularAt_iff
      (fun g => ⟨fun h => (htransfer x hx x' hx' hqq g h).1,
        fun h => (htransfer x' hx' x hx hqq.symm g h).1⟩)
      (fun g h => (htransfer x hx x' hx' hqq g h).2)
  · have hTF : ∀ (R T : Type) [CommRing R] [IsDomain R] [CommRing T] [IsDomain T] [Algebra R T]
        [FaithfulSMul R T], Module.IsTorsionFree R T := fun _ _ _ _ _ _ _ _ => inferInstance
    have : FaithfulSMul ℂ[X] S := by
      rw [faithfulSMul_iff_algebraMap_injective]
      refine Function.Injective.of_comp (f := algebraMap S C.functionField) ?_
      exact hinj
    have : Module.IsTorsionFree ℂ[X] S := hTF _ _
    rw [← IsDedekindDomain.coe_primesOverFinset (Polynomial.span_X_sub_C_ne_bot b) S]
    exact Finset.finite_toSet _

end Fibre

end AlgebraicGeometry.Scheme.ComplexPoints
