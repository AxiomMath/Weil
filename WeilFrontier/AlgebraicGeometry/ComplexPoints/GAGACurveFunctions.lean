/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.RationalFunctions
public import WeilFrontier.Geometry.Manifold.Complex.SymmetricFunctions
public import WeilFrontier.FieldTheory.Minpoly.FinrankLeOfDegreeBound
public import WeilFrontier.Geometry.Manifold.Sheaf.HolomorphicCohomology

/-!
# GAGA for functions on a compact smooth curve over `ℂ`

Let `C` be a smooth curve over `ℂ` with function field `K` whose complex points `X = C(ℂ)` form a
compact Riemann surface (for instance `C` projective). We prove:

* `X` is connected;
* every meromorphic function on `X` is, away from a discrete set, the analytification of a unique
  rational function on `C`;
* the regular functions on `C` are exactly the holomorphic functions on `X`.

The argument is a degree count. Choose a transcendental `t ∈ K`, so that `K` is a finite extension
of `ℂ(t)` of some degree `D`, and let `d` be the number of points of a generic fibre of the
analytification `t_an : X → ℙ¹(ℂ)`. A generic fibre has at most `D` points, so `d ≤ D`. If `U ⊆ X`
is a nonempty clopen set, every meromorphic function on `U` is a root of a polynomial of degree
`d_U` over `ℂ(t)`, where `d_U` is the fibre degree of `t_an` restricted to `U`; applied to the
analytifications of the elements of `K`, this shows that every element of `K` has degree at most
`d_U` over `ℂ(t)`, so `D ≤ d_U`. As the fibre degrees of a clopen set and of its complement add up
to `d`, the space `X` cannot be split into two nonempty clopen sets.

The germs of meromorphic functions on the connected Riemann surface `X` along the filter of
complements of discrete closed sets form an integral domain `𝓜(X)` containing `K`. Every element
of `𝓜(X)` is algebraic of degree at most `d` over `ℂ(t)`; hence `𝓜(X)` is a field, of degree at
most `d ≤ D` over `ℂ(t)`, and the inclusion `K ⊆ 𝓜(X)` of `ℂ(t)`-vector spaces of the same
finite dimension is an equality.

## Main definitions

* `RiemannSurface.meromorphicGerms`: the meromorphic functions on a Riemann surface, modulo
  equality away from a discrete closed set, as a subring of the germs along `codiscrete M`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analytifyRatGerm`,
  `AlgebraicGeometry.Scheme.ComplexPoints.analytifyRatMeromorphic`: the analytification of rational
  functions, as a ring homomorphism to these germs.
* `AlgebraicGeometry.Scheme.ComplexPoints.globalSectionsToHolomorphic`: a regular function on `C`
  as a global section of the sheaf of holomorphic functions on `X`.

## Main results

* `RiemannSurface.isDomain_meromorphicGerms`: on a connected Riemann surface the meromorphic germs
  form an integral domain.
* `AlgebraicGeometry.Scheme.ComplexPoints.connectedSpace`: `C(ℂ)` is connected.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_eq_analytifyRat`: every meromorphic function on
  `C(ℂ)` is the analytification of a rational function, away from a discrete closed set;
  `analytifyRat_injective` gives its uniqueness; `functionFieldEquivMeromorphicGerms` is the
  resulting isomorphism of the function field with the field of meromorphic germs.
* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_evalOrZero_top` and
  `bijective_globalSectionsToHolomorphic`: `Γ(C, 𝒪_C)` is the ring of holomorphic functions on
  `C(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.finrank_le_fibreDegree`,
  `fibreDegree_le_finrank`, `fibreDegree_eq_finrank`: the fibre degree of the analytification of a
  transcendental `t` is `[K : ℂ(t)]`.

## Implementation notes

Compactness of `C(ℂ)` is a hypothesis `[CompactSpace (ComplexPoints y)]`: it holds when `C` is
projective (`AlgebraicGeometry.Scheme.ComplexPoints.compactSpace_of_isProjective`), and the results
are stated in this generality. The holomorphic functions on `C(ℂ)` are constant by the maximum
principle on a compact connected complex manifold, which identifies them with the constant regular
functions without passing through the rational functions. The statements are for curves only;
GAGA for functions on projective schemes of higher dimension is not treated.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
* [For] O. Forster, *Lectures on Riemann Surfaces*, §8.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Filter Manifold Opposite
open scoped Polynomial

/-! ### Meromorphic germs on a Riemann surface -/

namespace RiemannSurface

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The meromorphic functions on a Riemann surface `M`, modulo equality away from a discrete
closed set, as a subring of the germs of functions along `codiscrete M`. -/
def meromorphicGerms : Subring ((codiscrete M).Germ ℂ) where
  carrier := {φ | ∃ f : M → ℂ, MeromorphicOn f Set.univ ∧ (f : (codiscrete M).Germ ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, meromorphicOn_const 1 _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, meromorphicOn_const 0 _, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

variable {M}

theorem coe_mem_meromorphicGerms {f : M → ℂ} (hf : MeromorphicOn f Set.univ) :
    (f : (codiscrete M).Germ ℂ) ∈ meromorphicGerms M :=
  ⟨f, hf, rfl⟩

/-- On a connected Riemann surface a meromorphic function vanishes away from a discrete closed set
as soon as it vanishes on a punctured neighbourhood of one point. -/
theorem coe_eq_zero_iff_eventually_eq_zero [T1Space M] [PreconnectedSpace M] {f : M → ℂ}
    (hf : MeromorphicOn f Set.univ) (x₀ : M) :
    (f : (codiscrete M).Germ ℂ) = 0 ↔ ∀ᶠ x in 𝓝[≠] x₀, f x = 0 := by
  constructor
  · intro h
    exact (eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 (Germ.coe_eq.1 h)) x₀
  · intro h
    exact Germ.coe_eq.2 (eventuallyEq_codiscreteWithin_of_isPreconnected hf
      (meromorphicOn_const 0 _) isPreconnected_univ (Set.mem_univ x₀) h)

/-- **On a connected Riemann surface the meromorphic germs form an integral domain**: a meromorphic
function vanishes identically near a point or has isolated zeros there, and by the identity theorem
the first alternative at one point makes it vanish away from a discrete closed set. -/
theorem isDomain_meromorphicGerms [T1Space M] [ConnectedSpace M] :
    IsDomain (meromorphicGerms M) := by
  obtain ⟨x₀⟩ := ‹ConnectedSpace M›.toNonempty
  have hne : (𝓝[≠] x₀).NeBot := nhdsNE_neBot x₀
  refine @NoZeroDivisors.to_isDomain _ _ ⟨⟨1, 0, fun h => ?_⟩⟩ ⟨fun {a b} hab => ?_⟩
  · have h' : ((fun _ => (1 : ℂ) : M → ℂ) : (codiscrete M).Germ ℂ) = 0 :=
      congrArg Subtype.val h
    obtain ⟨x, hx⟩ :=
      ((coe_eq_zero_iff_eventually_eq_zero (meromorphicOn_const 1 _) x₀).1 h').exists
    exact one_ne_zero hx
  · obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have hfg : ((f * g : M → ℂ) : (codiscrete M).Germ ℂ) = 0 := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    rw [coe_eq_zero_iff_eventually_eq_zero (hf.mul hg) x₀] at hfg
    rcases (hf x₀ trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
    · left
      exact Subtype.ext (hfa ▸ (coe_eq_zero_iff_eventually_eq_zero hf x₀).2 h)
    rcases (hg x₀ trivial).eventually_eq_zero_or_eventually_ne_zero with h' | h'
    · right
      exact Subtype.ext (hgb ▸ (coe_eq_zero_iff_eventually_eq_zero hg x₀).2 h')
    obtain ⟨x, hx, hfx, hgx⟩ := (hfg.and (h.and h')).exists
    exact absurd hx (mul_ne_zero hfx hgx)

end RiemannSurface

/-- A property holding on a punctured neighbourhood of `u` in an open subset `U` holds on a
punctured neighbourhood of `u` in the ambient space. -/
theorem TopologicalSpace.Opens.eventually_nhdsNE_of_eventually_nhdsNE_subtype {X : Type*}
    [TopologicalSpace X] {U : Opens X} {u : U} {p : X → Prop}
    (h : ∀ᶠ z : U in 𝓝[≠] u, p z) : ∀ᶠ x in 𝓝[≠] (u : X), p x := by
  rw [nhdsWithin_subtype, eventually_comap] at h
  have hmem : (Subtype.val '' ({u}ᶜ : Set U)) ∈ 𝓝[≠] (u : X) := by
    refine mem_of_superset (inter_mem_nhdsWithin _ (U.isOpen.mem_nhds u.2)) ?_
    rintro x ⟨hxu, hxU⟩
    exact ⟨⟨x, hxU⟩, fun h => hxu (congrArg Subtype.val h), rfl⟩
  filter_upwards [nhdsWithin_le_of_mem hmem h, hmem] with x hx hxm
  obtain ⟨a, -, rfl⟩ := hxm
  exact hx a rfl

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {C : Scheme.{0}} {y : C ⟶ Spec (.of ℂ)}

/-- A curve over `ℂ` has a complex point: it is quasi-compact and nonempty, so it has a closed
point, and closed points are complex points. -/
theorem nonempty_of_isCurve [IsCurve ℂ y] : Nonempty (ComplexPoints y) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace y
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := C)).exists_closed_singleton Set.univ_nonempty
  exact ⟨closedPointsEquiv ⟨x, hx⟩⟩

/-! ### Analytification as a ring homomorphism to meromorphic germs -/

section Germ

variable [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C]

/-- **The analytification of rational functions**, as a ring homomorphism from the function field
to the germs of functions on `C(ℂ)` away from discrete closed sets. -/
noncomputable def analytifyRatGerm :
    C.functionField →+* (codiscrete (ComplexPoints y)).Germ ℂ where
  toFun g := (analytifyRat g : ComplexPoints y → ℂ)
  map_one' := by rw [analytifyRat_one]; rfl
  map_mul' g h := Germ.coe_eq.2 (analytifyRat_mul_eventuallyEq g h)
  map_zero' := by rw [analytifyRat_zero]; rfl
  map_add' g h := Germ.coe_eq.2 (analytifyRat_add_eventuallyEq g h)

theorem analytifyRatGerm_apply (g : C.functionField) :
    analytifyRatGerm g =
      ((analytifyRat g : ComplexPoints y → ℂ) : (codiscrete (ComplexPoints y)).Germ ℂ) :=
  rfl

theorem analytifyRatGerm_mem_meromorphicGerms (g : C.functionField) :
    analytifyRatGerm g ∈ RiemannSurface.meromorphicGerms (ComplexPoints y) :=
  RiemannSurface.coe_mem_meromorphicGerms (meromorphicOn_analytifyRat g _)

/-- **Uniqueness of the rational function with a given analytification**: two rational functions
whose analytifications agree away from a discrete closed set are equal. -/
theorem analytifyRat_injective {g h : C.functionField}
    (hgh : analytifyRat (y := y) g =ᶠ[codiscrete (ComplexPoints y)] analytifyRat h) : g = h := by
  obtain ⟨p⟩ := nonempty_of_isCurve (y := y)
  rw [← sub_eq_zero]
  refine eq_zero_of_analytifyRat_eventuallyEq_zero (p := p) ?_
  have h1 := (eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1
    (analytifyRat_sub_eventuallyEq (y := y) g h)) p
  have h2 := (eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hgh) p
  filter_upwards [h1, h2] with q hq1 hq2
  rw [hq1, Pi.sub_apply, hq2, sub_self]

end Germ


/-! ### Polynomials in a rational function `t` -/

/-- The embedding `ℂ[X] → K` sending `X` to `t`, through an embedding `ℂ(X) → K` sending `X` to
`t`. -/
noncomputable abbrev polynomialToFunctionField (C : Scheme.{0}) [IsIntegral C]
    [Algebra (RatFunc ℂ) C.functionField] : ℂ[X] →+* C.functionField :=
  (algebraMap (RatFunc ℂ) C.functionField).comp (algebraMap ℂ[X] (RatFunc ℂ))

section RatFunc

variable [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C]
  [Algebra (RatFunc ℂ) C.functionField] {t : C.functionField}

theorem analytifyRatGerm_polynomialToFunctionField
    (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) (P : ℂ[X]) :
    analytifyRatGerm (y := y) (polynomialToFunctionField C P) =
      ((fun x => P.eval (analytifyRat (y := y) t x) : ComplexPoints y → ℂ) :
        (codiscrete (ComplexPoints y)).Germ ℂ) := by
  let _ := functionFieldAlgebra ℂ y
  induction P using Polynomial.induction_on with
  | C c =>
    have : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c) = algebraMap ℂ (RatFunc ℂ) c := by
      rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (RatFunc ℂ), Polynomial.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [RingHom.comp_apply, this, hc, analytifyRatGerm_apply, analytifyRat_algebraMap]
    simp only [Polynomial.eval_C]
  | add P Q hP hQ =>
    rw [RingHom.map_add, RingHom.map_add, hP, hQ, ← Germ.coe_add]
    congr 1
    funext x
    simp only [Pi.add_apply, Polynomial.eval_add]
  | monomial n c h =>
    have e : (Polynomial.C c * Polynomial.X ^ (n + 1) : ℂ[X]) =
        Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by ring
    rw [e, RingHom.map_mul, RingHom.map_mul, h, RingHom.comp_apply, RatFunc.algebraMap_X, ht,
      analytifyRatGerm_apply, ← Germ.coe_mul]
    congr 1
    funext x
    simp only [Pi.mul_apply, Polynomial.eval_mul_X]

/-- The analytification of a polynomial expression `P(t, g)` is `P(t_an, g_an)`, as germs. -/
theorem eval₂_analytifyRatGerm_comp
    (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) (P : ℂ[X][X]) (f : ComplexPoints y → ℂ) :
    P.eval₂ ((analytifyRatGerm (y := y)).comp (polynomialToFunctionField C))
        (f : (codiscrete _).Germ ℂ) =
      ((fun x => (P.map (Polynomial.evalRingHom (analytifyRat (y := y) t x))).eval (f x) :
        ComplexPoints y → ℂ) : (codiscrete (ComplexPoints y)).Germ ℂ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval₂_add, hP, hQ, Polynomial.map_add, Polynomial.eval_add]
    rfl
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, RingHom.comp_apply,
      analytifyRatGerm_polynomialToFunctionField ht hc, ← Germ.coe_pow, ← Germ.coe_mul]
    congr 1
    funext x
    simp only [Pi.mul_apply, Pi.pow_apply, Polynomial.map_monomial, Polynomial.eval_monomial,
      Polynomial.coe_evalRingHom]

/-- If `P(t_an, f)` vanishes away from a discrete closed set, then `P(t, ·)` maps `f`, as a germ,
to zero. -/
theorem eval₂_analytifyRatGerm_comp_eq_zero
    (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) {P : ℂ[X][X]} {f : ComplexPoints y → ℂ}
    (hP : ∀ᶠ x in codiscrete (ComplexPoints y),
      (P.map (Polynomial.evalRingHom (analytifyRat (y := y) t x))).eval (f x) = 0) :
    P.eval₂ ((analytifyRatGerm (y := y)).comp (polynomialToFunctionField C))
      (f : (codiscrete _).Germ ℂ) = 0 := by
  rw [eval₂_analytifyRatGerm_comp ht hc]
  exact Germ.coe_eq.2 hP

/-- **A polynomial relation between analytifications is a relation in the function field**: if
`P(t_an, g_an)` vanishes on a punctured neighbourhood of a point, then `P(t, g) = 0`. -/
theorem eval_map_eq_zero_of_eventually
    (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) {P : ℂ[X][X]} {g : C.functionField}
    {p : ComplexPoints y}
    (hP : ∀ᶠ x in 𝓝[≠] p,
      (P.map (Polynomial.evalRingHom (analytifyRat (y := y) t x))).eval (analytifyRat g x) = 0) :
    (P.map (polynomialToFunctionField C)).eval g = 0 := by
  refine eq_zero_of_analytifyRat_eventuallyEq_zero (p := p) ?_
  have h1 : analytifyRatGerm (y := y) ((P.map (polynomialToFunctionField C)).eval g) =
      ((fun x => (P.map (Polynomial.evalRingHom (analytifyRat (y := y) t x))).eval
        (analytifyRat g x) : ComplexPoints y → ℂ) : (codiscrete (ComplexPoints y)).Germ ℂ) := by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, analytifyRatGerm_apply,
      eval₂_analytifyRatGerm_comp ht hc]
  have h2 := (eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 (Germ.coe_eq.1 h1)) p
  filter_upwards [h2, hP] with q hq1 hq2
  exact hq1.trans hq2

omit [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C] in
/-- `t` is not a constant. -/
theorem notMem_range_algebraMap_of_algebraMap_X_eq
    (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) :
    letI := functionFieldAlgebra ℂ y; t ∉ Set.range (algebraMap ℂ C.functionField) := by
  let _ := functionFieldAlgebra ℂ y
  rintro ⟨c, hct⟩
  rw [← hc c, ← ht] at hct
  have h := (algebraMap (RatFunc ℂ) C.functionField).injective hct
  rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (RatFunc ℂ), ← RatFunc.algebraMap_X] at h
  exact Polynomial.X_ne_C c ((IsFractionRing.injective ℂ[X] (RatFunc ℂ)) h).symm

end RatFunc

/-! ### Fibre degree of a rational function and degree of the function field -/

section FibreDegree

variable [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C]
  [CompactSpace (ComplexPoints y)] [Algebra (RatFunc ℂ) C.functionField] {t : C.functionField}

/-- **The degree `[K : ℂ(t)]` is at most the fibre degree of `t_an` on every nonempty clopen
set** `U`: the analytification of every `g ∈ K`, restricted to `U`, is a root of a polynomial over
`ℂ[t]` of degree the fibre degree of `t_an` on `U`, and this relation holds in `K`. -/
theorem finrank_le_fibreDegree (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c)
    (U : TopologicalSpace.Opens (ComplexPoints y)) (hU : IsClosed (U : Set (ComplexPoints y)))
    [Nonempty U] :
    Module.finrank (RatFunc ℂ) C.functionField ≤
      RiemannSurface.fibreDegree (fun z : U => analytifyRat (y := y) t z) := by
  have hnt := notMem_range_algebraMap_of_algebraMap_X_eq ht hc
  have : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  have htU : ∀ z : U, RiemannSurface.MeromorphicNFAt (fun z : U => analytifyRat (y := y) t z) z :=
    fun z => (RiemannSurface.meromorphicNFAt_subtype_iff U (f := analytifyRat (y := y) t)
      (x := z)).2 (meromorphicNFAt_analytifyRat t (z : ComplexPoints y))
  have hncU : ∀ (z : U) (c : ℂ),
      RiemannSurface.orderAt (fun w : U => analytifyRat (y := y) t w - c) z ≠ ⊤ := by
    intro z c
    rw [RiemannSurface.orderAt_subtype U (f := fun q => analytifyRat (y := y) t q - c) (x := z)]
    exact orderAt_analytifyRat_sub_const_ne_top hnt z c
  refine (Field.finiteDimensional_and_finrank_le_of_forall_aeval (F := RatFunc ℂ)
    (E := C.functionField) fun g => ?_).2
  have hfU : RiemannSurface.MeromorphicOn (fun z : U => analytifyRat (y := y) g z) Set.univ :=
    fun z _ => ((RiemannSurface.meromorphicNFAt_subtype_iff U (f := analytifyRat (y := y) g)
      (x := z)).2 (meromorphicNFAt_analytifyRat g (z : ComplexPoints y))).meromorphicAt
  obtain ⟨P, hPdeg, hPlc, hP⟩ := RiemannSurface.exists_polynomial_eval_eq_zero htU hncU hfU
  refine ⟨P.map (algebraMap ℂ[X] (RatFunc ℂ)), ?_, ?_, ?_⟩
  · rw [Ne, Polynomial.map_eq_zero_iff (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    rintro rfl
    exact hPlc (by simp)
  · exact (Polynomial.natDegree_map_le).trans hPdeg.le
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
    obtain ⟨u⟩ := ‹Nonempty U›
    refine eval_map_eq_zero_of_eventually ht hc (p := (u : ComplexPoints y)) ?_
    exact TopologicalSpace.Opens.eventually_nhdsNE_of_eventually_nhdsNE_subtype
      (p := fun x => (P.map (Polynomial.evalRingHom (analytifyRat (y := y) t x))).eval
        (analytifyRat g x) = 0)
      ((eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hP) u)

/-- **The fibre degree of `t_an` is at most `[K : ℂ(t)]`**: a generic fibre of `t_an` has
`fibreDegree` points and every regular fibre has at most `[K : ℂ(t)]` points. -/
theorem fibreDegree_le_finrank (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) :
    RiemannSurface.fibreDegree (analytifyRat (y := y) t) ≤
      Module.finrank (RatFunc ℂ) C.functionField := by
  have hnt := notMem_range_algebraMap_of_algebraMap_X_eq ht hc
  have htX : ∀ x, RiemannSurface.MeromorphicNFAt (analytifyRat (y := y) t) x :=
    meromorphicNFAt_analytifyRat t
  have hncX : ∀ (x : ComplexPoints y) (c : ℂ),
      RiemannSurface.orderAt (fun q => analytifyRat (y := y) t q - c) x ≠ ⊤ :=
    orderAt_analytifyRat_sub_const_ne_top hnt
  obtain ⟨b, hb⟩ := (RiemannSurface.finite_branchValues htX hncX).infinite_compl.nonempty
  rw [← RiemannSurface.ncard_regularFibre_eq_fibreDegree htX hncX hb]
  exact ncard_regularFibre_le_finrank ht hc b

/-- **The fibre degree of `t_an` is `[K : ℂ(t)]`.** -/
theorem fibreDegree_eq_finrank (ht : algebraMap (RatFunc ℂ) C.functionField RatFunc.X = t)
    (hc : ∀ c : ℂ, letI := functionFieldAlgebra ℂ y
      algebraMap (RatFunc ℂ) C.functionField (algebraMap ℂ (RatFunc ℂ) c) =
        algebraMap ℂ C.functionField c) :
    RiemannSurface.fibreDegree (analytifyRat (y := y) t) =
      Module.finrank (RatFunc ℂ) C.functionField := by
  refine le_antisymm (fibreDegree_le_finrank ht hc) ?_
  obtain ⟨p⟩ := nonempty_of_isCurve (y := y)
  have : Nonempty (⊤ : TopologicalSpace.Opens (ComplexPoints y)) := ⟨⟨p, trivial⟩⟩
  have hnt := notMem_range_algebraMap_of_algebraMap_X_eq ht hc
  have hU : IsClosed ((⊤ : TopologicalSpace.Opens (ComplexPoints y)) : Set (ComplexPoints y)) :=
    isClosed_univ
  have e := RiemannSurface.fibreDegree_add_fibreDegree_compl
    (U := (⊤ : TopologicalSpace.Opens (ComplexPoints y)))
    (meromorphicNFAt_analytifyRat t) (orderAt_analytifyRat_sub_const_ne_top hnt) hU
  have h1 := finrank_le_fibreDegree ht hc ⊤ hU
  omega

end FibreDegree

/-! ### Connectedness -/

section Connected

variable [IsCurve ℂ y]

omit [IsCurve ℂ y] in
theorem exists_transcendental_functionField [IsCurve ℂ y] :
    letI := functionFieldAlgebra ℂ y; ∃ t : C.functionField, Transcendental ℂ t := by
  let _ := functionFieldAlgebra ℂ y
  by_contra h
  have : Algebra.IsAlgebraic ℂ C.functionField := ⟨fun x => by
    by_contra hx
    exact h ⟨x, hx⟩⟩
  have h1 := trdeg_functionField_eq_one ℂ y
  rw [trdeg_eq_zero_iff.2 this] at h1
  exact zero_ne_one h1

variable [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C] [CompactSpace (ComplexPoints y)]

/-- **The complex points of a smooth curve over `ℂ` with compact analytic space form a connected
space.** Let `t` be transcendental, `D = [K : ℂ(t)]` and `d` the fibre degree of `t_an`. If
`C(ℂ) = U ⊔ V` with `U`, `V` nonempty and clopen, then `D` is at most the fibre degree of `t_an`
on `U` and on `V`, which add up to `d ≤ D`; this is impossible as `D ≥ 1`. -/
theorem connectedSpace : ConnectedSpace (ComplexPoints y) := by
  have hX := nonempty_of_isCurve (y := y)
  let _ := functionFieldAlgebra ℂ y
  obtain ⟨t, ht⟩ := exists_transcendental_functionField (y := y)
  obtain ⟨inst, htX, hc⟩ := exists_algebra_ratFunc ht
  let _ := inst
  have := finiteDimensional_ratFunc hc
  have hnt := notMem_range_algebraMap_of_algebraMap_X_eq htX hc
  suffices hpre : PreconnectedSpace (ComplexPoints y) from
    { toPreconnectedSpace := hpre, toNonempty := hX }
  refine preconnectedSpace_iff_clopen.2 fun s hs => ?_
  by_contra hne
  rw [not_or, ← Ne, ← Set.nonempty_iff_ne_empty, ← Ne, ← Set.nonempty_compl] at hne
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hne
  let U : TopologicalSpace.Opens (ComplexPoints y) := ⟨s, hs.isOpen⟩
  have hU : IsClosed (U : Set (ComplexPoints y)) := hs.isClosed
  have : Nonempty U := ⟨⟨a, ha⟩⟩
  have : Nonempty (⟨(U : Set (ComplexPoints y))ᶜ, hU.isOpen_compl⟩ :
    TopologicalSpace.Opens (ComplexPoints y)) := ⟨⟨b, hb⟩⟩
  have e := RiemannSurface.fibreDegree_add_fibreDegree_compl (U := U)
    (meromorphicNFAt_analytifyRat t) (orderAt_analytifyRat_sub_const_ne_top hnt) hU
  have h1 := finrank_le_fibreDegree htX hc U hU
  have h2 := finrank_le_fibreDegree htX hc ⟨(U : Set (ComplexPoints y))ᶜ, hU.isOpen_compl⟩
    hs.isOpen.isClosed_compl
  have h3 := fibreDegree_le_finrank htX hc
  have h4 := Module.finrank_pos (R := RatFunc ℂ) (M := C.functionField)
  omega

end Connected


/-! ### Meromorphic functions are rational -/

section Meromorphic

variable [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y] [IsLocallyNoetherian C]

/-- The analytification of rational functions, as a ring homomorphism to the meromorphic germs
on `C(ℂ)`. -/
noncomputable def analytifyRatMeromorphic :
    C.functionField →+* RiemannSurface.meromorphicGerms (ComplexPoints y) :=
  (analytifyRatGerm (y := y)).codRestrict _ analytifyRatGerm_mem_meromorphicGerms

theorem coe_analytifyRatMeromorphic (g : C.functionField) :
    (analytifyRatMeromorphic (y := y) g : (codiscrete (ComplexPoints y)).Germ ℂ) =
      ((analytifyRat g : ComplexPoints y → ℂ) : (codiscrete (ComplexPoints y)).Germ ℂ) :=
  rfl

theorem injective_analytifyRatMeromorphic :
    Function.Injective (analytifyRatMeromorphic (y := y)) := fun _ _ hgh =>
  analytifyRat_injective (Germ.coe_eq.1 (congrArg Subtype.val hgh))

variable [CompactSpace (ComplexPoints y)]

/-- **Every meromorphic germ on `C(ℂ)` is the analytification of a rational function.**

Let `t` be transcendental, `D = [K : ℂ(t)]` and `d` the fibre degree of `t_an`, so `d ≤ D`. The
meromorphic germs on the connected Riemann surface `C(ℂ)` form a domain `𝓜` in which every element
is a root of a polynomial of degree `d` over `ℂ[t]`. Hence `𝓜` is integral over `K`, so it is a
field, and by `Field.finiteDimensional_and_finrank_le_of_forall_aeval` it has degree at most `d`
over `ℂ(t)`. The `ℂ(t)`-linear injection `K → 𝓜` between spaces of dimension `D ≥ dim 𝓜` is
onto. -/
theorem surjective_analytifyRatMeromorphic :
    Function.Surjective (analytifyRatMeromorphic (y := y)) := by
  have := connectedSpace (y := y)
  have := RiemannSurface.isDomain_meromorphicGerms (M := ComplexPoints y)
  let _ := functionFieldAlgebra ℂ y
  obtain ⟨t, ht⟩ := exists_transcendental_functionField (y := y)
  obtain ⟨inst, htX, hc⟩ := exists_algebra_ratFunc ht
  let _ := inst
  have := finiteDimensional_ratFunc hc
  have hnt := notMem_range_algebraMap_of_algebraMap_X_eq htX hc
  have htT := meromorphicNFAt_analytifyRat (y := y) t
  have hncT := orderAt_analytifyRat_sub_const_ne_top hnt
  let A := RiemannSurface.meromorphicGerms (ComplexPoints y)
  let φ : C.functionField →+* A := analytifyRatMeromorphic
  have hψ : Function.Injective (polynomialToFunctionField C) :=
    (algebraMap (RatFunc ℂ) C.functionField).injective.comp
      (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
  have key : ∀ a : A, ∃ P : ℂ[X][X],
      P.natDegree = RiemannSurface.fibreDegree (analytifyRat (y := y) t) ∧ P.leadingCoeff ≠ 0 ∧
        P.eval₂ (φ.comp (polynomialToFunctionField C)) a = 0 := by
    rintro ⟨_, f, hf, rfl⟩
    obtain ⟨P, hPdeg, hPlc, hP⟩ := RiemannSurface.exists_polynomial_eval_eq_zero htT hncT hf
    refine ⟨P, hPdeg, hPlc, Subtype.ext ?_⟩
    have h := Polynomial.hom_eval₂ P (φ.comp (polynomialToFunctionField C)) A.subtype
      ⟨_, f, hf, rfl⟩
    change A.subtype _ = A.subtype 0
    rw [h, map_zero]
    exact eval₂_analytifyRatGerm_comp_eq_zero htX hc hP
  let _ : Algebra C.functionField A := φ.toAlgebra
  have hint : Algebra.IsIntegral C.functionField A := ⟨fun a => by
    obtain ⟨P, -, hPlc, hP⟩ := key a
    refine IsAlgebraic.isIntegral ⟨P.map (polynomialToFunctionField C), fun h => hPlc ?_, ?_⟩
    · have h' := congrArg Polynomial.leadingCoeff h
      rw [Polynomial.leadingCoeff_map_of_injective hψ, Polynomial.leadingCoeff_zero] at h'
      exact hψ (h'.trans (RingHom.map_zero _).symm)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      exact hP⟩
  have hfield : IsField A :=
    (Algebra.IsIntegral.isField_iff_isField φ.injective).1 (Field.toIsField _)
  let _ : Field A := hfield.toField
  let _ : Algebra (RatFunc ℂ) A := (φ.comp (algebraMap (RatFunc ℂ) C.functionField)).toAlgebra
  obtain ⟨hfinA, hrkA⟩ := Field.finiteDimensional_and_finrank_le_of_forall_aeval
    (F := RatFunc ℂ) (E := A) (d := RiemannSurface.fibreDegree (analytifyRat (y := y) t))
    fun a => by
      obtain ⟨P, hPdeg, hPlc, hP⟩ := key a
      refine ⟨P.map (algebraMap ℂ[X] (RatFunc ℂ)), ?_,
        (Polynomial.natDegree_map_le).trans hPdeg.le, ?_⟩
      · rw [Ne, Polynomial.map_eq_zero_iff (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
        rintro rfl
        exact hPlc (by simp)
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        exact hP
  let L : C.functionField →ₐ[RatFunc ℂ] A := { φ with commutes' := fun _ => rfl }
  have hL : Function.Injective L.toLinearMap := φ.injective
  have heq : Module.finrank (RatFunc ℂ) C.functionField = Module.finrank (RatFunc ℂ) A :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hL)
      (hrkA.trans (fibreDegree_le_finrank htX hc))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hL

/-- **Every meromorphic function on `C(ℂ)` is rational** (GAGA for functions on a curve): it
agrees with the analytification of a rational function away from a discrete closed set. The
rational function is unique by `analytifyRat_injective`. -/
theorem exists_eq_analytifyRat {f : ComplexPoints y → ℂ}
    (hf : RiemannSurface.MeromorphicOn f Set.univ) :
    ∃ g : C.functionField, f =ᶠ[codiscrete (ComplexPoints y)] analytifyRat g := by
  obtain ⟨g, hg⟩ := surjective_analytifyRatMeromorphic (y := y)
    ⟨_, RiemannSurface.coe_mem_meromorphicGerms hf⟩
  exact ⟨g, (Germ.coe_eq.1 (congrArg Subtype.val hg)).symm⟩

/-- The function field of `C` is the field of meromorphic germs on `C(ℂ)`. -/
noncomputable def functionFieldEquivMeromorphicGerms :
    C.functionField ≃+* RiemannSurface.meromorphicGerms (ComplexPoints y) :=
  RingEquiv.ofBijective analytifyRatMeromorphic
    ⟨injective_analytifyRatMeromorphic, surjective_analytifyRatMeromorphic⟩

end Meromorphic

/-! ### Regular functions are the holomorphic functions -/

section GlobalSections

theorem mdifferentiable_evalOrZero_top [SmoothOfRelativeDimension 1 y] (s : Γ(C, ⊤)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (evalOrZero (z := y) ⊤ s) := fun x =>
  (mdifferentiableOn_evalOrZero ⊤ s x (mem_top x)).mdifferentiableAt
    ((isOpen_setOf_mem ⊤).mem_nhds (mem_top x))

/-- A regular function on a curve is determined by its values at the complex points. -/
theorem injective_evalOrZero_top [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]
    [IsLocallyNoetherian C] : Function.Injective (evalOrZero (z := y) ⊤) := by
  intro s s' h
  obtain ⟨p⟩ := nonempty_of_isCurve (y := y)
  have : Nonempty (⊤ : C.Opens) := ⟨⟨p.toPoint, trivial⟩⟩
  apply C.germToFunctionField_injective ⊤
  apply analytifyRat_injective (y := y)
  refine Eventually.of_forall fun q => ?_
  rw [eqOn_analytifyRat_germToFunctionField s (mem_top q),
    eqOn_analytifyRat_germToFunctionField s' (mem_top q), h]

/-- **GAGA for global functions on a curve**: the regular functions on `C` are exactly the
holomorphic functions on `C(ℂ)`. A holomorphic function on the compact connected Riemann surface
`C(ℂ)` is constant, hence the value of a constant regular function; a regular function vanishing on
`C(ℂ)` is zero. -/
theorem bijective_evalOrZero_top [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]
    [IsLocallyNoetherian C] [CompactSpace (ComplexPoints y)] :
    Function.Bijective (fun s : Γ(C, ⊤) =>
      (⟨evalOrZero ⊤ s, mdifferentiable_evalOrZero_top s⟩ :
        {f : ComplexPoints y → ℂ // MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f})) := by
  refine ⟨fun s s' h => injective_evalOrZero_top (congrArg Subtype.val h), fun ⟨f, hf⟩ => ?_⟩
  have := connectedSpace (y := y)
  obtain ⟨c, rfl⟩ := hf.exists_eq_const_of_compactSpace
  refine ⟨constHom (y := y) ⊤ c, Subtype.ext (funext fun q => ?_)⟩
  simp only [evalOrZero_of_mem _ (mem_top q), eval_constHom, Function.const_apply]

/-- A regular function on `C` as a global section of the sheaf of holomorphic functions on the
Riemann surface `C(ℂ)`. -/
noncomputable def globalSectionsToHolomorphic [SmoothOfRelativeDimension 1 y] (s : Γ(C, ⊤)) :
    (ComplexManifold.holomorphicSheaf 𝓘(ℂ) (ComplexPoints y)).presheaf.obj (op ⊤) :=
  ⟨fun x => evalOrZero ⊤ s x.1,
    (RiemannSurface.contMDiff_iff_mdifferentiable.2 (mdifferentiable_evalOrZero_top s)).comp
      contMDiff_subtype_val⟩

/-- **GAGA for global functions on a curve, sheaf form**: `s ↦ s_an` is a bijection from the
regular functions on `C` to the global sections of the sheaf of holomorphic functions on `C(ℂ)`. -/
theorem bijective_globalSectionsToHolomorphic [IsCurve ℂ y] [SmoothOfRelativeDimension 1 y]
    [IsLocallyNoetherian C] [CompactSpace (ComplexPoints y)] :
    Function.Bijective (globalSectionsToHolomorphic (y := y)) := by
  refine ⟨fun s s' h => injective_evalOrZero_top (y := y) (funext fun q => ?_), fun σ => ?_⟩
  · exact congrArg (fun σ => σ.1 ⟨q, trivial⟩) h
  · have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun q : ComplexPoints y => σ.1 ⟨q, trivial⟩) :=
      fun q => (RiemannSurface.mdifferentiableAt_subtype_iff
        (⊤ : TopologicalSpace.Opens (ComplexPoints y))
        (f := fun q : ComplexPoints y => σ.1 ⟨q, trivial⟩) (x := ⟨q, trivial⟩)).1
          (ContMDiff.mdifferentiable (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) σ.2 (by simp) _)
    obtain ⟨s, hs⟩ := (bijective_evalOrZero_top (y := y)).2 ⟨_, hf⟩
    refine ⟨s, Subtype.ext (funext fun x => ?_)⟩
    exact congrFun (congrArg Subtype.val hs) x.1

end GlobalSections

end AlgebraicGeometry.Scheme.ComplexPoints
