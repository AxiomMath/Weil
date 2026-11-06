module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Topology.IsLocalHomeomorph
public import Weil.AlgebraicGeometry.ComplexPoints.Functoriality

/-!
# Étale morphisms are local homeomorphisms on complex points

Let `f : Y' ⟶ Y` be an étale morphism of schemes over `ℂ`, and give the complex points the
analytic topology. Locally on `Y'`, `f` is standard étale: for affine opens `U ⊆ Y`,
`U' ⊆ f⁻¹ U` and a complex point `p ∈ U'(ℂ)` there is `b ∈ Γ(Y', U')` with `b(p) ≠ 0` and
`Γ(Y', U')[1/b] ≅ Γ(Y, U)[x][1/g(x)]/(P(x))` with `P` monic and `P'(x)` invertible. The complex
points of `D(b) ⊆ U'` are then the pairs `(a, t)` with `a ∈ U(ℂ)`, `P_a(t) = 0` and `g_a(t) ≠ 0`,
where `P_a`, `g_a` are the polynomials with coefficients evaluated at `a`. Writing the
coefficients as polynomials in the coordinates `s_i(a)` of a presentation of `Γ(Y, U)`,
`P_a(t) = F(s(a), t)` for a polynomial function `F` on `ℂ^ι × ℂ` with `∂F/∂t ≠ 0` at
`(s(f(p)), x(p))`. The holomorphic implicit function theorem gives a holomorphic root
`t = ψ(c)` near `s(f(p))`, unique near `x(p)`; this is a local inverse of `f`, continuous because
every regular function on `U'` is a rational function of the coordinates of the image and of `x`.

Consequently `f` induces a local homeomorphism `Y'(ℂ) → Y(ℂ)` when `Y` is locally of finite type
over `ℂ`, every regular function on `Y'` is locally a holomorphic function of the coordinates of
`Y`, and the fibres of `Y'(ℂ) → Y(ℂ)` are discrete. Independently of étaleness, a family of
morphisms that is jointly surjective on underlying points, from schemes locally of finite type
over `ℂ`, is jointly surjective on complex points, by Hilbert's Nullstellensatz.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.exists_openPartialHomeomorph_of_etale`: étale charts:
  for `f` étale, affine opens `U`, `U' ⊆ f⁻¹ U`, a finite presentation `s` of `Γ(Y, U)` and
  `p ∈ U'(ℂ)`, an open partial homeomorphism around `p` restricting `f`, whose target is cut out
  by an open `W ⊆ ℂ^ι` in the coordinates `s`, such that every `g ∈ Γ(Y', U')` equals `G ∘ s ∘ f`
  on its source for some `G` complex differentiable on `W`.
* `AlgebraicGeometry.Scheme.ComplexPoints.isLocalHomeomorph_map_of_etale`: an étale morphism
  over `ℂ`, with target locally of finite type, is a local homeomorphism on complex points.
* `AlgebraicGeometry.Scheme.ComplexPoints.discreteTopology_fiber_of_etale`: its fibres on complex
  points are discrete.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_map_eq_of_jointlySurjective`: jointly surjective
  families of morphisms from schemes locally of finite type over `ℂ` are jointly surjective on
  complex points; `exists_map_eq_of_jointlySurjective_of_etale` is the étale case.
* `AlgebraicGeometry.Scheme.ComplexPoints.nonempty_of_locallyOfFiniteType`: a nonempty scheme
  locally of finite type over `ℂ` has a complex point.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_implicitFunction`: the holomorphic implicit
  function theorem for one equation in one unknown, with parameters.

## Implementation notes

The holomorphy of the local inverses is stated in coordinates: the local inverse composed with
a regular function of `U'` is `G ∘ s` with `G : ℂ^ι → ℂ` complex differentiable on an open
`W ⊆ ℂ^ι`, the analytic topology of `U(ℂ)` being induced by the closed embedding
`s : U(ℂ) → ℂ^ι`. Complex differentiability (`DifferentiableOn ℂ`) is used rather than
analyticity, as several-variable Hartogs-type results are not needed downstream. Functions defined
only on `V(ℂ)` are extended by `0` (`evalOrZero`, `coordsOrZero`) so that continuity on open
sets can be stated with `ContinuousOn`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
* [SGA1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exposé XII, §3.
* [Stacks] The Stacks Project, Tag 00UE (étale ring maps are locally standard étale).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Filter

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### The holomorphic implicit function theorem in one variable -/

section Implicit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Holomorphic implicit function theorem**, for one equation in one unknown with parameters.
If `F : E × ℂ → ℂ` is `C¹` over `ℂ`, `F (c₀, t₀) = 0` and `∂F/∂t (c₀, t₀) ≠ 0`, then near `c₀` the
equation `F (c, t) = 0`, `t` near `t₀`, has exactly one solution `t = ψ c`, and `ψ` is complex
differentiable. The graph of `ψ` can moreover be kept inside any given neighbourhood `O` of
`(c₀, t₀)`. -/
theorem exists_implicitFunction {F : E × ℂ → ℂ} (hF : ContDiff ℂ 1 F) {c₀ : E} {t₀ : ℂ}
    (h0 : F (c₀, t₀) = 0) (hd : deriv (fun t => F (c₀, t)) t₀ ≠ 0) {O : Set (E × ℂ)}
    (hO : IsOpen O) (hu : (c₀, t₀) ∈ O) :
    ∃ (W : Set E) (D : Set ℂ) (ψ : E → ℂ), IsOpen W ∧ c₀ ∈ W ∧ IsOpen D ∧ t₀ ∈ D ∧
      ψ c₀ = t₀ ∧
      (∀ c ∈ W, ψ c ∈ D ∧ F (c, ψ c) = 0 ∧ (c, ψ c) ∈ O ∧ DifferentiableAt ℂ ψ c) ∧
      ∀ c ∈ W, ∀ t ∈ D, F (c, t) = 0 → t = ψ c := by
  set u : E × ℂ := (c₀, t₀)
  have cdf : ContDiffAt ℂ 1 F u := hF.contDiffAt
  have pn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hFd : HasFDerivAt F (fderiv ℂ F u) u :=
    (hF.differentiable (by simp) u).hasFDerivAt
  have hcomp : HasFDerivAt (fun t => F (c₀, t)) (fderiv ℂ F u ∘L .inr ℂ E ℂ) t₀ :=
    hFd.comp t₀ (hasFDerivAt_prodMk_right c₀ t₀)
  have hL1 : (fderiv ℂ F u ∘L .inr ℂ E ℂ) 1 = deriv (fun t => F (c₀, t)) t₀ :=
    hcomp.hasDerivAt.deriv.symm
  have if₂ : (fderiv ℂ F u ∘L .inr ℂ E ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hd), ?_⟩
    apply ContinuousLinearMap.ext_ring
    rw [hL1]
    simp [ContinuousLinearEquiv.unitsEquivAut]
  set ψ := cdf.implicitFunction pn if₂
  have hψ0 : ψ c₀ = t₀ := cdf.implicitFunction_apply_self pn if₂
  have E1 : ∀ᶠ x in 𝓝 c₀, F (x, ψ x) = F u := cdf.eventually_apply_implicitFunction pn if₂
  have E2 : ∀ᶠ v in 𝓝 u, F v = F u ↔ ψ v.1 = v.2 :=
    cdf.eventually_apply_eq_iff_implicitFunction pn if₂
  have E3 : ∀ᶠ x in 𝓝 c₀, ContDiffAt ℂ 1 ψ x :=
    (cdf.contDiffAt_implicitFunction pn if₂).eventually (by simp)
  have hψc : ContinuousAt ψ c₀ := (cdf.contDiffAt_implicitFunction pn if₂).continuousAt
  have hgraph : Tendsto (fun x => (x, ψ x)) (𝓝 c₀) (𝓝 u) := by
    have := (continuousAt_id.prodMk hψc).tendsto
    simpa [u, hψ0] using this
  have E4 : ∀ᶠ x in 𝓝 c₀, (x, ψ x) ∈ O := hgraph (hO.mem_nhds hu)
  obtain ⟨W₂, D, hW₂, hcW₂, hD, htD, hWD⟩ := mem_nhds_prod_iff'.1 E2
  have E5 : ∀ᶠ x in 𝓝 c₀, ψ x ∈ D := by
    have := hψc.tendsto
    rw [hψ0] at this
    exact this (hD.mem_nhds htD)
  have E6 : ∀ᶠ x in 𝓝 c₀, x ∈ W₂ := hW₂.mem_nhds hcW₂
  obtain ⟨W, hWsub, hW, hcW⟩ := mem_nhds_iff.1 (E1.and (E3.and (E4.and (E5.and E6))))
  refine ⟨W, D, ψ, hW, hcW, hD, htD, hψ0, fun c hc => ?_, fun c hc t ht hFt => ?_⟩
  · obtain ⟨h1, h3, h4, h5, -⟩ := hWsub hc
    refine ⟨h5, ?_, h4, h3.differentiableAt (by simp)⟩
    rw [h1, h0]
  · have := hWD (Set.mk_mem_prod (hWsub hc).2.2.2.2 ht)
    exact ((this.1 (by rw [hFt, h0])).symm)

end Implicit

/-! ### Polynomial functions on `ℂ^ι × ℂ` -/

section PolyFun

variable {ι : Type*}

/-- The function `(c, t) ↦ F(c)(t)` on `ℂ^ι × ℂ` attached to a polynomial in one variable `t`
with coefficients polynomials in `c`. -/
noncomputable def polyFun (F : Polynomial (MvPolynomial ι ℂ)) : (ι → ℂ) × ℂ → ℂ :=
  fun z => (F.map (MvPolynomial.eval z.1)).eval z.2

theorem deriv_polyFun (F : Polynomial (MvPolynomial ι ℂ)) (c : ι → ℂ) (t : ℂ) :
    deriv (fun t => polyFun F (c, t)) t = polyFun (Polynomial.derivative F) (c, t) := by
  simp only [polyFun, Polynomial.deriv, Polynomial.derivative_map]

variable [Fintype ι]

theorem contDiff_mvPolynomial_eval (P : MvPolynomial ι ℂ) {n : WithTop ℕ∞} :
    ContDiff ℂ n fun x : ι → ℂ => MvPolynomial.eval x P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℂ ℂ i)

theorem contDiff_polyFun (F : Polynomial (MvPolynomial ι ℂ)) {n : WithTop ℕ∞} :
    ContDiff ℂ n (polyFun F) := by
  have : polyFun F = fun z : (ι → ℂ) × ℂ =>
      ∑ k ∈ F.support, MvPolynomial.eval z.1 (F.coeff k) * z.2 ^ k := by
    funext z
    simp only [polyFun, Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [this]
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_mvPolynomial_eval _).comp contDiff_fst).mul (contDiff_snd.pow k)

end PolyFun

theorem continuous_polyFun {ι : Type*} [Finite ι] (F : Polynomial (MvPolynomial ι ℂ)) :
    Continuous (polyFun F) := by
  have := Fintype.ofFinite ι
  exact (contDiff_polyFun F (n := 0)).continuous

/-! ### Total versions of evaluation and coordinates -/

section Total

variable {Z : Scheme.{0}} {z : Z ⟶ Spec (.of ℂ)}

/-- The value `g(q)` of `g ∈ Γ(Z, V)` at `q ∈ V(ℂ)`, extended by `0` outside `V(ℂ)`. -/
noncomputable def evalOrZero (V : Z.Opens) (g : Γ(Z, V)) (q : ComplexPoints z) : ℂ :=
  open Classical in if h : q.Mem V then eval g q h else 0

theorem evalOrZero_of_mem {V : Z.Opens} (g : Γ(Z, V)) {q : ComplexPoints z} (h : q.Mem V) :
    evalOrZero V g q = eval g q h := by
  simp [evalOrZero, h]

theorem continuousOn_evalOrZero (V : Z.Opens) (g : Γ(Z, V)) :
    ContinuousOn (evalOrZero V g) {q : ComplexPoints z | q.Mem V} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_eval_of_isOpen V g).congr fun q => (evalOrZero_of_mem g q.2).symm

/-- The coordinates `q ↦ (s_i(q))_i`, extended by `0` outside `V(ℂ)`. -/
noncomputable def coordsOrZero {V : Z.Opens} {ι : Type*} (s : ι → Γ(Z, V)) (q : ComplexPoints z) :
    ι → ℂ :=
  fun i => evalOrZero V (s i) q

theorem coordsOrZero_of_mem {V : Z.Opens} {ι : Type*} (s : ι → Γ(Z, V)) {q : ComplexPoints z}
    (h : q.Mem V) : coordsOrZero s q = coords z s ⟨q, h⟩ :=
  funext fun i => evalOrZero_of_mem (s i) h

theorem continuousOn_coordsOrZero {V : Z.Opens} {ι : Type*} (s : ι → Γ(Z, V)) :
    ContinuousOn (coordsOrZero s) {q : ComplexPoints z | q.Mem V} :=
  continuousOn_pi.2 fun i => continuousOn_evalOrZero V (s i)

/-- Evaluating a polynomial with coefficients lifted along a presentation. -/
theorem eval₂_map_presentationHom {V : Z.Opens} {ι : Type*} (s : ι → Γ(Z, V))
    (F : Polynomial (MvPolynomial ι ℂ)) {q : ComplexPoints z} (h : q.Mem V) (t : ℂ) :
    (F.map (presentationHom z s)).eval₂ (evalHom q h) t = polyFun F (coords z s ⟨q, h⟩, t) := by
  have : (evalHom q h).comp (presentationHom z s) = MvPolynomial.eval (coords z s ⟨q, h⟩) :=
    RingHom.ext fun P => eval_presentationHom s P q h
  rw [Polynomial.eval₂_map, this, polyFun, Polynomial.eval_map]

end Total

/-! ### Morphisms and regular functions -/

section Morphism

variable {Y Y' : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} {y' : Y' ⟶ Spec (.of ℂ)} (f : Y' ⟶ Y)
  (hf : f ≫ y = y')

/-- The value of the pullback `f^* r ∈ Γ(Y', U')` at `q` is the value of `r` at `f(q)`. -/
theorem eval_appLE {U : Y.Opens} {U' : Y'.Opens} (e : U' ≤ f ⁻¹ᵁ U) (r : Γ(Y, U))
    (q : ComplexPoints y') (hq : q.Mem U') :
    eval (f.appLE U U' e r) q hq = eval r (map f hf q) ((map_mem_iff f hf q U).2 (hq.mono e)) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, eval_map e, eval_map_point]

include hf in
/-- Pullback along a morphism over `ℂ` preserves constants. -/
theorem appLE_constHom {U : Y.Opens} {U' : Y'.Opens} (e : U' ≤ f ⁻¹ᵁ U) (c : ℂ) :
    f.appLE U U' e (constHom (y := y) U c) = constHom (y := y') U' c := by
  subst hf
  simp only [constHom]
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE]

end Morphism

/-! ### The local structure of an étale morphism on complex points -/

section Etale

variable {Y Y' : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} {y' : Y' ⟶ Spec (.of ℂ)} (f : Y' ⟶ Y)
  (hf : f ≫ y = y')

/-- **Étale charts on complex points.** Let `f : Y' ⟶ Y` be étale over `ℂ`, `U ⊆ Y` and
`U' ⊆ f⁻¹ U` affine opens, `s : ι → Γ(Y, U)` (`ι` finite) generators of `Γ(Y, U)` over `ℂ`, and
`p ∈ U'(ℂ)`. Then `f` restricts to a homeomorphism `φ` from an open neighbourhood of `p` in
`U'(ℂ)` onto the open set of the points of `U(ℂ)` whose coordinates lie in an open set
`W ⊆ ℂ^ι`, and every regular function `g` on `U'` is, on the source of `φ`, a holomorphic function
on `W` of the coordinates of the image point: `g = G ∘ s ∘ f`. -/
theorem exists_openPartialHomeomorph_of_etale [Etale f] {U : Y.Opens} (hU : IsAffineOpen U)
    {ι : Type*} [Finite ι] {s : ι → Γ(Y, U)} (hs : Function.Surjective (presentationHom y s))
    {U' : Y'.Opens} (hU' : IsAffineOpen U') (e : U' ≤ f ⁻¹ᵁ U) (p : ComplexPoints y')
    (hp : p.Mem U') :
    ∃ (φ : OpenPartialHomeomorph (ComplexPoints y') (ComplexPoints y)) (W : Set (ι → ℂ)),
      p ∈ φ.source ∧ ⇑φ = map f hf ∧ IsOpen W ∧ (∀ q ∈ φ.source, q.Mem U') ∧
      φ.target = {a | ∃ ha : a.Mem U, coords y s ⟨a, ha⟩ ∈ W} ∧
      ∀ g : Γ(Y', U'), ∃ G : (ι → ℂ) → ℂ, DifferentiableOn ℂ G W ∧
        ∀ q ∈ φ.source, ∀ (hq : q.Mem U') (ha : (map f hf q).Mem U),
          eval g q hq = G (coords y s ⟨map f hf q, ha⟩) := by
  classical
  have := Fintype.ofFinite ι
  -- The étale algebra `Γ(Y, U) → Γ(Y', U')` and a standard étale localization at `p`.
  let _ : Algebra Γ(Y, U) Γ(Y', U') := (f.appLE U U' e).hom.toAlgebra
  have : Algebra.Etale Γ(Y, U) Γ(Y', U') := Etale.etale_appLE f hU hU' e
  have halg : ∀ r, algebraMap Γ(Y, U) Γ(Y', U') r = f.appLE U U' e r := fun _ => rfl
  have hmemU : ∀ q : ComplexPoints y', q.Mem U' → (map f hf q).Mem U :=
    fun q hq => (map_mem_iff f hf q U).2 (hq.mono e)
  have : (RingHom.ker (evalHom p hp)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨b, hbQ, hstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := Γ(Y, U)) (RingHom.ker (evalHom p hp))
  have hb : eval b p hp ≠ 0 := by simpa [RingHom.mem_ker] using hbQ
  let T := Localization.Away b
  let P : StandardEtalePresentation Γ(Y, U) T := hstd.nonempty_standardEtalePresentation.some
  obtain ⟨k, c, hxc⟩ := IsLocalization.Away.surj (S := T) b P.x
  -- The extension `χ_q : T → ℂ` of the evaluation at a point `q` with `b(q) ≠ 0`.
  let chi : ∀ (q : ComplexPoints y') (hq : q.Mem U'), eval b q hq ≠ 0 → (T →+* ℂ) :=
    fun q hq hbq => IsLocalization.Away.lift (S := T) b (g := evalHom q hq) (Ne.isUnit hbq)
  have chi_B : ∀ q hq hbq (g : Γ(Y', U')), chi q hq hbq (algebraMap _ T g) = eval g q hq :=
    fun q hq hbq g => IsLocalization.Away.lift_eq b _ g
  have chi_A : ∀ q hq hbq (r : Γ(Y, U)),
      chi q hq hbq (algebraMap _ T r) = eval r (map f hf q) (hmemU q hq) := by
    intro q hq hbq r
    rw [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(Y', U') T, chi_B q hq hbq, halg, eval_appLE f hf e]
  have chi_A' : ∀ q hq hbq,
      (chi q hq hbq).comp (algebraMap Γ(Y, U) T) = evalHom (map f hf q) (hmemU q hq) :=
    fun q hq hbq => RingHom.ext (chi_A q hq hbq)
  have chi_x : ∀ q hq hbq, chi q hq hbq P.x = eval c q hq / eval b q hq ^ k := by
    intro q hq hbq
    have h := congrArg (chi q hq hbq) hxc
    rw [map_mul, map_pow, chi_B q hq hbq, chi_B q hq hbq] at h
    exact eq_div_of_mul_eq (pow_ne_zero _ hbq) h
  -- Lifts of the standard étale polynomials to `ℂ[ι][X]`.
  obtain ⟨Ft, hFt⟩ := Polynomial.map_surjective _ hs P.f
  obtain ⟨Gt, hGt⟩ := Polynomial.map_surjective _ hs P.g
  have chi_aeval : ∀ q hq hbq (pt : Polynomial (MvPolynomial ι ℂ)),
      chi q hq hbq (Polynomial.aeval P.x (pt.map (presentationHom y s))) =
        polyFun pt (coords y s ⟨map f hf q, hmemU q hq⟩, chi q hq hbq P.x) := by
    intro q hq hbq pt
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, chi_A' q hq hbq, eval₂_map_presentationHom]
  -- The implicit function at `p`.
  set c₀ := coords y s ⟨map f hf p, hmemU p hp⟩
  set t₀ := chi p hp hb P.x
  have hF0 : polyFun Ft (c₀, t₀) = 0 := by
    rw [← chi_aeval p hp hb, hFt, P.hasMap.1, map_zero]
  have hFd : deriv (fun t => polyFun Ft (c₀, t)) t₀ ≠ 0 := by
    rw [deriv_polyFun, ← chi_aeval p hp hb, ← Polynomial.derivative_map, hFt]
    exact (P.hasMap.isUnit_derivative_f.map (chi p hp hb)).ne_zero
  have hG0 : polyFun Gt (c₀, t₀) ≠ 0 := by
    rw [← chi_aeval p hp hb, hGt]
    exact (P.hasMap.2.map (chi p hp hb)).ne_zero
  obtain ⟨W, D, ψ, hW, hc₀W, hD, ht₀D, hψ₀, hψW, huniq⟩ :=
    exists_implicitFunction (contDiff_polyFun Ft) hF0 hFd
      (isOpen_compl_singleton.preimage (continuous_polyFun Gt)) hG0
  -- The source and the target of the chart.
  let tT : ComplexPoints y' → ℂ := fun q => evalOrZero U' c q / evalOrZero U' b q ^ k
  let src : Set (ComplexPoints y') := {q | q.Mem U' ∧ evalOrZero U' b q ≠ 0 ∧
      coordsOrZero s (map f hf q) ∈ W ∧ tT q ∈ D}
  let tgt : Set (ComplexPoints y) := {a | a.Mem U ∧ coordsOrZero s a ∈ W}
  have tT_eq : ∀ q hq hbq, tT q = chi q hq hbq P.x := by
    intro q hq hbq
    simp only [tT, evalOrZero_of_mem _ hq, chi_x q hq hbq]
  have src_mem : ∀ q ∈ src, ∃ (hq : q.Mem U') (hbq : eval b q hq ≠ 0),
      coords y s ⟨map f hf q, hmemU q hq⟩ ∈ W ∧ chi q hq hbq P.x ∈ D := by
    rintro q ⟨hq, hbq, hW', hD'⟩
    rw [evalOrZero_of_mem _ hq] at hbq
    refine ⟨hq, hbq, ?_, ?_⟩
    · rwa [coordsOrZero_of_mem s (hmemU q hq)] at hW'
    · rwa [tT_eq q hq hbq] at hD'
  -- On the source, the value of `x` is the implicit function of the coordinates of the image.
  have src_x : ∀ q (hq : q.Mem U') (hbq : eval b q hq ≠ 0),
      coords y s ⟨map f hf q, hmemU q hq⟩ ∈ W → chi q hq hbq P.x ∈ D →
        chi q hq hbq P.x = ψ (coords y s ⟨map f hf q, hmemU q hq⟩) := by
    intro q hq hbq hW' hD'
    refine huniq _ hW' _ hD' ?_
    rw [← chi_aeval q hq hbq, hFt, P.hasMap.1, map_zero]
  -- Every regular function on `U'` is a rational function of the coordinates and of `x`.
  have hrep : ∀ g : Γ(Y', U'), ∃ (pt : Polynomial (MvPolynomial ι ℂ)) (n : ℕ),
      algebraMap _ T g * Polynomial.aeval P.x P.g ^ n =
        Polynomial.aeval P.x (pt.map (presentationHom y s)) := by
    intro g
    obtain ⟨pp, n, h⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x (algebraMap _ T g)
    obtain ⟨pt, rfl⟩ := Polynomial.map_surjective _ hs pp
    exact ⟨pt, n, h⟩
  choose pt n hpt using hrep
  let Gfun : Γ(Y', U') → (ι → ℂ) → ℂ := fun g c' =>
    polyFun (pt g) (c', ψ c') / polyFun Gt (c', ψ c') ^ n g
  have hGne : ∀ c' ∈ W, polyFun Gt (c', ψ c') ≠ 0 := fun c' hc' => (hψW c' hc').2.2.1
  have eval_eq : ∀ g q (hq : q.Mem U') (hbq : eval b q hq ≠ 0),
      coords y s ⟨map f hf q, hmemU q hq⟩ ∈ W → chi q hq hbq P.x ∈ D →
        eval g q hq = Gfun g (coords y s ⟨map f hf q, hmemU q hq⟩) := by
    intro g q hq hbq hW' hD'
    have h := congrArg (chi q hq hbq) (hpt g)
    rw [← hGt, map_mul, map_pow, chi_B q hq hbq, chi_aeval q hq hbq, chi_aeval q hq hbq,
      src_x q hq hbq hW' hD'] at h
    exact eq_div_of_mul_eq (pow_ne_zero _ (hGne _ hW')) h
  -- Injectivity on the source.
  have injOn : Set.InjOn (map f hf) src := by
    intro q hqs q' hq's hqq
    obtain ⟨hq, hbq, hW', hD'⟩ := src_mem q hqs
    obtain ⟨hq', hbq', hW'', hD''⟩ := src_mem q' hq's
    refine eq_of_eval_eq hU' hq hq' fun g => ?_
    rw [eval_eq g q hq hbq hW' hD', eval_eq g q' hq' hbq' hW'' hD'']
    have : (⟨map f hf q, hmemU q hq⟩ : {a : ComplexPoints y // a.Mem U}) =
        ⟨map f hf q', hmemU q' hq'⟩ := Subtype.ext hqq
    rw [this]
  -- Surjectivity onto the target.
  have surj : ∀ a ∈ tgt, ∃ q ∈ src, map f hf q = a := by
    rintro a ⟨ha, haW⟩
    rw [coordsOrZero_of_mem s ha] at haW
    set ca := coords y s ⟨a, ha⟩
    obtain ⟨hψD, hψF, hψO, -⟩ := hψW ca haW
    let _ : Algebra Γ(Y, U) ℂ := (evalHom a ha).toAlgebra
    have hev : ∀ pt' : Polynomial (MvPolynomial ι ℂ),
        Polynomial.aeval (ψ ca) (pt'.map (presentationHom y s)) = polyFun pt' (ca, ψ ca) := by
      intro pt'
      rw [Polynomial.aeval_def]
      exact eval₂_map_presentationHom s pt' ha _
    have hmap : P.HasMap (ψ ca) := by
      refine ⟨by rw [← hFt, hev]; exact hψF, ?_⟩
      rw [← hGt, hev]
      exact Ne.isUnit hψO
    let χ : T →+* ℂ := ((P.P.lift (ψ ca) hmap).comp P.equivRing.toAlgHom).toRingHom
    have χA : ∀ r, χ (algebraMap _ T r) = eval r a ha := by
      intro r
      change P.P.lift _ hmap (P.equivRing (algebraMap _ T r)) = _
      rw [AlgEquiv.commutes, AlgHom.commutes]
      rfl
    have χx : χ P.x = ψ ca := by
      change P.P.lift _ hmap (P.equivRing P.x) = _
      rw [P.equivRing_x, StandardEtalePair.lift_X]
    let ψB : Γ(Y', U') →+* ℂ := χ.comp (algebraMap Γ(Y', U') T)
    have ψB_A : ∀ r, ψB (f.appLE U U' e r) = eval r a ha := by
      intro r
      rw [← halg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, χA]
    have hconst : ∀ c', ψB (constHom (y := y') U' c') = c' := by
      intro c'
      rw [← appLE_constHom f hf e c', ψB_A, eval_constHom]
    let q := ofRingHom hU' hconst
    have hq : q.Mem U' := ofRingHom_mem hU' hconst
    have evq : ∀ g h, eval g q h = ψB g := fun g h => eval_ofRingHom hU' hconst g h
    have hbq : eval b q hq ≠ 0 := by
      rw [evq]
      exact ((IsLocalization.Away.algebraMap_isUnit (S := T) b).map χ).ne_zero
    have hfq : map f hf q = a := by
      refine eq_of_eval_eq hU (hmemU q hq) ha fun r => ?_
      rw [← eval_appLE f hf e r q hq, evq, ψB_A]
    have hchi : chi q hq hbq = χ :=
      IsLocalization.ringHom_ext (Submonoid.powers b) (RingHom.ext fun g => by
        rw [RingHom.comp_apply, chi_B q hq hbq, evq]
        )
    refine ⟨q, ⟨hq, ?_, ?_, ?_⟩, hfq⟩
    · rwa [evalOrZero_of_mem _ hq]
    · rw [coordsOrZero_of_mem s (hmemU q hq)]
      have : (⟨map f hf q, hmemU q hq⟩ : {a : ComplexPoints y // a.Mem U}) = ⟨a, ha⟩ :=
        Subtype.ext hfq
      rw [this]
      exact haW
    · rw [tT_eq q hq hbq, hchi, χx]
      exact hψD
  have mapsTo : ∀ q ∈ src, map f hf q ∈ tgt := by
    rintro q ⟨hq, -, hW', -⟩
    exact ⟨hmemU q hq, hW'⟩
  have : Nonempty (ComplexPoints y') := ⟨p⟩
  let inv := Function.invFunOn (map f hf) src
  have inv_mem : ∀ a ∈ tgt, inv a ∈ src := fun a ha => Function.invFunOn_mem (surj a ha)
  have inv_eq : ∀ a ∈ tgt, map f hf (inv a) = a := fun a ha => Function.invFunOn_eq (surj a ha)
  -- The source and the target are open.
  have hopenU' : IsOpen {q : ComplexPoints y' | q.Mem U'} := isOpen_setOf_mem U'
  have open_src : IsOpen src := by
    have h1 : IsOpen ({q : ComplexPoints y' | q.Mem U'} ∩ evalOrZero U' b ⁻¹' {0}ᶜ) :=
      (continuousOn_evalOrZero U' b).isOpen_inter_preimage hopenU' isOpen_compl_singleton
    have h2 : IsOpen (({q : ComplexPoints y' | q.Mem U'} ∩ evalOrZero U' b ⁻¹' {0}ᶜ) ∩
        (coordsOrZero s ∘ map f hf) ⁻¹' W) := by
      refine ContinuousOn.isOpen_inter_preimage ?_ h1 hW
      exact (continuousOn_coordsOrZero s).comp (continuous_map f hf).continuousOn
        (fun q hq => hmemU q hq.1)
    have h3 : IsOpen ((({q : ComplexPoints y' | q.Mem U'} ∩ evalOrZero U' b ⁻¹' {0}ᶜ) ∩
        (coordsOrZero s ∘ map f hf) ⁻¹' W) ∩ tT ⁻¹' D) := by
      refine ContinuousOn.isOpen_inter_preimage ?_ h2 hD
      exact ((continuousOn_evalOrZero U' c).mono fun q hq => hq.1.1).div
        (((continuousOn_evalOrZero U' b).mono fun q hq => hq.1.1).pow k)
        fun q hq => pow_ne_zero _ hq.1.2
    convert h3 using 1
    ext q
    simp only [src, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_compl_singleton_iff, Function.comp_apply, and_assoc]
  have open_tgt : IsOpen tgt :=
    (continuousOn_coordsOrZero s).isOpen_inter_preimage (isOpen_setOf_mem U) hW
  -- The holomorphic functions `G`.
  have Gdiff : ∀ g, DifferentiableOn ℂ (Gfun g) W := by
    intro g c' hc'
    have hgr : DifferentiableAt ℂ (fun c'' => (c'', ψ c'')) c' :=
      differentiableAt_id.prodMk (hψW c' hc').2.2.2
    have h1 : DifferentiableAt ℂ (fun c'' => polyFun (pt g) (c'', ψ c'')) c' :=
      ((contDiff_polyFun (pt g) (n := 1)).differentiable (by simp) _).comp c' hgr
    have h2 : DifferentiableAt ℂ (fun c'' => polyFun Gt (c'', ψ c'')) c' :=
      ((contDiff_polyFun Gt (n := 1)).differentiable (by simp) _).comp c' hgr
    have h3 : DifferentiableAt ℂ (fun c'' => polyFun Gt (c'', ψ c'') ^ n g) c' := h2.pow _
    have h4 : DifferentiableAt ℂ
        (fun c'' => polyFun (pt g) (c'', ψ c'') * (polyFun Gt (c'', ψ c'') ^ n g)⁻¹) c' :=
      h1.mul (h3.inv (pow_ne_zero _ (hGne c' hc')))
    have h5 : DifferentiableAt ℂ (Gfun g) c' := by
      simpa only [Gfun, div_eq_mul_inv] using h4
    exact h5.differentiableWithinAt
  -- The inverse is continuous.
  have inv_cont : ContinuousOn inv tgt := by
    rw [continuousOn_iff_continuous_domRestrict]
    let h : tgt → {q : ComplexPoints y' // q.Mem U'} := fun a => ⟨inv a, (inv_mem a a.2).1⟩
    have hh : Continuous h := by
      rw [(isInducing_evalMap hU').continuous_iff]
      refine continuous_pi fun g => ?_
      have hco : Continuous fun a : tgt => coordsOrZero s (a : ComplexPoints y) :=
        ((continuousOn_coordsOrZero s).mono fun a ha => ha.1).domRestrict
      refine ((Gdiff g).continuousOn.comp_continuous hco fun a => a.2.2).congr fun a => ?_
      obtain ⟨hq, hbq, hW', hD'⟩ := src_mem _ (inv_mem a a.2)
      have hc : coordsOrZero s (a : ComplexPoints y) =
          coords y s ⟨map f hf (inv a), hmemU _ hq⟩ := by
        rw [← coordsOrZero_of_mem, inv_eq a a.2]
      simp only [Function.comp_apply, evalMap, h]
      rw [eval_eq g _ hq hbq hW' hD', hc]
    exact continuous_subtype_val.comp hh
  let φ : OpenPartialHomeomorph (ComplexPoints y') (ComplexPoints y) :=
    { toFun := map f hf
      invFun := inv
      source := src
      target := tgt
      map_source' := mapsTo
      map_target' := inv_mem
      left_inv' := injOn.leftInvOn_invFunOn
      right_inv' := inv_eq
      open_source := open_src
      open_target := open_tgt
      continuousOn_toFun := (continuous_map f hf).continuousOn
      continuousOn_invFun := inv_cont }
  refine ⟨φ, W, ?_, rfl, hW, fun q hq => hq.1, ?_, fun g => ⟨Gfun g, Gdiff g, ?_⟩⟩
  · refine ⟨hp, by rwa [evalOrZero_of_mem _ hp], ?_, ?_⟩
    · rw [coordsOrZero_of_mem s (hmemU p hp)]
      exact hc₀W
    · rw [tT_eq p hp hb]
      exact ht₀D
  · ext a
    constructor
    · rintro ⟨ha, haW⟩
      exact ⟨ha, by rwa [coordsOrZero_of_mem s ha] at haW⟩
    · rintro ⟨ha, haW⟩
      exact ⟨ha, by rwa [coordsOrZero_of_mem s ha]⟩
  · intro q hqs hq ha
    obtain ⟨hq', hbq, hW', hD'⟩ := src_mem q hqs
    exact eval_eq g q hq' hbq hW' hD'

end Etale

/-! ### Schemes locally of finite type over `ℂ` -/

section FiniteType

variable {Z : Scheme.{0}} {z : Z ⟶ Spec (.of ℂ)}

/-- For `z` locally of finite type, the constants `ℂ → Γ(Z, V)` of an affine open are of finite
type. -/
theorem finiteType_constHom [LocallyOfFiniteType z] {V : Z.Opens} (hV : IsAffineOpen V) :
    (constHom (y := z) V).FiniteType := by
  have h1 : (z.appLE ⊤ V (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType z inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  have h2 : (Scheme.ΓSpecIso (.of ℂ)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

/-- **Finite presentations of affine opens.** If `z` is locally of finite type, the ring of
functions of an affine open `V` is generated over `ℂ` by finitely many functions. -/
theorem exists_surjective_presentationHom [LocallyOfFiniteType z] {V : Z.Opens}
    (hV : IsAffineOpen V) :
    ∃ (n : ℕ) (s : Fin n → Γ(Z, V)), Function.Surjective (presentationHom z s) := by
  let _ : Algebra ℂ Γ(Z, V) := (constHom (y := z) V).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Z, V) := finiteType_constHom hV
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine ⟨n, fun i => g (MvPolynomial.X i), ?_⟩
  have : presentationHom z (fun i => g (MvPolynomial.X i)) = g.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [presentationHom, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rfl
    · simp [presentationHom]
  rw [this]
  exact hg

/-- **A nonempty scheme locally of finite type over `ℂ` has a complex point** (Hilbert's
Nullstellensatz). -/
theorem nonempty_of_locallyOfFiniteType [LocallyOfFiniteType z] [Nonempty Z] :
    Nonempty (ComplexPoints z) := by
  obtain ⟨w⟩ : Nonempty Z := inferInstance
  obtain ⟨V, hV, hwV, -⟩ :=
    (Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens) (show w ∈ (⊤ : Z.Opens) from trivial)
  have : Nonempty V := ⟨⟨w, hwV⟩⟩
  have : Nontrivial Γ(Z, V) := Scheme.component_nontrivial Z V
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(Z, V)
  let _ : Field (Γ(Z, V) ⧸ M) := Ideal.Quotient.field M
  let _ : Algebra ℂ Γ(Z, V) := (constHom (y := z) V).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Z, V) := finiteType_constHom hV
  have : Algebra.FiniteType ℂ (Γ(Z, V) ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ M) (Ideal.Quotient.mkₐ_surjective ℂ M)
  have : Module.Finite ℂ (Γ(Z, V) ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ _
  have : Algebra.IsIntegral ℂ (Γ(Z, V) ⧸ M) := Algebra.IsIntegral.of_finite ℂ _
  have bij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := Γ(Z, V) ⧸ M)
  let eq : ℂ ≃+* Γ(Z, V) ⧸ M := RingEquiv.ofBijective (algebraMap ℂ _) bij
  let φ : Γ(Z, V) →+* ℂ := eq.symm.toRingHom.comp (Ideal.Quotient.mk M)
  have hφ : ∀ c, φ (constHom (y := z) V c) = c := by
    intro c
    change eq.symm (Ideal.Quotient.mk M (algebraMap ℂ Γ(Z, V) c)) = c
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, AlgHom.commutes]
    exact eq.symm_apply_apply c
  exact ⟨ofRingHom hV hφ⟩

end FiniteType

/-! ### The main theorems -/

section Main

variable {Y Y' : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} {y' : Y' ⟶ Spec (.of ℂ)}

/-- **An étale morphism of schemes locally of finite type over `ℂ` induces a local
homeomorphism on complex points.** -/
theorem isLocalHomeomorph_map_of_etale [LocallyOfFiniteType y] (f : Y' ⟶ Y) [Etale f]
    (hf : f ≫ y = y') : IsLocalHomeomorph (map f hf) := by
  intro p
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
    (show (map f hf p).hom.base pt ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U', hU', hzU', hU'le⟩ := (Opens.isBasis_iff_nbhd.1 Y'.isBasis_affineOpens)
    (show p.hom.base pt ∈ f ⁻¹ᵁ U from hxU)
  obtain ⟨n, s, hs⟩ := exists_surjective_presentationHom (z := y) hU
  obtain ⟨φ, W, hpφ, hφ, -⟩ :=
    exists_openPartialHomeomorph_of_etale f hf hU hs hU' hU'le p ((mem_iff pt).2 hzU')
  exact ⟨φ, hpφ, hφ.symm⟩

/-- The fibres of a local homeomorphism are discrete. -/
theorem discreteTopology_preimage_singleton {X X' : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] {g : X → X'} (hg : IsLocalHomeomorph g) (a : X') :
    DiscreteTopology (g ⁻¹' {a}) := by
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨q, hq⟩
  obtain ⟨e, hqe, rfl⟩ := hg q
  refine isOpen_induced_iff.2 ⟨e.source, e.open_source, ?_⟩
  ext ⟨r, hr⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq]
  constructor
  · intro hre
    exact e.injOn hre hqe (hr.trans hq.symm)
  · rintro rfl
    exact hqe

/-- **The fibres of an étale morphism on complex points are discrete.** -/
theorem discreteTopology_fiber_of_etale [LocallyOfFiniteType y] (f : Y' ⟶ Y) [Etale f]
    (hf : f ≫ y = y') (a : ComplexPoints y) : DiscreteTopology (map f hf ⁻¹' {a}) :=
  discreteTopology_preimage_singleton (isLocalHomeomorph_map_of_etale f hf) a

/-- A complex point `a` of `Y` whose underlying point is in the image of `f : Y' ⟶ Y`, with `Y'`
locally of finite type over `ℂ`, is the image of a complex point of `Y'`. -/
theorem exists_map_eq_of_mem_range [LocallyOfFiniteType y'] (f : Y' ⟶ Y) (hf : f ≫ y = y')
    (a : ComplexPoints y) (x : Spec (.of ℂ)) (hx : a.hom.base x ∈ Set.range f.base) :
    ∃ q : ComplexPoints y', map f hf q = a := by
  have : LocallyOfFiniteType (f ≫ y) := hf ▸ inferInstance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f y
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := a.hom) (g := f) x z hz.symm
  have : Nonempty ↥(Limits.pullback a.hom f) := ⟨w⟩
  obtain ⟨q₀⟩ := nonempty_of_locallyOfFiniteType (z := Limits.pullback.fst a.hom f)
  have hsnd : Limits.pullback.snd a.hom f ≫ y' = Limits.pullback.fst a.hom f := by
    rw [← hf, ← Category.assoc, ← Limits.pullback.condition, Category.assoc, a.hom_comp,
      Category.comp_id]
  refine ⟨map _ hsnd q₀, ext ?_⟩
  simp only [map_hom, Category.assoc]
  rw [← Limits.pullback.condition, ← Category.assoc, q₀.hom_comp, Category.id_comp]

/-- **Jointly surjective families.** If morphisms `f_i : Y_i ⟶ Y` over `ℂ`, with every `Y_i`
locally of finite type over `ℂ`, are jointly surjective on underlying points, they are jointly
surjective on complex points. This applies to étale families when `Y` is locally of finite
type. -/
theorem exists_map_eq_of_jointlySurjective {J : Type*} {Z : J → Scheme.{0}}
    {z : ∀ j, Z j ⟶ Spec (.of ℂ)} [∀ j, LocallyOfFiniteType (z j)] (f : ∀ j, Z j ⟶ Y)
    (hf : ∀ j, f j ≫ y = z j) (hsurj : ∀ x : Y, ∃ j, x ∈ Set.range (f j).base)
    (a : ComplexPoints y) : ∃ (j : J) (q : ComplexPoints (z j)), map (f j) (hf j) q = a := by
  obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨j, hj⟩ := hsurj (a.hom.base x)
  exact ⟨j, exists_map_eq_of_mem_range (f j) (hf j) a x hj⟩

/-- **Jointly surjective étale families** of schemes over `Y`, `Y` locally of finite type over
`ℂ`, are jointly surjective on complex points. -/
theorem exists_map_eq_of_jointlySurjective_of_etale [LocallyOfFiniteType y] {J : Type*}
    {Z : J → Scheme.{0}} (f : ∀ j, Z j ⟶ Y) [∀ j, Etale (f j)]
    (hsurj : ∀ x : Y, ∃ j, x ∈ Set.range (f j).base) (a : ComplexPoints y) :
    ∃ (j : J) (q : ComplexPoints (f j ≫ y)), map (f j) rfl q = a :=
  exists_map_eq_of_jointlySurjective (z := fun j => f j ≫ y) f (fun _ => rfl) hsurj a

end Main

end AlgebraicGeometry.Scheme.ComplexPoints
