module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Functoriality

/-!
# Smooth schemes over `ℂ` are locally regular zero sets on complex points

Let `y : Y ⟶ Spec ℂ` be smooth of relative dimension `d`. The Jacobian criterion says that
every point of `Y` has an affine open neighbourhood `U` with a presentation
`Γ(Y, U) ≅ ℂ[x₁, …, x_{c+d}] / (f₁, …, f_c)` whose `c × c` Jacobian minor
`det (∂ f_j / ∂ x_{m(k)})` is a unit of `Γ(Y, U)` (a *submersive presentation*, Tag 00T7).
Taking `x_i ↦ s_i ∈ Γ(Y, U)`, the coordinates `p ↦ (s_i(p))_i` identify `U(ℂ)` with the
common zero set in `ℂ^{c+d}` of the polynomials `f_j`; the Jacobian minor is a polynomial
which does not vanish on that zero set, so on the open set `W` where it does not vanish the
polynomial map `F = (f_j)_j : ℂ^{c+d} → ℂ^c` has surjective derivative and `U(ℂ) ≅ F⁻¹(0) ∩ W`.
Since `F` is holomorphic and a `ℂ`-linear surjection is an `ℝ`-linear surjection, the same holds
after identifying `ℂ^{c+d}` with a real vector space: `U(ℂ)` is locally the zero set of a real
analytic map with surjective derivative.

## Main results

* `MvPolynomial.hasFDerivAt_eval_sum_pderiv`: the derivative of a polynomial function is given by
  its partial derivatives.
* `MvPolynomial.surjective_fderiv_eval_of_det_ne_zero`: a family of polynomials has surjective
  derivative at a point where a maximal minor of its Jacobian matrix does not vanish.
* `exists_real_regularZeroSet_of_complex`: a local zero set of a holomorphic map with surjective
  complex derivative is a local zero set of a real analytic map with surjective real derivative.
* `AlgebraicGeometry.Scheme.ComplexPoints.range_coords_eq_of_submersivePresentation`: the
  Jacobian criterion on `U(ℂ)` for a submersive presentation of `Γ(Y, U)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_range_coords_eq_of_smoothOfRelativeDimension`:
  for `y` smooth of relative dimension `d`, every complex point has an affine neighbourhood
  `U` and a presentation in `c + d` variables for which `U(ℂ)` is the zero set of `c` polynomials
  with surjective derivative on an open set `W ⊇ U(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_range_coords_eq_of_smooth`: the same for `y`
  smooth, with some relative dimension at the point.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_real_regularZeroSet_of_smoothOfRelativeDimension`:
  the real form, for any real normed space identified with `ℂ^{c+d}`.

## Implementation notes

The presentation is not an arbitrary one: it is a submersive presentation produced by Mathlib's
`SmoothOfRelativeDimension` (or `Smooth`), on an affine open neighbourhood chosen with it. The
base ring of that presentation is `Γ(Spec ℂ, ⊤)`; its relations are moved to `ℂ[x]` along
`Scheme.ΓSpecIso`, and the hypothesis `hconst` records that the algebra structure is the one
given by the constants `constHom`. The holomorphic map is a polynomial map, so it is analytic
(`ContDiff ℂ ω`), and the real form is `ContDiff ℝ ω`.

## References

* [Stacks] The Stacks Project, Tags 00T6, 00T7 (standard smooth algebras), 01V4 (smooth
  morphisms), 00TA.
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
-/

public section

open CategoryTheory MvPolynomial
open scoped ContDiff

universe u

namespace MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}

theorem hasFDerivAt_eval_sum_pderiv [Fintype ι] (P : MvPolynomial ι 𝕜) (x : ι → 𝕜) :
    HasFDerivAt (fun z => eval z P)
      (∑ i, eval x (pderiv i P) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact (hasFDerivAt_const (𝕜 := 𝕜) (E := ι → 𝕜) a x).congr_fderiv (by ext; simp)
  | add p q hp hq =>
    have hfun : (fun z => eval z (p + q)) = fun z => eval z p + eval z q := by ext; simp
    rw [hfun]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h := hp.mul (hasFDerivAt_apply (𝕜 := 𝕜) (F' := fun _ : ι => 𝕜) j x)
    have hfun : (fun z => eval z (p * X j)) = fun z => eval z p * z j := by ext; simp
    rw [hfun]
    refine h.congr_fderiv ?_
    ext v
    simp only [Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, map_add, map_mul,
      eval_X]
    simp [apply_ite, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm]

theorem fderiv_eval_apply_single [Finite ι] [DecidableEq ι] (P : MvPolynomial ι 𝕜) (x : ι → 𝕜)
    (i : ι) : fderiv 𝕜 (fun z => eval z P) x (Pi.single i 1) = eval x (pderiv i P) := by
  have := Fintype.ofFinite ι
  rw [(hasFDerivAt_eval_sum_pderiv P x).fderiv]
  simp [Pi.single_apply]

theorem surjective_fderiv_eval_of_det_ne_zero [Finite ι] {σ : Type*} [Fintype σ]
    [DecidableEq σ] (F : σ → MvPolynomial ι 𝕜) (m : σ → ι) (x : ι → 𝕜)
    (h : (Matrix.of fun k j => eval x (pderiv (m k) (F j))).det ≠ 0) :
    Function.Surjective (fderiv 𝕜 (fun z j => eval z (F j)) x) := by
  classical
  have := Fintype.ofFinite ι
  have hF : HasFDerivAt (fun z j => eval z (F j))
      (ContinuousLinearMap.pi fun j => fderiv 𝕜 (fun z => eval z (F j)) x) x :=
    hasFDerivAt_pi.2 fun j => (hasFDerivAt_eval_sum_pderiv (F j) x).differentiableAt.hasFDerivAt
  rw [hF.fderiv]
  intro w
  have hM : IsUnit (Matrix.of fun k j => eval x (pderiv (m k) (F j))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  obtain ⟨u, hu⟩ := Matrix.vecMul_surjective_iff_isUnit.2 hM w
  refine ⟨∑ k, u k • Pi.single (m k) (1 : 𝕜), ?_⟩
  rw [← hu]
  funext j
  simp [map_sum, fderiv_eval_apply_single, Matrix.vecMul, dotProduct]

theorem contDiff_eval_pi [Fintype ι] {σ : Type*} [CompleteSpace 𝕜] (F : σ → MvPolynomial ι 𝕜)
    [Fintype σ] {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun z j => eval z (F j)) :=
  contDiff_pi.2 fun j => (AnalyticOnNhd.eval_mvPolynomial (F j)).contDiff

end MvPolynomial

namespace Algebra.PreSubmersivePresentation

/-- The determinant of the Jacobian matrix of a presentation, with its coefficients mapped along
`φ`, is the determinant of the Jacobian matrix of the mapped relations. -/
theorem map_det_jacobiMatrix {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S ι σ) (φ : R →+* T) :
    P.jacobiMatrix.det.map φ =
      (Matrix.of fun k j => pderiv (P.map k) ((P.relation j).map φ)).det := by
  rw [RingHom.map_det]
  congr 1
  ext k j
  simp [RingHom.mapMatrix_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply, pderiv_map]

end Algebra.PreSubmersivePresentation

theorem exists_real_regularZeroSet_of_complex {X Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Z] [NormedSpace ℂ Z] [FiniteDimensional ℂ Z]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (e : X ≃L[ℝ] E) {G : X → Z}
    (hG : ContDiff ℂ ω G) {K W : Set X}
    (hGs : ∀ x ∈ W, Function.Surjective (fderiv ℂ G x)) (hK : K ∩ W = {x ∈ W | G x = 0}) :
    ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)), ContDiff ℝ ω g ∧
      (∀ x ∈ e.symm ⁻¹' W, Function.Surjective (fderiv ℝ g x)) ∧
      e '' K ∩ e.symm ⁻¹' W = {x ∈ e.symm ⁻¹' W | g x = 0} := by
  let e₂ : Z ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  refine ⟨Module.finrank ℝ Z, fun x => e₂ (G (e.symm x)), ?_, ?_, ?_⟩
  · exact e₂.contDiff.comp ((hG.restrict_scalars ℝ).comp e.symm.contDiff)
  · intro x hx
    have hd : HasFDerivAt G (fderiv ℂ G (e.symm x)) (e.symm x) :=
      (hG.differentiable (by simp) _).hasFDerivAt
    have h := (e₂.hasFDerivAt.comp x ((hd.restrictScalars ℝ).comp x e.symm.hasFDerivAt))
    rw [show (fun x => e₂ (G (e.symm x))) = e₂ ∘ G ∘ e.symm from rfl, h.fderiv]
    exact e₂.surjective.comp ((hGs _ hx).comp e.symm.surjective)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      ContinuousLinearEquiv.image_eq_preimage_symm, map_eq_zero_iff _ e₂.injective]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, ((Set.ext_iff.1 hK (e.symm x)).1 ⟨h1, h2⟩).2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨((Set.ext_iff.1 hK (e.symm x)).2 ⟨h1, h2⟩).1, h1⟩

namespace AlgebraicGeometry.Scheme.ComplexPoints
variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} {U : Y.Opens}

section Submersive

variable [Algebra Γ(Spec (.of ℂ), ⊤) Γ(Y, U)]
  (hconst : (constHom (y := y) U).comp (Scheme.ΓSpecIso (.of ℂ)).hom.hom =
    algebraMap Γ(Spec (.of ℂ), ⊤) Γ(Y, U))
include hconst

theorem presentationHom_map_eq_aeval {ι : Type*} (s : ι → Γ(Y, U))
    (Q : MvPolynomial ι Γ(Spec (.of ℂ), ⊤)) :
    presentationHom y s (Q.map (Scheme.ΓSpecIso (.of ℂ)).hom.hom) = aeval s Q := by
  simp only [presentationHom, coe_eval₂Hom, eval₂_map, hconst, aeval_def]

theorem surjective_presentationHom_val {ι σ : Type*}
    (P : Algebra.Presentation Γ(Spec (.of ℂ), ⊤) Γ(Y, U) ι σ) :
    Function.Surjective (presentationHom y P.val) := by
  intro a
  obtain ⟨Q, rfl⟩ := P.aeval_val_surjective a
  exact ⟨_, presentationHom_map_eq_aeval hconst _ Q⟩

theorem zeroLocus_val_eq {ι σ : Type*}
    (P : Algebra.Presentation Γ(Spec (.of ℂ), ⊤) Γ(Y, U) ι σ) :
    zeroLocus y P.val =
      {z | ∀ j,
        MvPolynomial.eval z ((P.relation j).map (Scheme.ΓSpecIso (.of ℂ)).hom.hom) = 0} := by
  ext z
  constructor
  · intro hz j
    refine hz _ (RingHom.mem_ker.2 ?_)
    rw [presentationHom_map_eq_aeval hconst, P.aeval_val_relation]
  · intro hz Q hQ
    set φ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom
    set ψ := (Scheme.ΓSpecIso (.of ℂ)).inv.hom
    have hφψ : φ.comp ψ = RingHom.id ℂ := by
      rw [← CommRingCat.hom_comp, Iso.inv_hom_id]; rfl
    have hQ' : Q = (Q.map ψ).map φ := by
      rw [MvPolynomial.map_map, hφψ, MvPolynomial.map_id]
    have hmem : Q.map ψ ∈ Ideal.span (Set.range P.relation) := by
      rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker,
        ← presentationHom_map_eq_aeval hconst, ← hQ']
      exact hQ
    have hle : Ideal.map (MvPolynomial.map φ) (Ideal.span (Set.range P.relation)) ≤
        RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact hz j
    rw [hQ']
    exact hle (Ideal.mem_map_of_mem _ hmem)

theorem eval_coords_map_eq {ι : Type*} (s : ι → Γ(Y, U)) (Q : MvPolynomial ι Γ(Spec (.of ℂ), ⊤))
    (q : {q : ComplexPoints y // q.Mem U}) :
    MvPolynomial.eval (coords y s q) (Q.map (Scheme.ΓSpecIso (.of ℂ)).hom.hom) =
      eval (aeval s Q) q.1 q.2 := by
  rw [← presentationHom_map_eq_aeval hconst, eval_presentationHom]
  rfl

theorem eval_coords_map_det_jacobiMatrix_ne_zero {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation Γ(Spec (.of ℂ), ⊤) Γ(Y, U) ι σ)
    (q : {q : ComplexPoints y // q.Mem U}) :
    MvPolynomial.eval (coords y P.val q) (P.jacobiMatrix.det.map (Scheme.ΓSpecIso (.of ℂ)).hom.hom)
      ≠ 0 := by
  rw [eval_coords_map_eq hconst]
  have h : aeval P.val P.jacobiMatrix.det = P.jacobian := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
  rw [h, ← evalHom_apply]
  exact (P.jacobian_isUnit.map (evalHom q.1 q.2)).ne_zero

/-- **Jacobian criterion on complex points, for a submersive presentation.** If `P` is a
submersive presentation of `Γ(Y, U)` over `Γ(Spec ℂ, ⊤)`, `U` affine, then the coordinates
`p ↦ (P.val i)(p)` identify `U(ℂ)` with `{x ∈ W | F x = 0}`, where `F` are the relations of `P`
with complex coefficients and `W ⊇ U(ℂ)` is the open set where their Jacobian minor does not
vanish; the derivative of `F` is surjective on `W`. -/
theorem range_coords_eq_of_submersivePresentation (hU : IsAffineOpen U) {ι σ : Type*} [Finite ι]
    [Finite σ] (P : Algebra.SubmersivePresentation Γ(Spec (.of ℂ), ⊤) Γ(Y, U) ι σ) :
    ∃ (F : σ → MvPolynomial ι ℂ) (W : Set (ι → ℂ)), IsOpen W ∧
      Set.range (coords y P.val) ⊆ W ∧
      (∀ x ∈ W, Function.Surjective (fderiv ℂ (fun z j => MvPolynomial.eval z (F j)) x)) ∧
      Set.range (coords y P.val) = {x ∈ W | ∀ j, MvPolynomial.eval x (F j) = 0} := by
  classical
  have := Fintype.ofFinite σ
  set φ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom
  let F : σ → MvPolynomial ι ℂ := fun j => (P.relation j).map φ
  let D : MvPolynomial ι ℂ := (Matrix.of fun k j => pderiv (P.map k) (F j)).det
  have hD : ∀ x, MvPolynomial.eval x D =
      (Matrix.of fun k j => MvPolynomial.eval x (pderiv (P.map k) (F j))).det := by
    intro x
    rw [RingHom.map_det]
    rfl
  have hrange : Set.range (coords y P.val) = {z | ∀ j, MvPolynomial.eval z (F j) = 0} := by
    rw [range_coords hU (surjective_presentationHom_val hconst P.toPresentation),
      zeroLocus_val_eq hconst P.toPresentation]
  refine ⟨F, {x | MvPolynomial.eval x D ≠ 0},
    isOpen_ne_fun (MvPolynomial.continuous_eval D) continuous_const, ?_, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    have := eval_coords_map_det_jacobiMatrix_ne_zero hconst P q
    rwa [Algebra.PreSubmersivePresentation.map_det_jacobiMatrix] at this
  · intro x hx
    exact MvPolynomial.surjective_fderiv_eval_of_det_ne_zero F P.map x ((hD x) ▸ hx)
  · ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · obtain ⟨q, rfl⟩ := hx
        have := eval_coords_map_det_jacobiMatrix_ne_zero hconst P q
        rwa [Algebra.PreSubmersivePresentation.map_det_jacobiMatrix] at this
      · rw [hrange] at hx
        exact hx
    · rintro ⟨-, hx⟩
      rw [hrange]
      exact hx

/-- The Jacobian criterion on complex points for a submersive presentation of dimension `d`
with `c` relations, reindexed by `Fin (c + d)` and `Fin c`, at a given point `p ∈ U(ℂ)`. -/
theorem exists_fin_range_coords_eq_of_submersivePresentation (hU : IsAffineOpen U)
    {p : ComplexPoints y} (hp : p.Mem U) {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation Γ(Spec (.of ℂ), ⊤) Γ(Y, U) ι σ) {d : ℕ}
    (hPd : P.dimension = d) :
    ∃ (c : ℕ) (s : Fin (c + d) → Γ(Y, U)), Function.Surjective (presentationHom y s) ∧
      ∃ (F : Fin c → MvPolynomial (Fin (c + d)) ℂ) (W : Set (Fin (c + d) → ℂ)), IsOpen W ∧
        coords y s ⟨p, hp⟩ ∈ W ∧
        (∀ x ∈ W, Function.Surjective (fderiv ℂ (fun z j => MvPolynomial.eval z (F j)) x)) ∧
        Set.range (coords y s) = {x ∈ W | ∀ j, MvPolynomial.eval x (F j) = 0} := by
  have hcard : Nat.card ι = Nat.card σ + d := by
    have := P.card_relations_le_card_vars_of_isFinite
    rw [← hPd]
    simp only [Algebra.Presentation.dimension]
    omega
  let P' := P.reindex (Finite.equivFinOfCardEq hcard).symm (Finite.equivFinOfCardEq rfl).symm
  obtain ⟨F, W, hW, hsub, hF, heq⟩ := range_coords_eq_of_submersivePresentation hconst hU P'
  exact ⟨Nat.card σ, P'.val, surjective_presentationHom_val hconst P'.toPresentation,
    F, W, hW, hsub ⟨⟨p, hp⟩, rfl⟩, hF, heq⟩

end Submersive

/-- The constants of `Γ(Y, V)` are the algebra structure given by `y`. -/
theorem constHom_comp_ΓSpecIso_hom (V : Y.Opens) (e : V ≤ y ⁻¹ᵁ ⊤) :
    (constHom (y := y) V).comp (Scheme.ΓSpecIso (.of ℂ)).hom.hom = (y.appLE ⊤ V e).hom := by
  ext c
  simp [constHom]

/-- **Jacobian criterion on complex points.** Let `y : Y ⟶ Spec ℂ` be smooth of relative
dimension `d` and `p ∈ Y(ℂ)`. There are an affine open `U ∋ p`, a presentation
`ℂ[x₁, …, x_{c+d}] ↠ Γ(Y, U)`, `x_i ↦ s_i`, polynomials `F = (F₁, …, F_c)` and an open
`W ⊆ ℂ^{c+d}` containing the coordinates of `p` such that the derivative of `F` is surjective
at every point of `W`, and the coordinates identify `U(ℂ)` with `{x ∈ W | F x = 0}`. -/
theorem exists_range_coords_eq_of_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d y] (p : ComplexPoints y) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (hp : p.Mem U) (c : ℕ) (s : Fin (c + d) → Γ(Y, U)),
      Function.Surjective (presentationHom y s) ∧
      ∃ (F : Fin c → MvPolynomial (Fin (c + d)) ℂ) (W : Set (Fin (c + d) → ℂ)), IsOpen W ∧
        coords y s ⟨p, hp⟩ ∈ W ∧
        (∀ x ∈ W, Function.Surjective (fderiv ℂ (fun z j => MvPolynomial.eval z (F j)) x)) ∧
        Set.range (coords y s) = {x ∈ W | ∀ j, MvPolynomial.eval x (F j) = 0} := by
  obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨U', hU', V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := y)
      (p.hom.base x)
  have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain rfl : U' = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [Subsingleton.elim z (y.base (p.hom.base x))]
    exact e hxV
  let := (y.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, P, hPd⟩ := (RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra d hP).out
  have hp : p.Mem V := (mem_iff x).2 hxV
  exact ⟨V, hV, hp, exists_fin_range_coords_eq_of_submersivePresentation
    (constHom_comp_ΓSpecIso_hom V e) hV hp P hPd⟩

/-- **Jacobian criterion on complex points**, for `y : Y ⟶ Spec ℂ` smooth: as
`exists_range_coords_eq_of_smoothOfRelativeDimension`, with some relative dimension `d` at
the point. -/
theorem exists_range_coords_eq_of_smooth [Smooth y] (p : ComplexPoints y) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (hp : p.Mem U) (c d : ℕ)
      (s : Fin (c + d) → Γ(Y, U)), Function.Surjective (presentationHom y s) ∧
      ∃ (F : Fin c → MvPolynomial (Fin (c + d)) ℂ) (W : Set (Fin (c + d) → ℂ)), IsOpen W ∧
        coords y s ⟨p, hp⟩ ∈ W ∧
        (∀ x ∈ W, Function.Surjective (fderiv ℂ (fun z j => MvPolynomial.eval z (F j)) x)) ∧
        Set.range (coords y s) = {x ∈ W | ∀ j, MvPolynomial.eval x (F j) = 0} := by
  obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨U', hU', V, hV, hxV, e, hP⟩ := Smooth.exists_isStandardSmooth y (p.hom.base x)
  have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain rfl : U' = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [Subsingleton.elim z (y.base (p.hom.base x))]
    exact e hxV
  let := (y.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (RingHom.IsStandardSmooth.toAlgebra hP).out
  have hp : p.Mem V := (mem_iff x).2 hxV
  obtain ⟨c, s, hs, rest⟩ := exists_fin_range_coords_eq_of_submersivePresentation
    (constHom_comp_ΓSpecIso_hom V e) hV hp P rfl
  exact ⟨V, hV, hp, c, P.dimension, s, hs, rest⟩

/-- **Real form of the Jacobian criterion on complex points.** Let `y : Y ⟶ Spec ℂ` be smooth
of relative dimension `d` and `p ∈ Y(ℂ)`. There are an affine open `U ∋ p` and a presentation
`ℂ[x₁, …, x_{c+d}] ↠ Γ(Y, U)`, `x_i ↦ s_i`, such that for every real normed space `E` and every
`ℝ`-linear isomorphism `e : ℂ^{c+d} ≃ E`, the image `K` of `U(ℂ)` in `E` is, near `e(s(p))`, the
zero set of a real analytic map `g : E → ℝ^m` with surjective derivative: there is an open
`V ∋ e(s(p))` with `K ∩ V = {x ∈ V | g x = 0}`. -/
theorem exists_real_regularZeroSet_of_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d y] (p : ComplexPoints y) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (hp : p.Mem U) (c : ℕ) (s : Fin (c + d) → Γ(Y, U)),
      Function.Surjective (presentationHom y s) ∧
      ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        (e : (Fin (c + d) → ℂ) ≃L[ℝ] E), ∃ V : Set E, IsOpen V ∧ e (coords y s ⟨p, hp⟩) ∈ V ∧
        ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)), ContDiff ℝ ω g ∧
          (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
          e '' Set.range (coords y s) ∩ V = {x ∈ V | g x = 0} := by
  obtain ⟨U, hU, hp, c, s, hs, F, W, hW, hpW, hF, heq⟩ :=
    exists_range_coords_eq_of_smoothOfRelativeDimension d p
  refine ⟨U, hU, hp, c, s, hs, fun {E} _ _ e => ?_⟩
  have hK : Set.range (coords y s) ∩ W =
      {x ∈ W | (fun z j => MvPolynomial.eval z (F j)) x = 0} := by
    rw [heq]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, funext_iff, Pi.zero_apply]
    tauto
  obtain ⟨m, g, hg, hgs, hgK⟩ := exists_real_regularZeroSet_of_complex e
    (MvPolynomial.contDiff_eval_pi F) hF hK
  exact ⟨e.symm ⁻¹' W, hW.preimage e.symm.continuous, by simpa using hpW, m, g, hg, hgs, hgK⟩

end AlgebraicGeometry.Scheme.ComplexPoints
