module

public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The image of an immersion is locally a regular zero set

Let `F` and `E` be finite-dimensional real normed spaces and let `ψ : F → E` be `Cⁿ` (`n ≥ 1`) on
an open set `V`, with injective derivative at `x₀ ∈ V`. Then, near `x₀`, the image of `ψ` is the
zero set of a `Cⁿ` map `g : E → ℝ^{dim E - dim F}` with surjective derivative.

The proof is the classical one. Complete the derivative `D = ψ'(x₀)` to a linear isomorphism
`(u, t) ↦ D u + L t` from `F × ℝ^{dim E - dim F}` onto `E`, where `L` parametrizes a complement of
the range of `D`. The map `Φ (x, t) = ψ x + L t` has invertible derivative at `(x₀, 0)`, so by the
inverse function theorem it restricts to a `Cⁿ` diffeomorphism from a product neighbourhood
`V₀ × B` of `(x₀, 0)` onto an open set `W ∋ ψ x₀`. The second component `g` of its inverse is
`Cⁿ` with surjective derivative on `W`, and `{e ∈ W | g e = 0} = Φ (V₀ × {0}) = ψ '' V₀`.

If `ψ` is moreover inducing on `V` (for instance a topological embedding of `V`), then `ψ '' V₀`
is open in `ψ '' V`, and shrinking `W` gives `ψ '' V ∩ W = {e ∈ W | g e = 0}`: the whole image
`ψ '' V` is, near `ψ x₀`, a regular zero set.

## Main results

* `exists_continuousLinearEquiv_prod_of_injective` — an injective linear map `D : F → E` extends
  to a linear isomorphism `(u, t) ↦ D u + L t` from `F × ℝ^{dim E - dim F}` onto `E`.
* `exists_image_eq_regularZeroSet_of_injective_fderiv` — locally near `x₀`, `ψ '' V₀` is the zero
  set in an open `W` of a `Cⁿ` map with surjective derivative on `W`.
* `exists_image_inter_eq_regularZeroSet_of_injective_fderiv` — the same for `ψ '' V ∩ W`, when
  `ψ` is inducing on `V`.
* `exists_inter_eq_regularZeroSet_of_inter_eq_image` — if `K ∩ U = ψ '' V` for an open `U`, with
  `ψ` inducing on `V` and with injective derivative everywhere on `V`, then `K` is, near each point
  of `ψ '' V`, a regular zero set `K ∩ W = {x ∈ W | g x = 0}`.
* `forall_mem_image_exists_regularZeroSet` — the case `K = ψ '' V`.
-/

@[expose] public section

open Set Function Module Topology Filter

noncomputable section

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An injective continuous linear map `D : F →L[ℝ] E` between finite-dimensional spaces extends
to a linear isomorphism `F × ℝ^{dim E - dim F} ≃ E` of the form `(u, t) ↦ D u + L t`. -/
theorem exists_continuousLinearEquiv_prod_of_injective (D : F →L[ℝ] E) (hD : Injective D) :
    ∃ (L : EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)) →L[ℝ] E)
      (φ : (F × EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F))) ≃L[ℝ] E),
      ∀ p, φ p = D p.1 + L p.2 := by
  set G := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F))
  obtain ⟨C, hC⟩ := (LinearMap.range (D : F →ₗ[ℝ] E)).exists_isCompl
  have h1 : finrank ℝ (LinearMap.range (D : F →ₗ[ℝ] E)) = finrank ℝ F :=
    LinearMap.finrank_range_of_inj hD
  have h2 := Submodule.finrank_add_eq_of_isCompl hC
  have hG : finrank ℝ G = finrank ℝ C := by
    simp only [G, finrank_euclideanSpace_fin]; omega
  let e : G ≃ₗ[ℝ] C := LinearEquiv.ofFinrankEq _ _ hG
  let ψ₁ : F ≃ₗ[ℝ] LinearMap.range (D : F →ₗ[ℝ] E) := LinearEquiv.ofInjective _ hD
  let φₗ : (F × G) ≃ₗ[ℝ] E := (ψ₁.prodCongr e).trans (Submodule.prodEquivOfIsCompl _ _ hC)
  refine ⟨(C.subtype.comp (e : G →ₗ[ℝ] C)).toContinuousLinearMap,
    φₗ.toContinuousLinearEquiv, fun p => ?_⟩
  simp [φₗ, ψ₁, Submodule.coe_prodEquivOfIsCompl']

/-- **The image of an immersion is locally a regular zero set.** Let `ψ : F → E` be `Cⁿ`
(`1 ≤ n`) on an open set `V` of a finite-dimensional real normed space, with injective derivative
at `x₀ ∈ V`. Then there are an open neighbourhood `V₀ ⊆ V` of `x₀`, an open `W ∋ ψ x₀` and a map
`g : E → ℝ^{dim E - dim F}`, `Cⁿ` on `W` with surjective derivative at every point of `W`, such
that `ψ '' V₀ = {e ∈ W | g e = 0}`. -/
theorem exists_image_eq_regularZeroSet_of_injective_fderiv {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ψ : F → E} {V : Set F} (hV : IsOpen V) (hψ : ContDiffOn ℝ n ψ V) {x₀ : F} (hx₀ : x₀ ∈ V)
    (hinj : Injective (fderiv ℝ ψ x₀)) :
    ∃ V₀ : Set F, IsOpen V₀ ∧ x₀ ∈ V₀ ∧ V₀ ⊆ V ∧
      ∃ W : Set E, IsOpen W ∧ ψ x₀ ∈ W ∧
        ∃ g : E → EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)),
          ContDiffOn ℝ n g W ∧ (∀ e ∈ W, Surjective (fderiv ℝ g e)) ∧
            ψ '' V₀ = {e ∈ W | g e = 0} := by
  obtain ⟨L, φ, hφ⟩ := exists_continuousLinearEquiv_prod_of_injective (fderiv ℝ ψ x₀) hinj
  set G := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F))
  have : CompleteSpace (F × G) := FiniteDimensional.complete ℝ _
  let Φ : F × G → E := fun p => ψ p.1 + L p.2
  have hVo : IsOpen (V ×ˢ (univ : Set G)) := hV.prod isOpen_univ
  have hΦ : ContDiffOn ℝ n Φ (V ×ˢ univ) :=
    (hψ.comp contDiffOn_fst fun p hp => hp.1).add (L.contDiff.comp contDiff_snd).contDiffOn
  have hΦat : ∀ p ∈ V ×ˢ (univ : Set G), ContDiffAt ℝ n Φ p := fun p hp =>
    hΦ.contDiffAt (hVo.mem_nhds hp)
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ x₀) x₀ :=
    ((hψ.contDiffAt (hV.mem_nhds hx₀)).differentiableAt hn0).hasFDerivAt
  have hΦ' : HasFDerivAt Φ (φ : F × G →L[ℝ] E) (x₀, 0) := by
    have := (hψd.comp (x₀, (0 : G)) hasFDerivAt_fst).add
      (L.hasFDerivAt.comp (x₀, (0 : G)) hasFDerivAt_snd)
    have heq : (φ : F × G →L[ℝ] E) = (fderiv ℝ ψ x₀).comp (ContinuousLinearMap.fst ℝ F G) +
        L.comp (ContinuousLinearMap.snd ℝ F G) :=
      ContinuousLinearMap.ext fun p => by simp [hφ]
    rw [heq]
    exact this
  let P : Set (F × G) := (V ×ˢ univ) ∩
    fderiv ℝ Φ ⁻¹' range (ContinuousLinearEquiv.toContinuousLinearMap (R₁ := ℝ))
  have hP : IsOpen P := (hΦ.continuousOn_fderiv_of_isOpen hVo hn).isOpen_inter_preimage hVo
    ContinuousLinearEquiv.isOpen
  let h := (hΦat (x₀, 0) ⟨hx₀, trivial⟩).toOpenPartialHomeomorph Φ hΦ' hn0
  have hh : (h : F × G → E) = Φ := rfl
  have hO : IsOpen (h.source ∩ P) := h.open_source.inter hP
  have hx₀O : (x₀, (0 : G)) ∈ h.source ∩ P :=
    ⟨(hΦat (x₀, 0) ⟨hx₀, trivial⟩).mem_toOpenPartialHomeomorph_source hΦ' hn0,
      ⟨hx₀, trivial⟩, ⟨φ, hΦ'.fderiv.symm⟩⟩
  obtain ⟨V₀, B, hV₀, hB, hxV₀, h0B, hsub⟩ := isOpen_prod_iff.1 hO x₀ 0 hx₀O
  have hsrc : V₀ ×ˢ B ⊆ h.source := fun p hp => (hsub hp).1
  have hV₀V : V₀ ⊆ V := fun x hx => (hsub (mk_mem_prod hx h0B)).2.1.1
  have key : ∀ p ∈ V₀ ×ˢ B, ∃ ψ' : (F × G) ≃L[ℝ] E,
      HasFDerivAt h.symm (ψ'.symm : E →L[ℝ] F × G) (h p) ∧ ContDiffAt ℝ n h.symm (h p) := by
    intro p hp
    obtain ⟨ψ', hψ'⟩ := (hsub hp).2.2
    have hpV : p ∈ V ×ˢ (univ : Set G) := (hsub hp).2.1
    have hd : HasFDerivAt h (ψ' : F × G →L[ℝ] E) (h.symm (h p)) := by
      rw [h.left_inv (hsrc hp), hh, hψ']
      exact ((hΦat p hpV).differentiableAt hn0).hasFDerivAt
    refine ⟨ψ', h.hasFDerivAt_symm (h.map_source (hsrc hp)) hd,
      h.contDiffAt_symm (h.map_source (hsrc hp)) hd ?_⟩
    rw [h.left_inv (hsrc hp), hh]
    exact hΦat p hpV
  refine ⟨V₀, hV₀, hxV₀, hV₀V, h '' (V₀ ×ˢ B), h.isOpen_image_of_subset_source (hV₀.prod hB) hsrc,
    ⟨(x₀, 0), ⟨hxV₀, h0B⟩, by simp [hh, Φ]⟩, fun e => (h.symm e).2, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨ψ', -, hc⟩ := key p hp
    exact (contDiff_snd.contDiffAt.comp _ hc).contDiffWithinAt
  · intro e he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨ψ', hd, -⟩ := key p hp
    rw [show (fun e => (h.symm e).2) = Prod.snd ∘ h.symm from rfl,
      (hasFDerivAt_snd.comp (h p) hd).fderiv]
    intro t
    exact ⟨ψ' (0, t), by simp⟩
  · ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : h (x, 0) = ψ x := by simp [hh, Φ]
      refine ⟨⟨(x, 0), ⟨hx, h0B⟩, hx'⟩, ?_⟩
      simp only
      rw [← hx', h.left_inv (hsrc ⟨hx, h0B⟩)]
    · rintro ⟨⟨p, hp, rfl⟩, hg⟩
      simp only [h.left_inv (hsrc hp)] at hg
      exact ⟨p.1, hp.1, by simp [hh, Φ, hg]⟩

/-- **The image of an immersion which is inducing is locally a regular zero set.** If moreover
`ψ` restricted to `V` is inducing (for instance a topological embedding of `V`), the open set `W`
can be chosen so that the whole image satisfies `ψ '' V ∩ W = {e ∈ W | g e = 0}`. -/
theorem exists_image_inter_eq_regularZeroSet_of_injective_fderiv {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ψ : F → E} {V : Set F} (hV : IsOpen V) (hψ : ContDiffOn ℝ n ψ V)
    (hind : IsInducing (fun x : V => ψ x)) {x₀ : F} (hx₀ : x₀ ∈ V)
    (hinj : Injective (fderiv ℝ ψ x₀)) :
    ∃ W : Set E, IsOpen W ∧ ψ x₀ ∈ W ∧
      ∃ g : E → EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)),
        ContDiffOn ℝ n g W ∧ (∀ e ∈ W, Surjective (fderiv ℝ g e)) ∧
          ψ '' V ∩ W = {e ∈ W | g e = 0} := by
  obtain ⟨V₀, hV₀, hxV₀, hV₀V, W, hW, hxW, g, hg, hgs, heq⟩ :=
    exists_image_eq_regularZeroSet_of_injective_fderiv hn hV hψ hx₀ hinj
  obtain ⟨O, hO, hOeq⟩ := hind.isOpen_iff.1 (hV₀.preimage continuous_subtype_val)
  have hmem : ∀ x ∈ V, ψ x ∈ O ↔ x ∈ V₀ := fun x hx => by
    have := congrArg ((⟨x, hx⟩ : V) ∈ ·) hOeq
    simpa using this
  refine ⟨W ∩ O, hW.inter hO, ⟨hxW, (hmem x₀ hx₀).2 hxV₀⟩, g, hg.mono inter_subset_left,
    fun e he => hgs e he.1, ?_⟩
  ext e
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hW', hO'⟩
    have : ψ x ∈ {e ∈ W | g e = 0} := heq ▸ mem_image_of_mem ψ ((hmem x hx).1 hO')
    exact ⟨⟨hW', hO'⟩, this.2⟩
  · rintro ⟨⟨hW', hO'⟩, hg0⟩
    have : e ∈ ψ '' V₀ := heq ▸ ⟨hW', hg0⟩
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hV₀V hx, rfl⟩, hW', hO'⟩

/-- **A set locally parametrized by an inducing immersion is locally a regular zero set.** Let
`K ⊆ E` and let `U ⊆ E` be open with `K ∩ U = ψ '' V`, where `ψ` is `Cⁿ` (`1 ≤ n`) on the open set
`V`, inducing on `V`, with injective derivative at every point of `V`. Then near every point `p`
of `ψ '' V`, `K` is the zero set of a `Cⁿ` map with surjective derivative: there are an open
`W ∋ p` and `g : E → ℝᵐ`, `Cⁿ` on `W` with surjective derivative on `W`, such that
`K ∩ W = {x ∈ W | g x = 0}`. -/
theorem exists_inter_eq_regularZeroSet_of_inter_eq_image {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ψ : F → E} {V : Set F} (hV : IsOpen V) (hψ : ContDiffOn ℝ n ψ V)
    (hind : IsInducing (fun x : V => ψ x)) (hinj : ∀ x ∈ V, Injective (fderiv ℝ ψ x))
    {K U : Set E} (hU : IsOpen U) (hKU : K ∩ U = ψ '' V) :
    ∀ p ∈ ψ '' V, ∃ W : Set E, IsOpen W ∧ p ∈ W ∧
      ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)), ContDiffOn ℝ n g W ∧
        (∀ x ∈ W, Surjective (fderiv ℝ g x)) ∧ K ∩ W = {x ∈ W | g x = 0} := by
  rintro _ ⟨x₀, hx₀, rfl⟩
  obtain ⟨W, hW, hxW, g, hg, hgs, heq⟩ :=
    exists_image_inter_eq_regularZeroSet_of_injective_fderiv hn hV hψ hind hx₀ (hinj x₀ hx₀)
  have hxU : ψ x₀ ∈ U := (hKU.symm ▸ mem_image_of_mem ψ hx₀ : ψ x₀ ∈ K ∩ U).2
  refine ⟨W ∩ U, hW.inter hU, ⟨hxW, hxU⟩, _, g, hg.mono inter_subset_left,
    fun x hx => hgs x hx.1, ?_⟩
  ext x
  constructor
  · rintro ⟨hK, hW', hU'⟩
    have : x ∈ ψ '' V ∩ W := ⟨hKU ▸ ⟨hK, hU'⟩, hW'⟩
    rw [heq] at this
    exact ⟨⟨hW', hU'⟩, this.2⟩
  · rintro ⟨⟨hW', hU'⟩, hg0⟩
    have : x ∈ ψ '' V ∩ W := heq ▸ ⟨hW', hg0⟩
    have hK : x ∈ K ∩ U := hKU ▸ this.1
    exact ⟨hK.1, hW', hU'⟩

/-- **The image of an inducing immersion is locally a regular zero set**, in the form used for
neighbourhood retracts: near every point `p` of `ψ '' V`, `ψ '' V ∩ W = {x ∈ W | g x = 0}` for an
open `W ∋ p` and a `Cⁿ` map `g` with surjective derivative on `W`. -/
theorem forall_mem_image_exists_regularZeroSet {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ψ : F → E} {V : Set F} (hV : IsOpen V) (hψ : ContDiffOn ℝ n ψ V)
    (hind : IsInducing (fun x : V => ψ x)) (hinj : ∀ x ∈ V, Injective (fderiv ℝ ψ x)) :
    ∀ p ∈ ψ '' V, ∃ W : Set E, IsOpen W ∧ p ∈ W ∧
      ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)), ContDiffOn ℝ n g W ∧
        (∀ x ∈ W, Surjective (fderiv ℝ g x)) ∧ ψ '' V ∩ W = {x ∈ W | g x = 0} :=
  exists_inter_eq_regularZeroSet_of_inter_eq_image hn hV hψ hind hinj isOpen_univ (inter_univ _)

end

end
