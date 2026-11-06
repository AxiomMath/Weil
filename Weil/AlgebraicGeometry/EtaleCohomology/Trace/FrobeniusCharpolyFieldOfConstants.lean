module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionCharpolyRoots
public import Weil.Attr

/-!
# Frobenius characteristic polynomials over a clopen decomposition, and cyclic endomorphisms

Let `X` be a separated scheme of finite type over a finite field `k`, compactified by
`j : X ⟶ X̄`, let `F` be an ℓ-adic sheaf on `X`, and let `X = U ⊔ Z` with `U` and `Z` open and
closed subschemes, compactified by the induced compactifications. Then the characteristic
polynomial of the geometric Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the product of those on
`Hⁱ_c(U_k̄, F_U ⊗ ℚ_ℓ)` and `Hⁱ_c(Z_k̄, F_Z ⊗ ℚ_ℓ)`.

For an open immersion `j_U : U ⟶ X` with complementary closed immersion `i_Z : Z ⟶ X` the
excision sequence `Hⁱ_c(X_k̄, j_{U!} j_U⁻¹ G) → Hⁱ_c(X_k̄, G) → Hⁱ_c(X_k̄, i_{Z*} i_Z⁻¹ G)` is only
exact in the middle. When `U` is also closed, the comparison `j_{U!} j_U⁻¹ G ⟶ j_{U*} j_U⁻¹ G`
(the counit of `j_! ⊣ j⁻¹` followed by the unit of `j⁻¹ ⊣ j_*`) is an isomorphism, which
splits the first map; when `Z` is also open the same comparison for `Z` splits the second map.
So the sequence is a split short exact sequence compatible with the Frobenius in every degree,
and the characteristic polynomial is multiplicative.

The second part is the linear algebra of the field of constants. If `X` is a scheme over a finite
field `k` whose structure morphism factors through `Spec k'` for an extension `k'` of degree `r`,
then `Hⁱ(X ⊗_k k̄) = ⨁_τ Hⁱ(X ⊗_{k', τ} k̄)` over the `r` embeddings `τ : k' → k̄`, the Frobenius
permutes the `r` summands cyclically, and its `r`-th power on one summand is the Frobenius of `X`
over `k'`. For an endomorphism `φ` of `V = ⨁_{a ∈ ℤ/r} W a` with `φ (W a) ⊆ W (a + 1)` one has
`det (1 - t φ) = det (1 - t ^ r φ ^ r |_{W 0})`: write `φ = φ' + ω` with `ω = φ ∘ P₀`, `P₀` the
projection onto `W 0`; then `φ'` is nilpotent and
`1 - φ = (1 - φ') (1 - (∑_{k < r} φ' ^ k) ω)`, and the second factor is the identity on the
complement of `W 0` and induces `1 - φ ^ r` on the quotient, which is `W 0`.

## Main results

* `Weil.LinearMap.charpoly_eq_mul_of_exact_of_retraction`: the characteristic polynomial is
  multiplicative along an equivariant exact sequence `A → B → C` with an equivariant retraction
  of `A → B` and `B → C` surjective.
* `Weil.det_one_sub_eq_det_one_sub_pow_restrict_of_cyclic`: for `φ (W a) ⊆ W (a + 1)`,
  `det (1 - φ) = det (1 - φ ^ r |_{W 0})`.
* `Weil.reverse_charpoly_eq_comp_of_cyclic`: the reverse characteristic polynomial of such a `φ`
  is that of `φ ^ r |_{W 0}` evaluated at `X ^ r`.
* `Weil.isIso_etaleModuleOpenPartToClosedPart_app`: for an open and closed immersion
  `j : V ⟶ X`, `j_! j⁻¹ G ⟶ j_* j⁻¹ G` is an isomorphism.
* `Weil.LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_mul_of_isClopen`:
  multiplicativity of the Frobenius characteristic polynomial over a clopen decomposition.

## Implementation notes

`Weil.reverse_charpoly_eq_comp_of_cyclic` is stated over an infinite field (it is used over
`ℚ_ℓ`): the polynomial identity is checked at every point.
`ProjectiveDeterminant.det_one_sub_smul_inducedEnd` is the special case of a cyclic shift of
`r` copies of one module.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.EtaleCohomology

universe u

namespace Weil

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### Linear algebra -/

section LinearAlgebra

variable {K : Type*} [Field K] {A B C : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B]
  [Module K B] [AddCommGroup C] [Module K C] [FiniteDimensional K A] [FiniteDimensional K B]
  [FiniteDimensional K C]

/-- **The characteristic polynomial along a split exact sequence.** Let `a : A → B`, `b : B → C`
be an exact sequence of finite-dimensional vector spaces, `r : B → A` a retraction of `a` and `b`
surjective, all intertwining endomorphisms `φA`, `φB`, `φC`. Then
`charpoly φB = charpoly φA * charpoly φC`. -/
theorem LinearMap.charpoly_eq_mul_of_exact_of_retraction {φA : Module.End K A}
    {φB : Module.End K B} {φC : Module.End K C} {a : A →ₗ[K] B} {b : B →ₗ[K] C} {r : B →ₗ[K] A}
    (hexact : Function.Exact a b) (hra : ∀ x, r (a x) = x) (hb : Function.Surjective b)
    (hr : ∀ y, r (φB y) = φA (r y)) (hbφ : ∀ y, b (φB y) = φC (b y)) :
    φB.charpoly = φA.charpoly * φC.charpoly := by
  let e₀ : B →ₗ[K] A × C := r.prod b
  have ha : Function.Injective a := Function.LeftInverse.injective hra
  have hinj : Function.Injective e₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : r y = 0 := congrArg Prod.fst hy
    have h2 : b y = 0 := congrArg Prod.snd hy
    obtain ⟨x, rfl⟩ := (hexact y).1 h2
    rw [hra] at h1
    rw [h1, map_zero]
  have hdim : Module.finrank K B = Module.finrank K (A × C) := by
    rw [Module.finrank_prod, ← b.finrank_range_add_finrank_ker, LinearMap.range_eq_top.2 hb,
      finrank_top, add_comm]
    congr 1
    have hk : LinearMap.ker b = LinearMap.range a := by
      ext y
      exact (hexact y)
    rw [hk, LinearMap.finrank_range_of_inj ha]
  have hbij : Function.Bijective e₀ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  let e : B ≃ₗ[K] A × C := LinearEquiv.ofBijective e₀ hbij
  have hconj : e.conj φB = φA.prodMap φC := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    change e₀ (φB y) = (φA.prodMap φC) (e₀ y)
    exact Prod.ext (hr y) (hbφ y)
  rw [← LinearMap.charpoly_prodMap, ← hconj, LinearEquiv.charpoly_conj]

end LinearAlgebra

/-! ### Cyclic endomorphisms -/

section Cyclic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The reverse characteristic polynomial evaluated at `c` is `det (1 - c f)`. -/
theorem LinearMap.eval_reverse_charpoly (f : Module.End K V) (c : K) :
    f.charpoly.reverse.eval c = LinearMap.det (1 - c • f) := by
  let b := Module.Free.chooseBasis K V
  rw [LinearMap.charpoly_def, Matrix.reverse_charpoly, Matrix.charpolyRev,
    ← Polynomial.coe_evalRingHom, RingHom.map_det, ← LinearMap.det_toMatrix b]
  congr 1
  ext i j
  simp [Matrix.one_apply, LinearMap.toMatrix_one, map_sub, map_smul, b]
  ring

variable {r : ℕ} (W : ZMod r → Submodule K V) (φ : Module.End K V)
  (hφ : ∀ a, ∀ v ∈ W a, φ v ∈ W (a + 1))

omit [FiniteDimensional K V] in
include hφ in
theorem pow_apply_mem_of_cyclic (n : ℕ) : ∀ a, ∀ v ∈ W a, (φ ^ n) v ∈ W (a + n) := by
  induction n with
  | zero => intro a v hv; simpa using hv
  | succ n ih =>
    intro a v hv
    rw [pow_succ, Module.End.mul_apply]
    have := ih (a + 1) (φ v) (hφ a v hv)
    rwa [Nat.cast_succ, add_comm (n : ZMod r) 1, ← add_assoc]

omit [FiniteDimensional K V] in
include hφ in
theorem pow_apply_mem_zero_of_cyclic : ∀ v ∈ W 0, (φ ^ r) v ∈ W 0 := fun v hv => by
  simpa using pow_apply_mem_of_cyclic W φ hφ r 0 v hv

omit [FiniteDimensional K V] in
include hφ in
/-- The part `φ' = φ ∘ (1 - P₀)` of a cyclic `φ` killing `W 0` is nilpotent: `φ' ^ r = 0`. -/
theorem pow_comp_sub_projection_eq_zero_of_cyclic [NeZero r] (hW : DirectSum.IsInternal W)
    (hc : IsCompl (W 0) (⨆ (a) (_ : a ≠ 0), W a)) :
    (φ * (1 - (W 0).projection _ hc)) ^ r = 0 := by
  set ψ := φ * (1 - (W 0).projection _ hc)
  have hP0 : ∀ v ∈ W 0, ψ v = 0 := fun v hv => by
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.projection_apply_of_mem_left hc hv, sub_self, map_zero]
  have hPa : ∀ a, a ≠ 0 → ∀ v ∈ W a, ψ v = φ v := fun a ha v hv => by
    have hv' : v ∈ ⨆ (a) (_ : a ≠ 0), W a := (le_iSup₂ (f := fun a (_ : a ≠ 0) => W a) a ha) hv
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.projection_apply_of_mem_right hc hv', sub_zero]
  have hψ : ∀ a, ∀ v ∈ W a, ψ v ∈ W (a + 1) := fun a v hv => by
    by_cases ha : a = 0
    · rw [hP0 v (ha ▸ hv)]; exact zero_mem _
    · rw [hPa a ha v hv]; exact hφ a v hv
  have hv : ∀ a, ∀ v ∈ W a, (ψ ^ r) v = 0 := fun a v hv => by
    by_cases ha : a = 0
    · subst ha
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne r)
      rw [hn, pow_succ, Module.End.mul_apply, hP0 v hv, map_zero]
    · have hlt := ZMod.val_lt a
      have hpos : 0 < a.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).2 ha)
      have hmem := pow_apply_mem_of_cyclic W ψ hψ (r - a.val) a v hv
      have hz : a + ((r - a.val : ℕ) : ZMod r) = 0 := by
        have h1 : ((a.val + (r - a.val) : ℕ) : ZMod r) = 0 := by
          rw [Nat.add_sub_cancel' hlt.le, ZMod.natCast_self]
        rwa [Nat.cast_add, ZMod.natCast_zmod_val] at h1
      rw [hz] at hmem
      have hr : r = (r - (r - a.val + 1)) + 1 + (r - a.val) := by omega
      rw [hr, pow_add, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hP0 _ hmem,
        map_zero]
  refine LinearMap.ext fun v => ?_
  have hvtop : v ∈ ⨆ a, W a := by rw [hW.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W (motive := fun v => (ψ ^ r) v = 0) hvtop
    (fun a v hv' => by simpa using hv a v hv') (by simp) (fun x y hx hy => by simp_all)

omit [FiniteDimensional K V] in
/-- The pieces `W a`, `a ≠ 0`, of a direct sum decomposition span a complement of `W 0`. -/
theorem isCompl_iSup_ne_zero [NeZero r] (hW : DirectSum.IsInternal W) :
    IsCompl (W 0) (⨆ (a) (_ : a ≠ 0), W a) := by
  refine ⟨hW.submodule_iSupIndep 0, codisjoint_iff.2 ?_⟩
  rw [← iSup_split_single W 0, hW.submodule_iSup_eq_top]

include hφ in
/-- **`det (1 - φ) = det (1 - φ ^ r |_{W 0})` for a cyclic `φ`.** -/
theorem det_one_sub_eq_det_one_sub_pow_restrict_of_cyclic [NeZero r]
    (hW : DirectSum.IsInternal W) :
    LinearMap.det (1 - φ) =
      LinearMap.det (1 - (φ ^ r).restrict (pow_apply_mem_zero_of_cyclic W φ hφ)) := by
  have hc := isCompl_iSup_ne_zero W hW
  set W' := ⨆ (a) (_ : a ≠ 0), W a
  set P := (W 0).projection W' hc
  set φ' := φ * (1 - P)
  set ω := φ * P
  set S := ∑ k ∈ Finset.range r, φ' ^ k
  have hP0 : ∀ v ∈ W 0, P v = v := fun v hv => Submodule.projection_apply_of_mem_left hc hv
  have hP' : ∀ v ∈ W', P v = 0 := fun v hv => Submodule.projection_apply_of_mem_right hc hv
  have hnil : φ' ^ r = 0 := pow_comp_sub_projection_eq_zero_of_cyclic W φ hφ hW hc
  have hPa : ∀ a, a ≠ 0 → ∀ v ∈ W a, φ' v = φ v := fun a ha v hv => by
    have hv' : v ∈ W' := (le_iSup₂ (f := fun a (_ : a ≠ 0) => W a) a ha) hv
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.projection_apply_of_mem_right hc hv', sub_zero]
  -- `1 - φ = (1 - φ') (1 - S ω)`
  have h1 : 1 - φ = (1 - φ') * (1 - S * ω) := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_neg_geom_sum, hnil, sub_zero, one_mul]
    simp only [φ', ω, mul_sub, mul_one]
    abel
  have h2 : LinearMap.det (1 - φ') = 1 := by
    have h := LinearMap.eval_charpoly φ' 1
    rw [(show IsNilpotent φ' from ⟨r, hnil⟩).charpoly_eq_X_pow_finrank, eval_pow, eval_X, one_pow,
      map_one] at h
    exact h.symm
  rw [h1, map_mul, h2, one_mul]
  -- `1 - S ω` is the identity on `W'`
  set E := 1 - S * ω
  have hE : ∀ v ∈ W', E v = v := fun v hv => by
    change v - S (φ (P v)) = v
    rw [hP' v hv, map_zero, map_zero, sub_zero]
  have hle : W' ≤ W'.comap E := fun v hv => by
    rw [Submodule.mem_comap, hE v hv]; exact hv
  rw [LinearMap.det_eq_det_mul_det W' E hle]
  have hres : E.restrict hle = LinearMap.id := LinearMap.ext fun v => Subtype.ext (hE v v.2)
  rw [hres, LinearMap.det_id, one_mul]
  -- the map induced on `V ⧸ W' ≅ W 0`
  let e := Submodule.quotientEquivOfIsCompl W' (W 0) hc.symm
  rw [← LinearMap.det_conj (W'.mapQ W' E hle) e]
  congr 1
  refine LinearMap.ext fun w => Subtype.ext ?_
  -- the powers of `φ'` on `φ w`
  have hpow : ∀ k, k < r → (φ' ^ k) (φ w) = (φ ^ (k + 1)) w := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [pow_succ', Module.End.mul_apply, ih (by omega)]
      have hmem := pow_apply_mem_of_cyclic W φ hφ (k + 1) 0 w w.2
      rw [zero_add] at hmem
      have hne : ((k + 1 : ℕ) : ZMod r) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => absurd (Nat.le_of_dvd (Nat.succ_pos k) h) (by omega)
      rw [hPa _ hne _ hmem, pow_succ' φ (k + 1), Module.End.mul_apply]
  have hproj : P (S (ω w)) = (φ ^ r) w := by
    have hω : ω w = φ w := by
      change φ (P w) = φ w
      rw [hP0 _ w.2]
    have hr0 := NeZero.ne r
    obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    rw [hω, LinearMap.sum_apply, map_sum, show Finset.range r = Finset.range (n + 1) by rw [hn],
      Finset.sum_range_succ]
    have hlast := pow_apply_mem_of_cyclic W φ hφ (n + 1) 0 w w.2
    rw [zero_add, ← hn, ZMod.natCast_self] at hlast
    rw [hpow n (by omega), ← hn, hP0 _ hlast]
    rw [Finset.sum_eq_zero, zero_add]
    intro k hk
    rw [Finset.mem_range] at hk
    have hmem := pow_apply_mem_of_cyclic W φ hφ (k + 1) 0 w w.2
    rw [zero_add] at hmem
    have hne : ((k + 1 : ℕ) : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd (Nat.succ_pos k) h) (by omega)
    rw [hpow k (by omega)]
    exact hP' _ ((le_iSup₂ (f := fun a (_ : a ≠ 0) => W a) _ hne) hmem)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e,
    Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.coe_projectionOnto_apply,
    LinearMap.sub_apply, Module.End.one_apply, LinearMap.restrict_apply, Submodule.coe_sub]
  have hEw : E w = w - S (ω w) := rfl
  rw [hEw, map_sub, hP0 _ w.2, hproj]

include hφ in
/-- **The reverse characteristic polynomial of a cyclic endomorphism.** Let
`V = ⨁_{a ∈ ℤ/r} W a` and `φ` an endomorphism with `φ (W a) ⊆ W (a + 1)`. Then
`det (1 - t φ) = det (1 - t ^ r φ ^ r |_{W 0})`, that is, the reverse characteristic polynomial of
`φ` is that of `φ ^ r` on `W 0` evaluated at `t ^ r`. -/
theorem reverse_charpoly_eq_comp_of_cyclic [Infinite K] [NeZero r]
    (hW : DirectSum.IsInternal W) :
    φ.charpoly.reverse =
      ((φ ^ r).restrict (pow_apply_mem_zero_of_cyclic W φ hφ)).charpoly.reverse.comp
        (Polynomial.X ^ r) := by
  refine Polynomial.funext fun c => ?_
  have hφc : ∀ a, ∀ v ∈ W a, (c • φ) v ∈ W (a + 1) := fun a v hv =>
    Submodule.smul_mem _ c (hφ a v hv)
  rw [eval_comp, eval_pow, eval_X, LinearMap.eval_reverse_charpoly,
    LinearMap.eval_reverse_charpoly,
    det_one_sub_eq_det_one_sub_pow_restrict_of_cyclic W (c • φ) hφc hW]
  congr 2
  ext w
  simp [_root_.smul_pow]

end Cyclic

/-! ### Towers -/

section Tower

variable {ℓ : ℕ} [Fact ℓ.Prime] [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{u} ℤ_[ℓ])]
  {A B C : ℕᵒᵖ ⥤ ModuleCat.{u} ℤ_[ℓ]}

/-- **Characteristic polynomials along a split exact sequence of towers.** Let `α : A ⟶ B`,
`β : B ⟶ C` be maps of towers of `ℤ_ℓ`-modules, exact at every level, with every `A n` finite,
`ρ : B ⟶ A` a retraction of `α` and `σ : C ⟶ B` a section of `β`, intertwining endomorphisms
`φA`, `φB`, `φC`. On the rational limits, the characteristic polynomial of `φB` is the product of
those of `φA` and `φC`. -/
theorem charpoly_rationalLimMap_eq_mul_of_split (α : A ⟶ B) (β : B ⟶ C) (ρ : B ⟶ A)
    (σ : C ⟶ B) (hαρ : α ≫ ρ = 𝟙 A) (hσβ : σ ≫ β = 𝟙 C)
    (hex : ∀ n, Function.Exact (α.app n) (β.app n)) (hfin : ∀ n, Finite (A.obj n))
    (φA : A ⟶ A) (φB : B ⟶ B) (φC : C ⟶ C) (hρ : φB ≫ ρ = ρ ≫ φA) (hβ : φB ≫ β = β ≫ φC)
    [hA : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u} (ℓ := ℓ)).obj A)]
    [hB : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u} (ℓ := ℓ)).obj B)]
    [hC : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u} (ℓ := ℓ)).obj C)] :
    ((rationalLim.{u} (ℓ := ℓ)).map φB).hom.charpoly =
      ((rationalLim.{u} (ℓ := ℓ)).map φA).hom.charpoly *
        ((rationalLim.{u} (ℓ := ℓ)).map φC).hom.charpoly := by
  set R := rationalLim.{u} (ℓ := ℓ)
  have hcomp : ∀ {P Q S : ℕᵒᵖ ⥤ ModuleCat.{u} ℤ_[ℓ]} (f : P ⟶ Q) (g : Q ⟶ S) (x : R.obj P),
      (R.map g).hom ((R.map f).hom x) = (R.map (f ≫ g)).hom x := fun f g x => by
    rw [Functor.map_comp]; rfl
  refine LinearMap.charpoly_eq_mul_of_exact_of_retraction (a := (R.map α).hom)
    (b := (R.map β).hom) (r := (R.map ρ).hom) (exact_rationalLimMap_of_finite α β hex hfin)
    (fun x => by rw [hcomp, hαρ, CategoryTheory.Functor.map_id]; rfl)
    (fun z => ⟨(R.map σ).hom z, by rw [hcomp, hσβ, CategoryTheory.Functor.map_id]; rfl⟩)
    (fun y => by rw [hcomp, hcomp, hρ]) (fun y => by rw [hcomp, hcomp, hβ])

end Tower

/-! ### Open and closed immersions -/

section OpenClosed

variable (Λ : Type) [Ring Λ] {V W X : Scheme.{u}} (jV : V ⟶ X) [IsOpenImmersion jV]
  [IsClosedImmersion jV] (jW : W ⟶ X) [IsOpenImmersion jW]
  (hVW : Set.range jW.base = (Set.range jV.base)ᶜ)

/-- The comparison `j_! j⁻¹ ⟶ j_* j⁻¹` of sheaves of `Λ`-modules on `X_étale` for an open and
closed immersion `j : V ⟶ X`: the counit of `j_! ⊣ j⁻¹` followed by the unit of `j⁻¹ ⊣ j_*`. -/
abbrev etaleModuleOpenPartToClosedPart :
    etaleModuleOpenPart Λ jV ⟶ etaleModuleClosedPart Λ jV :=
  (etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).counit ≫
    (etaleModuleInverseImageAdj.{u, 0} Λ jV).unit

include hVW in
/-- **For an open and closed immersion `j : V ⟶ X`, `j_! j⁻¹ G ⟶ j_* j⁻¹ G` is an
isomorphism**: after `j⁻¹` it is the composite of two isomorphisms, and after inverse image to
the complement `W` both sides vanish. -/
theorem isIso_etaleModuleOpenPartToClosedPart_app (G : EtaleModules.{u, 0} Λ X) :
    IsIso ((etaleModuleOpenPartToClosedPart Λ jV).app G) := by
  have hd : Disjoint (Set.range jW.base) (Set.range jV.base) := by
    rw [hVW]; exact disjoint_compl_left
  have : IsIso ((etaleModuleInverseImage.{u, 0} Λ jV).map
      ((etaleModuleOpenPartToClosedPart Λ jV).app G)) := by
    simp only [NatTrans.comp_app, Functor.map_comp]
    have := isIso_etaleModuleInverseImage_map_unit.{u, 0} Λ jV G
    have : IsIso ((etaleModuleInverseImage.{u, 0} Λ jV).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).counit.app G)) :=
      (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jV) _).mpr
        (isIso_etaleModuleRestriction_map_counit.{u, 0} Λ jV G)
    infer_instance
  have : IsIso ((etaleModuleInverseImage.{u, 0} Λ jW).map
      ((etaleModuleOpenPartToClosedPart Λ jV).app G)) := by
    refine isIso_of_source_target_iso_zero _
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint.{u, 0} Λ jW jV hd _).isoZero
      ?_
    exact (IsZero.of_iso (isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint.{u, 0}
      Λ jV jW hd.symm _) ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jW).app _)).isoZero
  exact isIso_of_isIso_etaleModuleInverseImage.{u, 0} Λ jV jW hVW _

include hVW in
theorem isIso_etaleModuleOpenPartToClosedPart :
    IsIso (etaleModuleOpenPartToClosedPart Λ jV) :=
  have := isIso_etaleModuleOpenPartToClosedPart_app Λ jV jW hVW
  NatIso.isIso_of_isIso_app _

end OpenClosed

/-! ### Excision for ℓ-adic sheaves over a clopen decomposition -/

section LAdic

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X : B.Scheme} [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Multiplicativity of the Frobenius characteristic polynomial over a clopen decomposition.**
Let `X = U ⊔ Z` with `j_U : U ⟶ X` and `i_Z : Z ⟶ X` open and closed immersions with
complementary images, compactified by the compactifications induced by `j`, and let `F_U`, `F_Z`
be ℓ-adic sheaves on `U` and `Z` whose towers of levels are identified with the inverse images
of the tower of levels of `F`. Then the characteristic polynomial of the geometric Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the product of the ones on `Hⁱ_c(U_k̄, F_U ⊗ ℚ_ℓ)` and on
`Hⁱ_c(Z_k̄, F_Z ⊗ ℚ_ℓ)`. The groups `Hⁱ_c(U_k̄, F_U,ₙ)` at the finite levels are assumed
finite. -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_mul_of_isClopen
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) {U Z : B.Scheme} [IsNoetherian U.1]
    [IsNoetherian Z.1] (jU : U ⟶ X) (iZ : Z ⟶ X) [IsOpenImmersion (B.inclusion.map jU)]
    [IsClosedImmersion (B.inclusion.map jU)] [IsOpenImmersion (B.inclusion.map iZ)]
    [IsClosedImmersion (B.inclusion.map iZ)] [QuasiCompact (B.inclusion.map jU ≫ f)]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (FU : LAdicSheaf.{u, u + 1} B U ℓ) (FZ : LAdicSheaf.{u, u + 1} B Z ℓ)
    (eU : LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map jU) ≅ LAdicSheaf.padicTower B U ℓ FU)
    (eZ : LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map iZ) ≅ LAdicSheaf.padicTower B Z ℓ FZ)
    (hfin : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map jU ≫ f)
      (j.restrictOpen (B.inclusion.map jU)) kbar i).obj ((LAdicSheaf.padicTower B U ℓ FU).obj n)))
    [hX : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [hU : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar FU i)]
    [hZ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar FZ i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar p q hcard FU i).hom.charpoly *
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar p q hcard FZ i).hom.charpoly := by
  set jU' := B.inclusion.map jU
  set iZ' := B.inclusion.map iZ
  set T := LAdicSheaf.padicTower B X ℓ F
  set H := compactSupportSheafCohomology ℤ_[ℓ] f j kbar i
  -- the rational limits of the towers of `X`, `U` and `Z`
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)) := hX
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B U ℓ (jU' ≫ f) (j.restrictOpen jU')
        kbar FU i)) := hU
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B Z ℓ (iZ' ≫ f)
        (j.restrictClosed iZ') kbar FZ i)) := hZ
  have hXT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj (T ⋙ H)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).symm
  have hUT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B U ℓ FU ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B U ℓ (jU' ≫ f) (j.restrictOpen jU') kbar FU i).symm
  have hZT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B Z ℓ FZ ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B Z ℓ (iZ' ≫ f) (j.restrictClosed iZ') kbar FZ i).symm
  -- the open and closed parts of the tower of `X`, read on `U` and `Z`
  let eU' : T ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU' ≅ LAdicSheaf.padicTower B U ℓ FU :=
    Functor.isoWhiskerLeft T (etaleModuleInverseImageRestrictionIso.{u, 0} ℤ_[ℓ] jU').symm ≪≫ eU
  let EU := towerOpenPartCohomologyIso f j kbar jU' T i ≪≫ Functor.isoWhiskerRight eU'
    (compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)
  let EZ := towerClosedPartCohomologyIso f j kbar iZ' T i ≪≫ Functor.isoWhiskerRight eZ
    (compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)
  have hfin' : ∀ n, Finite (H.obj ((etaleModuleOpenPart ℤ_[ℓ] jU').obj (T.obj n))) := fun n =>
    @Finite.of_equiv _ _ (hfin n) (EU.app n).toLinearEquiv.toEquiv.symm
  have hA : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU') ⋙ H)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EU.symm (hA := hUT)
  have hC : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ') ⋙ H)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EZ.symm (hA := hZT)
  rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap B ℓ f j
    kbar p q hcard F i]
  have hU' : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (jU' ≫ f)
      (j.restrictOpen jU') kbar p q hcard FU i).hom.charpoly =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU')
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom.charpoly :=
    (LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap B ℓ
      (jU' ≫ f) (j.restrictOpen jU') kbar p q hcard FU i).trans
      (charpoly_rationalLimMap_eq_of_iso.{u + 1} EU _ _ (comp_trans_hom_eq_of_comm _ _ _ _ _
        (towerOpenPartCohomologyIso_hom_frobenius f j kbar p q hcard jU' T i)
        (whiskerLeft_comp_isoWhiskerRight_hom_of_tower eU' _)) (hA := hA) (hA' := hUT))
  have hZ' : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (iZ' ≫ f)
      (j.restrictClosed iZ') kbar p q hcard FZ i).hom.charpoly =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ')
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom.charpoly :=
    (LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap B ℓ
      (iZ' ≫ f) (j.restrictClosed iZ') kbar p q hcard FZ i).trans
      (charpoly_rationalLimMap_eq_of_iso.{u + 1} EZ _ _ (comp_trans_hom_eq_of_comm _ _ _ _ _
        (towerClosedPartCohomologyIso_hom_frobenius f j kbar p q hcard iZ' T i)
        (whiskerLeft_comp_isoWhiskerRight_hom_of_tower eZ _)) (hA := hC) (hA' := hZT))
  rw [hU', hZ']
  -- the splittings
  have hUZ : Set.range iZ'.base = (Set.range jU'.base)ᶜ := by rw [hij, compl_compl]
  have hεU := isIso_etaleModuleOpenPartToClosedPart ℤ_[ℓ] jU' iZ' hUZ
  have hεZ := isIso_etaleModuleOpenPartToClosedPart ℤ_[ℓ] iZ' jU' hij
  let ρ₀ : 𝟭 _ ⟶ etaleModuleOpenPart ℤ_[ℓ] jU' :=
    (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] jU').unit ≫
      inv (etaleModuleOpenPartToClosedPart ℤ_[ℓ] jU')
  let σ₀ : etaleModuleClosedPart ℤ_[ℓ] iZ' ⟶ 𝟭 _ :=
    inv (etaleModuleOpenPartToClosedPart ℤ_[ℓ] iZ') ≫
      (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] iZ').counit
  have hρ₀ : (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jU').counit ≫ ρ₀ = 𝟙 _ := by
    simp only [ρ₀, ← Category.assoc]
    exact IsIso.hom_inv_id _
  have hσ₀ : σ₀ ≫ (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] iZ').unit = 𝟙 _ := by
    simp only [σ₀, Category.assoc]
    exact IsIso.inv_hom_id _
  refine charpoly_rationalLimMap_eq_mul_of_split.{u + 1}
    (Functor.whiskerLeft T (Functor.whiskerRight
      (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jU').counit H))
    (Functor.whiskerLeft T (Functor.whiskerRight
      (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] iZ').unit H))
    (Functor.whiskerLeft T (Functor.whiskerRight ρ₀ H))
    (Functor.whiskerLeft T (Functor.whiskerRight σ₀ H)) ?_ ?_
    (fun n => exact_compactSupportSheafCohomology_openClosed ℤ_[ℓ] f j kbar iZ' jU' hij (T.obj n) i)
    hfin' _ _ _ ?_ ?_ (hA := hA) (hB := hXT) (hC := hC)
  · rw [← Functor.whiskerLeft_comp, ← Functor.whiskerRight_comp, hρ₀]
    ext n; simp
  · rw [← Functor.whiskerLeft_comp, ← Functor.whiskerRight_comp, hσ₀]
    ext n; simp
  all_goals
    refine NatTrans.ext (funext fun n => ?_)
    first
    | exact ((compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i).naturality
        (ρ₀.app (T.obj n))).symm
    | exact ((compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i).naturality
        ((etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] iZ').unit.app (T.obj n))).symm

end LAdic

end Weil

end
