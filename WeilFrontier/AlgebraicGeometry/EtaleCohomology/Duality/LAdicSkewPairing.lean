module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPairing

/-!
# Alternating perfect ℓ-adic pairings from skew-symmetric pairings of the levels

Let `M` be a finitely generated `ℤ_p`-module with an endomorphism `f`, and suppose that for every
`n` there is a biadditive pairing `e : M × M → ℤ/pⁿ`, skew-symmetric, with `e(f a, f b) = c e(a, b)`
and whose kernel is contained in `p^{n-K}`. Then there is a perfect pairing `B` on `ℚ_p ⊗ M`
with `B(f v, f w) = c B(v, w)` which is alternating: `B(v, v) = 0`.

The proof follows the compactness argument of
`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow`, with the additional
closed condition that the bilinear form of the Gram matrix be skew-symmetric modulo `pⁿ`.

## Main results

* `Weil.LAdicPairing.exists_skew_pairing_of_forall_zmodPow`: the free case, over `ℤ_p`.
* `Weil.LAdicPairing.exists_isPerfPair_of_forall_zmodPow_of_skew`: the perfect alternating
  pairing over `ℚ_p`.
* `Weil.LAdicPairing.exists_isPerfPair_extendScalars_of_levels_of_skew`: the same from
  nondegenerate skew-symmetric pairings on the levels of a tower.

## Implementation notes

A skew-symmetric form `e` modulo `pⁿ` need not lift to a skew-symmetric form over `ℤ_p` with the
same reduction when `p = 2`, since only `2 e(x, x) = 0` holds. We lift instead `2e`, as the
reduction of `J - Jᵀ` for any lift `J` of the Gram matrix of `e`; this costs one power of `p` in
the kernel bound, since `p ∈ 2 ℤ_p`.
-/

@[expose] public noncomputable section

open Matrix

universe v

namespace Weil.LAdicPairing

open Stacks.EtaleCohomology Stacks.EtaleCohomology.LAdicPairing

variable {p : ℕ} [Fact p.Prime]

/-- The prime `p` is divisible by `2` in `ℤ_p`: for `p = 2` trivially, and otherwise because `2`
is a unit. -/
theorem exists_natCast_eq_two_mul : ∃ u : ℤ_[p], (p : ℤ_[p]) = 2 * u := by
  rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
  · subst h
    exact ⟨1, by norm_num⟩
  · have h2 : IsUnit (2 : ℤ_[p]) := by
      have : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.2
        ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 (by
          rintro rfl
          exact (Nat.not_even_iff_odd.2 h) even_two))
      exact PadicInt.isUnit_iff.2 (by exact_mod_cast this)
    obtain ⟨w, hw⟩ := h2
    refine ⟨(w⁻¹ : ℤ_[p]ˣ) * p, ?_⟩
    rw [← mul_assoc, ← hw, Units.mul_inv, one_mul]

section Free

variable {L : Type*} [AddCommGroup L] [Module ℤ_[p] L] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (m : Module.Basis ι ℤ_[p] L)

/-- The bilinear form of the matrix `J` is skew-symmetric modulo `pⁿ`. -/
def IsSkewMod (n : ℕ) (J : Matrix ι ι ℤ_[p]) : Prop :=
  ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J a b) =
    -PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J b a)

/-- `IsSkewMod` only depends on the reduction of the matrix modulo `pⁿ`. -/
theorem isSkewMod_congr {n : ℕ} {J J' : Matrix ι ι ℤ_[p]}
    (hJ : J.map (PadicInt.toZModPow n) = J'.map (PadicInt.toZModPow n))
    (hskew : IsSkewMod m n J) : IsSkewMod m n J' := by
  have h : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J a b) =
      PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J' a b) := fun a b => by
    rw [toZModPow_toLinearMap₂, toZModPow_toLinearMap₂, hJ]
  simpa only [IsSkewMod, h] using hskew

/-- A matrix skew modulo `pⁿ⁺¹` is skew modulo `pⁿ`. -/
theorem isSkewMod_of_succ {n : ℕ} {J : Matrix ι ι ℤ_[p]} (hskew : IsSkewMod m (n + 1) J) :
    IsSkewMod m n J := by
  intro a b
  have hc := congrArg (ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n))) (hskew a b)
  rw [map_neg] at hc
  rwa [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ n.le_succ,
    ← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ n.le_succ] at hc

variable (f : L →ₗ[ℤ_[p]] L) (c K : ℕ)

omit [Fintype ι] [DecidableEq ι] in
include m in
/-- **A skew-symmetric equivariant pairing over `ℤ_p` from skew-symmetric equivariant pairings
modulo every `pⁿ`**, for a module with a finite basis. -/
theorem exists_skew_pairing_of_forall_zmodPow_of_basis [Finite ι]
    (h : ∀ n : ℕ, ∃ e : L →+ L →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ a b, e (f a) (f b) = (c : ZMod (p ^ n)) * e a b) ∧ ∀ a b, e a b = -e b a) :
    ∃ β : L →ₗ[ℤ_[p]] L →ₗ[ℤ_[p]] ℤ_[p], (∀ a, (∀ b, β a b = 0) → a = 0) ∧
      (∀ a b, β (f a) (f b) = c * β a b) ∧ ∀ a b, β a b = -β b a := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨u, hu⟩ := exists_natCast_eq_two_mul (p := p)
  let t : ℕ → Set (Matrix ι ι ℤ_[p]) := fun n =>
    {J | IsGoodMod m m f f c (K + 1) n J ∧ IsSkewMod m n J}
  have hcl : ∀ n, IsClosed (t n) := fun n =>
    isClosed_setOf_of_map_eq n _ fun J J' hJ hJt =>
      ⟨isGoodMod_congr m m f f c (K + 1) hJ hJt.1, isSkewMod_congr m hJ hJt.2⟩
  have hdec : ∀ n, t (n + 1) ⊆ t n := fun n J hJ =>
    ⟨isGoodMod_of_succ m m f f c (K + 1) hJ.1, isSkewMod_of_succ m hJ.2⟩
  have hne : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨e, hl, he, hs⟩ := h n
    have hsurj := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n)
    let J₀ : Matrix ι ι ℤ_[p] := fun i j => Function.surjInv hsurj (e (m i) (m j))
    have hJ₀ : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J₀ a b) = e a b := by
      intro a b
      rw [toZModPow_toLinearMap₂, pairing_eq_sum m m n e a b]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.map_apply]
      exact congrArg _ (Function.surjInv_eq hsurj _)
    let B₀ := Matrix.toLinearMap₂ m m J₀
    let J : Matrix ι ι ℤ_[p] := (Matrix.toLinearMap₂ m m).symm (B₀ - B₀.flip)
    have hJ : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J a b) = 2 * e a b := by
      intro a b
      simp only [J, LinearEquiv.apply_symm_apply, LinearMap.sub_apply, LinearMap.flip_apply,
        map_sub, B₀, hJ₀, hs b a, sub_neg_eq_add, two_mul]
    have hJs : IsSkewMod m n J := fun a b => by rw [hJ, hJ, hs b a, mul_neg, neg_neg]
    have hleft : ∀ a, (∀ b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m J a b) = 0) →
        ∃ a', (p : ℤ_[p]) ^ (K + 1) • a = (p : ℤ_[p]) ^ n • a' := by
      intro a ha
      obtain ⟨a', ha'⟩ := hl (a + a) fun b => by
        rw [map_add, AddMonoidHom.add_apply, ← two_mul, ← hJ]
        exact ha b
      refine ⟨u • a', ?_⟩
      rw [smul_comm _ u, ← ha', ← two_smul ℤ_[p] a, smul_smul, smul_smul]
      congr 1
      rw [pow_succ, hu]
      ring
    refine ⟨J, ⟨hleft, fun b hb => hleft b fun a => ?_, fun a b => ?_⟩, hJs⟩
    · rw [hJs, hb a, neg_zero]
    · rw [hJ, hJ, he, mul_left_comm]
  have : CompactSpace (Matrix ι ι ℤ_[p]) := inferInstanceAs (CompactSpace (ι → ι → ℤ_[p]))
  obtain ⟨J, hJ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hJ
  refine ⟨Matrix.toLinearMap₂ m m J, fun a ha => ?_, fun a b => ?_, fun a b => ?_⟩
  · exact eq_zero_of_forall_pow_smul m (K + 1) a fun n =>
      (hJ n).1.1 a fun b => by rw [ha b, map_zero]
  · rw [← PadicInt.ext_of_toZModPow]
    intro n
    rw [(hJ n).1.2.2 a b, map_mul, map_natCast]
  · rw [← PadicInt.ext_of_toZModPow]
    intro n
    rw [(hJ n).2 a b, map_neg]

end Free

/-- **A skew-symmetric equivariant pairing over `ℤ_p` from skew-symmetric equivariant pairings
modulo every `pⁿ`**, for free `ℤ_p`-modules of finite rank. -/
theorem exists_skew_pairing_of_forall_zmodPow {L : Type*} [AddCommGroup L] [Module ℤ_[p] L]
    [Module.Free ℤ_[p] L] [Module.Finite ℤ_[p] L] (f : L →ₗ[ℤ_[p]] L) (c K : ℕ)
    (h : ∀ n : ℕ, ∃ e : L →+ L →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ a b, e (f a) (f b) = (c : ZMod (p ^ n)) * e a b) ∧ ∀ a b, e a b = -e b a) :
    ∃ β : L →ₗ[ℤ_[p]] L →ₗ[ℤ_[p]] ℤ_[p], (∀ a, (∀ b, β a b = 0) → a = 0) ∧
      (∀ a b, β (f a) (f b) = c * β a b) ∧ ∀ a b, β a b = -β b a := by
  classical
  exact exists_skew_pairing_of_forall_zmodPow_of_basis (Module.Free.chooseBasis ℤ_[p] L) f c K h

section Rational

open TensorProduct

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]

/-- The rational pairing of a skew-symmetric pairing is skew-symmetric. -/
theorem rationalPairing_eq_neg (β : M →ₗ[ℤ_[p]] M →ₗ[ℤ_[p]] ℤ_[p])
    (hβ : ∀ a b, β a b = -β b a) (v w : ℚ_[p] ⊗[ℤ_[p]] M) :
    rationalPairing β v w = -rationalPairing β w v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv', neg_add]
  | tmul x a =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw', neg_add]
    | tmul y b =>
      rw [rationalPairing_tmul, rationalPairing_tmul, hβ, map_neg]
      ring

/-- The rational pairing of a skew-symmetric pairing is alternating. -/
theorem rationalPairing_self_eq_zero (β : M →ₗ[ℤ_[p]] M →ₗ[ℤ_[p]] ℤ_[p])
    (hβ : ∀ a b, β a b = -β b a) (v : ℚ_[p] ⊗[ℤ_[p]] M) : rationalPairing β v v = 0 :=
  self_eq_neg.1 (rationalPairing_eq_neg β hβ v v)

end Rational

section Main

open TensorProduct Submodule

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]

/-- **Alternating Poincaré duality over `ℚ_p` from finite levels.** Let `M` be a finitely
generated `ℤ_p`-module with an endomorphism `f`, and suppose that for every `n` there is a
skew-symmetric biadditive pairing `e : M × M → ℤ/pⁿ` with `e(f a, f b) = c e(a, b)` whose kernel is
contained in `p^{n-K}`. Then there is a perfect pairing `B` on `ℚ_p ⊗ M` with
`B(f v, f w) = c B(v, w)`, skew-symmetric and alternating. -/
theorem exists_isPerfPair_of_forall_zmodPow_of_skew (f : M →ₗ[ℤ_[p]] M) (c K : ℕ)
    (h : ∀ n : ℕ, ∃ e : M →+ M →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ a b, e (f a) (f b) = (c : ZMod (p ^ n)) * e a b) ∧ ∀ a b, e a b = -e b a) :
    ∃ B : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p], B.IsPerfPair ∧
      (∀ v w, B (f.baseChange ℚ_[p] v) (f.baseChange ℚ_[p] w) = (c : ℚ_[p]) * B v w) ∧
      (∀ v w, B v w = -B w v) ∧ ∀ v, B v v = 0 := by
  obtain ⟨k, hkM⟩ := exists_pow_smul_eq_zero_of_mem_torsion (p := p) (M := M)
  set T := torsion ℤ_[p] M
  let σ : M ⧸ T → M := Function.surjInv T.mkQ_surjective
  have hσ : ∀ x, T.mkQ (σ x) = x := Function.surjInv_eq T.mkQ_surjective
  let fbar : M ⧸ T →ₗ[ℤ_[p]] M ⧸ T := T.mapQ T f (torsion_le_comap f)
  have hpk : ∀ {n : ℕ} (e : M →+ M →+ ZMod (p ^ n)) (a b : M),
      e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) =
        e ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • a) b := fun e a b => by
    rw [map_smul_eq_toZModPow_mul (e _)]
    exact (map_smul_eq_toZModPow_mul (e.flip b) _ _).symm
  have hlev : ∀ n : ℕ, ∃ e : M ⧸ T →+ M ⧸ T →+ ZMod (p ^ n),
      (∀ x, (∀ y, e x y = 0) → ∃ x', (p : ℤ_[p]) ^ (K + 2 * k) • x = (p : ℤ_[p]) ^ n • x') ∧
      (∀ x y, e (fbar x) (fbar y) = (c : ZMod (p ^ n)) * e x y) ∧ ∀ x y, e x y = -e y x := by
    intro n
    obtain ⟨e, hl, he, hs⟩ := h n
    let eL : M ⧸ T →+ M ⧸ T →+ ZMod (p ^ n) :=
      AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
        (fun y => e ((p : ℤ_[p]) ^ k • σ x) ((p : ℤ_[p]) ^ k • σ y)) (fun y y' => by
          rw [← map_add, ← smul_add, pow_smul_eq_of_mkQ_eq hkM (a := σ (y + y'))
            (a' := σ y + σ y') (by rw [map_add, hσ, hσ, hσ])]))
        (fun x x' => by
          ext y
          simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
          rw [← AddMonoidHom.add_apply, ← map_add, ← smul_add,
            pow_smul_eq_of_mkQ_eq hkM (a := σ (x + x')) (a' := σ x + σ x')
              (by rw [map_add, hσ, hσ, hσ])])
    have heL : ∀ a b, eL (T.mkQ a) (T.mkQ b) =
        e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) := fun a b => by
      simp only [eL, AddMonoidHom.mk'_apply]
      rw [pow_smul_eq_of_mkQ_eq hkM (hσ _), pow_smul_eq_of_mkQ_eq hkM (hσ _)]
    refine ⟨eL, fun x hx => ?_, fun x y => ?_, fun x y => ?_⟩
    · obtain ⟨a', ha'⟩ := hl ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • σ x) fun b => by
        rw [← hpk, ← heL, hσ]
        exact hx _
      refine ⟨T.mkQ a', ?_⟩
      rw [← hσ x, ← map_smul, ← map_smul, ← ha', smul_smul, smul_smul, ← pow_add, ← pow_add,
        two_mul, ← add_assoc]
    · rw [← hσ x, ← hσ y]
      have h1 : ∀ z, fbar (T.mkQ z) = T.mkQ (f z) := fun _ => rfl
      rw [h1, h1, heL, heL, ← map_smul, ← map_smul, he]
    · simp only [eL, AddMonoidHom.mk'_apply]
      exact hs _ _
  obtain ⟨βbar, hβl, hβe, hβs⟩ :=
    exists_skew_pairing_of_forall_zmodPow fbar c (K + 2 * k) hlev
  let β : M →ₗ[ℤ_[p]] M →ₗ[ℤ_[p]] ℤ_[p] := βbar.compl₁₂ T.mkQ T.mkQ
  have hβ : ∀ a b, β a b = βbar (T.mkQ a) (T.mkQ b) := fun a b => rfl
  have hβskew : ∀ a b, β a b = -β b a := fun a b => by rw [hβ, hβ, hβs]
  have hl : ∀ a, (∀ b, β a b = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • a = 0 := by
    intro a ha
    have h0 : T.mkQ a = 0 := hβl _ fun y => by rw [← hσ y, ← hβ]; exact ha _
    rw [mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨s, hs⟩ := (mem_torsion_iff a).1 h0
    exact ⟨s, nonZeroDivisors.ne_zero s.2, hs⟩
  have hr : ∀ b, (∀ a, β.flip b a = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • b = 0 := fun b hb =>
    hl b fun a => by rw [hβskew, ← LinearMap.flip_apply β, hb a, neg_zero]
  refine ⟨rationalPairing β, ?_, ?_, rationalPairing_eq_neg β hβskew,
    rationalPairing_self_eq_zero β hβskew⟩
  · refine LinearMap.IsPerfPair.of_injective ?_ ?_
    · rw [injective_iff_map_eq_zero]
      intro v hv
      exact eq_zero_of_rationalPairing_eq_zero β hl v fun w => by rw [hv]; rfl
    · rw [injective_iff_map_eq_zero, rationalPairing_flip]
      intro w hw
      exact eq_zero_of_rationalPairing_eq_zero β.flip hr w fun v => by rw [hw]; rfl
  · intro v w
    refine rationalPairing_baseChange_baseChange β f f c (fun a b => ?_) v w
    have : β (f a) (f b) = c * β a b := by
      rw [hβ, hβ]
      exact hβe (T.mkQ a) (T.mkQ b)
    rw [this, map_mul, map_natCast]

end Main

/-- **An alternating perfect `ℚ_p`-pairing from skew-symmetric perfect pairings of the levels of
a tower.** If the projections `πₙ : M → Hₙ` have kernel in `pⁿ⁺¹ M` and image containing
`p^K Hₙ`, and the levels carry skew-symmetric pairings `εₙ` with values in `ℤ/pⁿ⁺¹`,
nondegenerate and scaled by `c` under endomorphisms `φₙ` over `f`, then there is a perfect
pairing `B` of `M ⊗ ℚ_p` with itself, with `B (f v) (f w) = c B(v, w)` and `B(v, v) = 0`. -/
theorem exists_isPerfPair_extendScalars_of_levels_of_skew {M : ModuleCat.{v} ℤ_[p]}
    [Module.Finite ℤ_[p] M] (f : M ⟶ M) (c K : ℕ)
    {H : ℕ → Type*} [∀ n, AddCommGroup (H n)]
    (π : ∀ n, M →+ H n) (φ : ∀ n, H n →+ H n)
    (hπ : ∀ n a, π n (f.hom a) = φ n (π n a))
    (hker : ∀ n a, π n a = 0 → ∃ a', a = (p ^ (n + 1)) • a')
    (hrange : ∀ n (y : H n), ∃ a, π n a = (p ^ K) • y)
    (ε : ∀ n, H n →+ H n →+ ZMod (p ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → x = 0)
    (hε : ∀ n x y, ε n (φ n x) (φ n y) = (c : ZMod (p ^ (n + 1))) * ε n x y)
    (hskew : ∀ n x y, ε n x y = -ε n y x) :
    ∃ B : (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M →ₗ[ℚ_[p]]
        (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M →ₗ[ℚ_[p]] ℚ_[p],
      B.IsPerfPair ∧ (∀ v w,
        B (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map f).hom v)
          (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map f).hom w) =
          (c : ℚ_[p]) * B v w) ∧ ∀ v, B v v = 0 := by
  obtain ⟨B, hB, hBf, -, hBa⟩ := exists_isPerfPair_of_forall_zmodPow_of_skew f.hom c K
    fun n => by
      cases n with
      | zero =>
        refine ⟨0, fun a _ => ⟨(p : ℤ_[p]) ^ K • a, by rw [pow_zero, one_smul]⟩,
          fun a b => ?_, fun a b => ?_⟩
        · simp only [AddMonoidHom.zero_apply, mul_zero]
        · simp only [AddMonoidHom.zero_apply, neg_zero]
      | succ m =>
        refine ⟨((ε m).compl₂ (π m)).comp (π m), ?_, fun a b => ?_, fun a b => ?_⟩
        · intro a ha
          have h0 : π m ((p ^ K) • a) = 0 := by
            refine hl m _ fun y => ?_
            obtain ⟨b, hb⟩ := hrange m y
            simpa only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, hb, map_nsmul,
              AddMonoidHom.nsmul_apply] using ha b
          obtain ⟨a', ha'⟩ := hker m _ h0
          exact ⟨a', by simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using ha'⟩
        · simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, hπ]
          exact hε m _ _
        · simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply]
          exact hskew m _ _
  exact ⟨B, hB, hBf, hBa⟩

end Weil.LAdicPairing
