module

public import Weil.Attr
public import WeilFrontier.Defs.LinearAlgebra.PerfectPairing.Basic
public import WeilFrontier.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Eigenvalue multiplicities of an alternating twisted-equivariant duality

Let `F` be an endomorphism of a finite-dimensional vector space `V` over a field `K`, let `c ∈ Kˣ`
and let `β` be an alternating `c`-duality for `(F, F)`: `β x x = 0`, `x ↦ β x ·` is injective and
`β (F x) (F y) = c β x y`. If `γ` is a square root of `c` in some field extension `L` of `K`, then
the multiplicity of `γ` as a root of the characteristic polynomial of `F` is even.

When `γ ∈ K`, write `T = F - γ`. The identity `β (T x) (F y) = -γ β x (T y)` iterates to
`β (Tᵏ x) (Fᵏ y) = (-γ)ᵏ β x (Tᵏ y)`, so the maximal generalized eigenspace `ker T^∞` is
orthogonal to the Fitting complement `⋂ₖ range Tᵏ`. Hence `β` restricts to a nondegenerate
alternating form on `ker T^∞`, whose dimension (the multiplicity of `γ`) is therefore even. The
general case follows by extending scalars to `L`.

## Main results

* `LinearMap.BilinForm.even_finrank_maxGenEigenspace_of_sq_eq`: over `K`, the generalized
  eigenspace of `F` for a square root `γ ∈ K` of `c` is even-dimensional.
* `LinearMap.BilinForm.even_rootMultiplicity_charpoly_map_of_isFrobeniusDuality`: the
  multiplicity of a square root `γ ∈ L` of `c` as a root of the characteristic polynomial of `F`
  is even.

## Implementation notes

The source takes `γ` in an algebraic closure of `K`; the statement here allows any field
extension `L` of `K`, which contains that case. The base change to `L` is `L ⊗[K] V` with
`LinearMap.BilinForm.baseChange` and `LinearMap.baseChange`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public section

open Module TensorProduct

namespace LinearMap.BilinForm

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For `T = F - γ` and `β (F x) (F y) = γ² β x y`, one has
`β (Tᵏ x) (Fᵏ y) = (-γ)ᵏ β x (Tᵏ y)`. -/
lemma apply_sub_smul_pow_pow {β : LinearMap.BilinForm K V} {F : Module.End K V} {γ : K}
    (hmap : ∀ x y, β (F x) (F y) = γ ^ 2 * β x y) (k : ℕ) (x y : V) :
    β (((F - γ • 1) ^ k) x) ((F ^ k) y) = (-γ) ^ k * β x (((F - γ • 1) ^ k) y) := by
  set T := F - γ • (1 : Module.End K V)
  have hcomm : Commute T F := (Commute.refl F).sub_left (Commute.smul_left (Commute.one_left F) γ)
  have h1 : ∀ x y, β (T x) (F y) = -γ * β x (T y) := by
    intro x y
    simp only [T, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hmap]
    ring
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h1,
      ← Module.End.mul_apply, (hcomm.pow_right k).eq, Module.End.mul_apply, ih,
      ← Module.End.mul_apply (T ^ k) T y,
      ← pow_succ, ← pow_succ', pow_succ' (-γ)]
    ring

/-- Let `β` be a bilinear form on a finite-dimensional space with `x ↦ β x ·` injective and
`β (F x) (F y) = γ² β x y` for a nonzero `γ`. Then the maximal generalized eigenspace of `F` for
`γ` is orthogonal to the Fitting complement `⋂ₖ range (F - γ)ᵏ`, and `β` restricted to it is
injective. -/
lemma injective_restrict_maxGenEigenspace [FiniteDimensional K V]
    {β : LinearMap.BilinForm K V} {F : Module.End K V} {γ : K} (hinj : Function.Injective β)
    (hmap : ∀ x y, β (F x) (F y) = γ ^ 2 * β x y) (hγ : γ ≠ 0) :
    Function.Injective (β.restrict (F.maxGenEigenspace γ)) := by
  set T := F - γ • (1 : Module.End K V)
  set W := F.maxGenEigenspace γ
  set U := ⨅ n : ℕ, LinearMap.range (T ^ n)
  have hW : W = ⨆ n : ℕ, LinearMap.ker (T ^ n) := by
    rw [show W = _ from Module.End.maxGenEigenspace_eq_maxGenEigenspace_zero F γ]
    simp [T, ← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  have hWU : W ⊔ U = ⊤ := by
    rw [hW]; exact (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow T).sup_eq_top
  have horth : ∀ x ∈ W, ∀ u ∈ U, β x u = 0 := by
    intro x hx u hu
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace F γ x).mp hx
    obtain ⟨y, rfl⟩ := (Submodule.mem_iInf _).mp hu k
    have h := apply_sub_smul_pow_pow hmap k x y
    rw [hk, map_zero, LinearMap.zero_apply] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hγ))
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  apply hinj
  ext v
  have hv : v ∈ W ⊔ U := hWU ▸ Submodule.mem_top
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  have h1 : β x w = 0 := by
    simpa using LinearMap.congr_fun hx ⟨w, hw⟩
  simp [h1, horth x x.2 u hu]

/-- Let `β` be an alternating bilinear form on a finite-dimensional space with `x ↦ β x ·`
injective and `β (F x) (F y) = γ² β x y` for a nonzero `γ ∈ K`. Then the maximal generalized
eigenspace of `F` for `γ` is even-dimensional. -/
theorem even_finrank_maxGenEigenspace_of_sq_eq [FiniteDimensional K V]
    {β : LinearMap.BilinForm K V} {F : Module.End K V} {γ : K} (halt : β.IsAlt)
    (hinj : Function.Injective β)
    (hmap : ∀ x y, β (F x) (F y) = γ ^ 2 * β x y) (hγ : γ ≠ 0) :
    Even (finrank K (F.maxGenEigenspace γ)) :=
  even_finrank_of_isAlt_of_injective _ (fun x => halt x)
    (injective_restrict_maxGenEigenspace hinj hmap hγ)

end Field

section BaseChange

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (L : Type*) [Field L] [Algebra K L]

/-- The base change of an alternating bilinear form is skew-symmetric. -/
lemma IsAlt.baseChange_neg_eq {β : LinearMap.BilinForm K V} (halt : β.IsAlt) (x y : L ⊗[K] V) :
    -β.baseChange L x y = β.baseChange L y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, neg_add, hx, hx']
  | tmul a v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, neg_add, hy, hy', LinearMap.add_apply]
    | tmul b w =>
      simp only [baseChange_tmul, ← halt.neg_eq v w, neg_smul, mul_comm a b]

/-- The base change of an alternating bilinear form is alternating. -/
lemma IsAlt.baseChange {β : LinearMap.BilinForm K V} (halt : β.IsAlt) : (β.baseChange L).IsAlt := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    have := halt.baseChange_neg_eq L x y
    simp only [map_add, LinearMap.add_apply, hx, hy, ← this]
    abel
  | tmul a v => simp [halt.self_eq_zero v]

/-- If `β (F x) (F y) = c β x y`, the same holds for the base changes of `β` and `F`. -/
lemma baseChange_apply_baseChange {β : LinearMap.BilinForm K V} {F : Module.End K V} {c : K}
    (hmap : ∀ x y, β (F x) (F y) = c * β x y) (x y : L ⊗[K] V) :
    β.baseChange L (F.baseChange L x) (F.baseChange L y) =
      algebraMap K L c * β.baseChange L x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
  | tmul a v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
    | tmul b w =>
      simp only [LinearMap.baseChange_tmul, baseChange_tmul, hmap, Algebra.smul_def, map_mul]
      ring

/-- The base change of a bilinear form `β` on a finite-dimensional space with `x ↦ β x ·`
injective again has this property. -/
lemma injective_baseChange [FiniteDimensional K V] {β : LinearMap.BilinForm K V}
    (hinj : Function.Injective β) : Function.Injective (β.baseChange L) := by
  set b := Module.finBasis K V
  set b' := Algebra.TensorProduct.basis L b
  have hnd : β.Nondegenerate := nondegenerate_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hinj)
  have hdet : (BilinForm.toMatrix b β).det ≠ 0 := (nondegenerate_iff_det_ne_zero b).mp hnd
  have hmat : BilinForm.toMatrix b' (β.baseChange L) =
      (BilinForm.toMatrix b β).map (algebraMap K L) := by
    ext i j
    simp [b', BilinForm.toMatrix_apply, Algebra.TensorProduct.basis_apply, Algebra.smul_def]
  have hnd' : (β.baseChange L).Nondegenerate := by
    rw [nondegenerate_iff_det_ne_zero b', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hdet
  exact LinearMap.ker_eq_bot.mp (nondegenerate_iff_ker_eq_bot.mp hnd')

/-- Let `F` be an endomorphism of a finite-dimensional `K`-vector space `V`, `β` a `c`-duality
for `(F, F)` with `β x x = 0` for all `x`, and `γ` a square root of `c` in a field extension `L`
of `K`. Then the multiplicity of `γ` as an eigenvalue of `F` (as a root of its characteristic
polynomial) is even. -/
@[weil "lem_fk401_alternating_duality_eigenvalue_multiplicity_even"]
theorem even_rootMultiplicity_charpoly_map_of_isFrobeniusDuality [FiniteDimensional K V]
    {β : LinearMap.BilinForm K V} {F : Module.End K V} {c : Kˣ} (hβ : β.IsFrobeniusDuality F F c)
    (halt : β.IsAlt) {γ : L} (hγ : γ ^ 2 = algebraMap K L c) :
    Even ((F.charpoly.map (algebraMap K L)).rootMultiplicity γ) := by
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap K L).injective] at hγ
    exact c.ne_zero hγ
  rw [← LinearMap.charpoly_baseChange, ← LinearMap.finrank_maxGenEigenspace_eq]
  refine even_finrank_maxGenEigenspace_of_sq_eq (halt.baseChange L)
    (injective_baseChange L hβ.injective_left) (fun x y => ?_) hγ0
  rw [hγ]
  exact baseChange_apply_baseChange L hβ.map_map x y

end BaseChange

end LinearMap.BilinForm
