module

public import Weil.Attr
public import Weil.CategoryTheory.Abelian.ArKernel
public import Weil.CategoryTheory.Abelian.SerreClass.ArCategoryAbelian
public import Weil.CategoryTheory.Abelian.SerreClass.Localization
public import Weil.CategoryTheory.Abelian.Subcategory
public import Weil.CategoryTheory.Preadditive.ArZeroObjectIffNull
public import Weil.Defs.CategoryTheory.ObjectProperty.ArIsomorphism
public import Weil.Defs.CategoryTheory.ObjectProperty.NullSystem
public import Weil.Defs.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration

/-!
# The Artin–Rees lemma for the projective system of a kernel

Let `Λ` be a noetherian commutative ring, `l ∈ Λ`, and let `φ : M → N` be a homomorphism of
finitely generated `Λ`-modules with kernel `K`. Applying the functor `S` (`S(M)_n = M / l^{n+1} M`)
to the inclusion `K ↪ M` gives a morphism `S(K) ⟶ S(M)` whose composite with `S(φ)` vanishes, hence
a morphism `w : S(K) ⟶ Ker S(φ)` of projective systems. In degree `n ≥ 0` it is the map
`K / l^{n+1} K → φ⁻¹(l^{n+1} N) / l^{n+1} M` induced by the inclusion. It is in general not an
isomorphism, but it is an A–R isomorphism: by the Artin–Rees lemma there is `c` with
`K ∩ l^m M ⊆ l^{m-c} K` and `φ(M) ∩ l^m N ⊆ l^{m-c} φ(M)` for `m ≥ c`, so `ε^c` kills the kernel
and the cokernel of `w`, which are therefore null systems.

## Main definitions

* `CategoryTheory.ProjectiveSystem.ofModuleKerToKernel l φ`: the morphism
  `w : S(ker φ) ⟶ Ker S(φ)` induced by `S(ker φ ↪ M)`.

## Main results

* `CategoryTheory.ProjectiveSystem.representsArIso_ofModuleKerToKernel`: for finitely generated
  modules over a noetherian ring, `w` represents an A–R isomorphism.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite Pointwise

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/- the next lemma is the "if" direction of
`representsArIso_iff_isNull_kernel_and_isNull_cokernel` (in
`Weil.CategoryTheory.Abelian.SerreClass.MorphismProperty`), proved here directly. -/

/-- A morphism of projective systems whose kernel and cokernel are null systems represents an
A–R isomorphism. -/
private lemma representsArIso_of_isNull_kernel_of_isNull_cokernel
    {F G : ProjectiveSystem.{v} Λ l} (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G)
    (hK : isNull (kernel f)) (hC : isNull (cokernel f)) : RepresentsArIso r f := by
  have eK : ArCategory.of (kernel f) ≅ kernel (ArCategory.homMk r f) :=
    IsLimit.conePointUniqueUpToIso (ArCategory.isLimitKernelForkHomMkKernelι f)
      (limit.isLimit _)
  have eC : ArCategory.of (cokernel f) ≅ cokernel (ArCategory.homMk r f) :=
    IsColimit.coconePointUniqueUpToIso
      (ArCategory.isColimitCokernelCoforkHomMk (w := cokernel.condition f) (cokernelIsCokernel f))
      (colimit.isColimit _)
  rw [← ArCategory.isZero_of_iff_isNull, eK.isZero_iff, ← Preadditive.mono_iff_isZero_kernel]
    at hK
  rw [← ArCategory.isZero_of_iff_isNull, eC.isZero_iff, ← Preadditive.epi_iff_isZero_cokernel]
    at hC
  exact isIso_of_mono_of_epi _

/-- The kernel of `f` is null if, for some `t`, every element of `F_{n+t}` killed by `f` is killed
by `ε^t_{F,n}`. -/
private lemma isNull_kernel_of_forall {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (t : ℕ)
    (h : ∀ (n : ℤ) (y : F.term (n + t)), (app f (n + t)).hom y = 0 →
      (app (natMap F t) n).hom y = 0) :
    isNull (kernel f) := by
  refine ⟨t, (natMap_eq_zero_iff _ _).2 fun n => ?_⟩
  have : Mono (app (kernel.ι f) n) := by rw [← kernelIso_hom_ι]; infer_instance
  refine (cancel_mono (app (kernel.ι f) n)).1 ?_
  rw [zero_comp]
  have hnat := congrArg (fun g => app g n) (natMap_naturality (kernel.ι f) t)
  simp only [comp_app, shift_map_app] at hnat
  rw [← hnat]
  refine ModuleCat.hom_ext (LinearMap.ext fun (z : (kernel f).term (n + t)) => ?_)
  have hz := congrArg (fun g => (app g (n + t)).hom z) (kernel.condition f)
  simp only [comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  exact h n _ hz

/-- The cokernel of `f` is null if, for some `t`, the image under `ε^t_{G,n}` of every element of
`G_{n+t}` lies in the image of `f_n`. -/
private lemma isNull_cokernel_of_forall {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (t : ℕ)
    (h : ∀ (n : ℤ) (y : G.term (n + t)), ∃ x : F.term n,
      (app f n).hom x = (app (natMap G t) n).hom y) :
    isNull (cokernel f) := by
  refine ⟨t, (natMap_eq_zero_iff _ _).2 fun n => ?_⟩
  have : Epi (app (cokernel.π f) (n + t)) := by
    have e : app (cokernel.π f) (n + t) =
        cokernel.π (app f (n + t)) ≫ (cokernelIso f (n + t)).inv := by
      rw [← π_cokernelIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  refine (cancel_epi (app (cokernel.π f) (n + t))).1 ?_
  have hnat := congrArg (fun g => app g n) (natMap_naturality (cokernel.π f) t)
  simp only [comp_app, shift_map_app] at hnat
  refine hnat.trans (Eq.trans ?_ comp_zero.symm)
  refine ModuleCat.hom_ext (LinearMap.ext fun (y : G.term (n + t)) => ?_)
  obtain ⟨x, hx⟩ := h n y
  have hz := congrArg (fun g => (app g n).hom x) (cokernel.condition f)
  simp only [comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hx] at hz
  exact hz

/-- Artin–Rees, in the form used here: for a submodule `N` of a finitely generated module over a
noetherian ring there is `c` with `I^e M ∩ N ⊆ I^{e-c} N` for all `e`. -/
private lemma exists_pow_smul_top_inf_le [IsNoetherianRing Λ] (I : Ideal Λ) {M : Type*}
    [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (N : Submodule Λ M) :
    ∃ c : ℕ, ∀ e : ℕ, I ^ e • (⊤ : Submodule Λ M) ⊓ N ≤ I ^ (e - c) • N := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨c, fun e => ?_⟩
  rcases le_or_gt c e with h | h
  · rw [hc e h]
    exact Submodule.smul_mono le_rfl inf_le_right
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact inf_le_right

private lemma subtype_comp_eq_zero {M N : ModuleCat.{v} Λ} (φ : M ⟶ N) :
    ModuleCat.ofHom (LinearMap.ker φ.hom).subtype ≫ φ = 0 := by
  ext x
  exact x.2

variable (l) in
/-- The morphism `w : S(ker φ) ⟶ Ker S(φ)` of projective systems induced by `S(ker φ ↪ M)`. -/
@[weil "lem_fk112_artin_rees_kernel"]
noncomputable def ofModuleKerToKernel {M N : ModuleCat.{v} Λ} (φ : M ⟶ N) :
    (ofModule l).obj (ModuleCat.of Λ (LinearMap.ker φ.hom)) ⟶ kernel ((ofModule l).map φ) :=
  kernel.lift _ ((ofModule l).map (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype)) (by
    rw [← Functor.map_comp, subtype_comp_eq_zero]
    refine hom_ext fun n => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl)

@[reassoc (attr := simp)]
lemma ofModuleKerToKernel_ι {M N : ModuleCat.{v} Λ} (φ : M ⟶ N) :
    ofModuleKerToKernel l φ ≫ kernel.ι _ =
      (ofModule l).map (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype) :=
  kernel.lift_ι _ _ _

/-- **Artin–Rees for kernels.** Let `φ : M → N` be a homomorphism of finitely generated modules
over a noetherian ring `Λ`. The morphism `w : S(ker φ) ⟶ Ker S(φ)` induced by `S(ker φ ↪ M)`
represents an A–R isomorphism. -/
@[weil "lem_fk112_artin_rees_kernel"]
theorem representsArIso_ofModuleKerToKernel [IsNoetherianRing Λ] {M N : ModuleCat.{v} Λ}
    [Module.Finite Λ M] [Module.Finite Λ N] (φ : M ⟶ N) :
    RepresentsArIso 0 (natMap _ 0 ≫ ofModuleKerToKernel l φ) := by
  have hι : ∀ (n : ℤ) (x : ((ofModule l).obj (ModuleCat.of Λ (LinearMap.ker φ.hom))).term n),
      (app (kernel.ι ((ofModule l).map φ)) n).hom ((app (ofModuleKerToKernel l φ) n).hom x) =
        (app ((ofModule l).map (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype)) n).hom x :=
    fun n x => by
      have := congrArg (fun g => (app g n).hom x) (ofModuleKerToKernel_ι (l := l) φ)
      simpa only [comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hinj : ∀ n : ℤ, Function.Injective (app (kernel.ι ((ofModule l).map φ)) n).hom :=
    fun n => by
      have : Mono (app (kernel.ι ((ofModule l).map φ)) n) := by
        rw [← kernelIso_hom_ι]; infer_instance
      exact (ModuleCat.mono_iff_injective _).1 this
  have : IsIso (natMap ((ofModule l).obj (ModuleCat.of Λ (LinearMap.ker φ.hom))) 0) := by
    rw [natMap_zero]
    infer_instance
  apply representsArIso_of_isNull_kernel_of_isNull_cokernel
  · refine isNull_of_iso (kernelIsIsoComp _ _).symm ?_
    obtain ⟨c, hc⟩ := exists_pow_smul_top_inf_le (Ideal.span {l}) (LinearMap.ker φ.hom)
    refine isNull_kernel_of_forall _ c fun n y hy => ?_
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hk : (k : M) ∈ (Ideal.span {l}) ^ (n + c + 1).toNat • (⊤ : Submodule Λ M) := by
      have := hι (n + c) (Submodule.Quotient.mk k)
      rw [hy, map_zero] at this
      exact (Submodule.Quotient.mk_eq_zero _).1 this.symm
    have hk' : (LinearMap.ker φ.hom).subtype k ∈ Submodule.map (LinearMap.ker φ.hom).subtype
        ((Ideal.span {l}) ^ ((n + c + 1).toNat - c) • ⊤) := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
      exact hc _ ⟨hk, k.2⟩
    obtain ⟨k', hk', hkk'⟩ := hk'
    obtain rfl : k' = k := Subtype.ext hkk'
    change (Submodule.Quotient.mk k' : LinearMap.ker φ.hom ⧸
      ((Ideal.span {l}) ^ (n + 1).toNat • (⊤ : Submodule Λ (LinearMap.ker φ.hom)))) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hk'
  · refine isNull_of_iso (cokernelEpiComp _ _).symm ?_
    obtain ⟨c, hc⟩ := exists_pow_smul_top_inf_le (Ideal.span {l}) (LinearMap.range φ.hom)
    refine isNull_cokernel_of_forall _ c fun n y => ?_
    have hz := congrArg (fun g => (app g (n + c)).hom y) (kernel.condition ((ofModule l).map φ))
    simp only [comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _
      ((app (kernel.ι ((ofModule l).map φ)) (n + c)).hom y)
    have hφm : φ.hom m ∈ (Ideal.span {l}) ^ (n + c + 1).toNat • (⊤ : Submodule Λ N) := by
      rw [← hm] at hz
      exact (Submodule.Quotient.mk_eq_zero _).1 hz
    have hφm' := hc _ ⟨hφm, LinearMap.mem_range_self _ m⟩
    rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at hφm'
    obtain ⟨m', hm', hmm'⟩ := hφm'
    have hker : m - m' ∈ LinearMap.ker φ.hom := by
      rw [LinearMap.mem_ker, map_sub, hmm', sub_self]
    refine ⟨Submodule.Quotient.mk ⟨m - m', hker⟩, hinj n ?_⟩
    refine (hι n _).trans ?_
    have hnat := congrArg (fun g => (app g n).hom y)
      (natMap_naturality (kernel.ι ((ofModule l).map φ)) c)
    simp only [comp_app, shift_map_app, ModuleCat.hom_comp] at hnat
    refine Eq.trans ?_ hnat
    change _ = (app (natMap ((ofModule l).obj M) c) n).hom
      ((app (kernel.ι ((ofModule l).map φ)) (n + c)).hom y)
    rw [← hm]
    change (Submodule.Quotient.mk (m - m') :
      M ⧸ ((Ideal.span {l}) ^ (n + 1).toNat • (⊤ : Submodule Λ M))) = Submodule.Quotient.mk m
    rw [Submodule.Quotient.eq, sub_sub_cancel_left, Submodule.neg_mem_iff]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hm'

end ProjectiveSystem

end CategoryTheory
