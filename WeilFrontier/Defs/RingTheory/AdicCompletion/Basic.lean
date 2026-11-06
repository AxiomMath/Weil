module

public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The projective system of a module

Let `Λ` be a commutative ring and `l ∈ Λ`. For a `Λ`-module `M`, the projective system `S(M)`
has terms `S(M)_n = M / l^{n+1} M` for `n ≥ 0` and `S(M)_n = 0` for `n < 0`, with the natural
surjections `M / l^{n+2} M → M / l^{n+1} M` (and `M / l M → 0`) as transition maps. Every
term is `l`-power torsion, so `S(M)` is a projective system of `l`-power torsion modules. A
`Λ`-linear map `φ : M → N` induces the morphism `S(φ)` with components `φ mod l^{n+1}`, and
`S` is a functor.

More generally, for an ideal `I` of `Λ` we write down the system `n ↦ M ⧸ I^{n+1} M` (zero for
`n < 0`) as a functor `ℤᵒᵖ ⥤ ModuleCat Λ`; for `I = (l)` it is `S(M)`. Its non-negative part is
the system whose limit is `AdicCompletion I M`, and its transition maps are
`AdicCompletion.transitionMap`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.adicDiagram I`: the functor sending `M` to the system
  `n ↦ M ⧸ (I ^ (n + 1).toNat • ⊤)` in `ℤᵒᵖ ⥤ ModuleCat Λ`.
* `CategoryTheory.ProjectiveSystem.ofModule l`: the functor
  `S : ModuleCat Λ ⥤ ProjectiveSystem Λ l`.

## Main results

* `CategoryTheory.ProjectiveSystem.ofModule_term`: `S(M)_n = M ⧸ ((l) ^ (n + 1).toNat • ⊤)`.
* `CategoryTheory.ProjectiveSystem.ofModuleTermEquiv`: for `n ≥ 0`, `S(M)_n ≃ M ⧸ l^{n+1} M`.
* `CategoryTheory.ProjectiveSystem.isZero_ofModule_term`: `S(M)_n = 0` for `n < 0`.
* `CategoryTheory.ProjectiveSystem.ofModule_transition_mk`: the transition maps are the natural
  surjections.
* `CategoryTheory.ProjectiveSystem.ofModule_map_app_mk`: `S(φ)_n` is `φ mod l^{n+1}`.

## Implementation notes

The term in degree `n` is the quotient of `M` by `I ^ (n + 1).toNat • ⊤` with `I = (l)`, uniformly
in `n ∈ ℤ`: for `n < 0` the exponent is `0` and `I ^ 0 • ⊤ = ⊤`, so the quotient is zero. The
submodule `(l) ^ k • ⊤` is Mathlib's form of `l^k M` used by `AdicCompletion`; it equals the
pointwise `l ^ k • ⊤` (`CategoryTheory.ProjectiveSystem.span_singleton_pow_smul_top`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

noncomputable section

universe v u

open Opposite Pointwise

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ]

/-- The exponent `(n + 1).toNat` is monotone in `n`. -/
lemma toNat_add_one_le_of_le {m n : ℤ} (h : m ≤ n) : (m + 1).toNat ≤ (n + 1).toNat :=
  Int.toNat_le_toNat (by omega)

/-- The system `n ↦ M ⧸ I^{n+1} M` (zero for `n < 0`) of a `Λ`-module `M`, with the natural
surjections as transition maps, as a functor of `M`. -/
def adicDiagram (I : Ideal Λ) : ModuleCat.{v} Λ ⥤ (ℤᵒᵖ ⥤ ModuleCat.{v} Λ) where
  obj M :=
    { obj := fun n => ModuleCat.of Λ (M ⧸ (I ^ (n.unop + 1).toNat • ⊤ : Submodule Λ M))
      map := fun {n m} h => ModuleCat.ofHom
        (AdicCompletion.transitionMap I M (toNat_add_one_le_of_le (leOfHom h.unop)))
      map_id := fun n => by
        ext x
        rfl
      map_comp := fun {a b c} f g => by
        ext x
        rfl }
  map {M N} φ :=
    { app := fun n => ModuleCat.ofHom
        (Submodule.mapQ _ _ φ.hom (Submodule.smul_top_le_comap_smul_top _ φ.hom))
      naturality := fun {n m} h => by
        ext x
        rfl }
  map_id M := by
    ext n : 2
    ext x
    rfl
  map_comp φ ψ := by
    ext n : 2
    ext x
    rfl

@[simp]
lemma adicDiagram_obj_obj (I : Ideal Λ) (M : ModuleCat.{v} Λ) (n : ℤᵒᵖ) :
    ((adicDiagram I).obj M).obj n =
      ModuleCat.of Λ (M ⧸ (I ^ (n.unop + 1).toNat • ⊤ : Submodule Λ M)) := rfl

/-- `I ^ 0 • ⊤ = ⊤`, so the quotient in a negative degree is zero. -/
lemma isZero_adicDiagram_obj_obj (I : Ideal Λ) (M : ModuleCat.{v} Λ) {n : ℤ} (hn : n < 0) :
    IsZero (((adicDiagram I).obj M).obj (op n)) := by
  have h : (n + 1).toNat = 0 := by omega
  have : Subsingleton (M ⧸ (I ^ (n + 1).toNat • ⊤ : Submodule Λ M)) := by
    rw [h, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.Quotient.subsingleton_iff.mpr rfl
  exact @ModuleCat.isZero_of_subsingleton _ _ (((adicDiagram I).obj M).obj (op n)) this

/-- `(l) ^ k • ⊤ = l ^ k • ⊤`: the submodule of `M` used in the adic system is `l^k M`. -/
lemma span_singleton_pow_smul_top (l : Λ) (M : Type*) [AddCommGroup M] [Module Λ M] (k : ℕ) :
    ((Ideal.span {l}) ^ k • ⊤ : Submodule Λ M) = l ^ k • (⊤ : Submodule Λ M) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]

/-- Every element of `M ⧸ (l) ^ k M` is killed by `l ^ k`. -/
lemma pow_smul_eq_zero_of_quotient (l : Λ) (M : Type*) [AddCommGroup M] [Module Λ M] (k : ℕ)
    (x : M ⧸ ((Ideal.span {l}) ^ k • ⊤ : Submodule Λ M)) : l ^ k • x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self l) k)
    Submodule.mem_top

lemma isTorsionBounded_adicDiagram_obj (l : Λ) (M : ModuleCat.{v} Λ) :
    isTorsionBounded.{v} Λ l ((adicDiagram (Ideal.span {l})).obj M) :=
  ⟨fun n x => ⟨⟨l ^ (n + 1).toNat, (n + 1).toNat, rfl⟩, pow_smul_eq_zero_of_quotient l M _ x⟩,
    -1, fun n hn => isZero_adicDiagram_obj_obj _ M (by omega)⟩

variable (l : Λ)

/-- The projective system `S(M)` of a `Λ`-module `M`: `S(M)_n = M / l^{n+1} M` for `n ≥ 0`,
`S(M)_n = 0` for `n < 0`, with the natural surjections as transition maps; a linear map
`φ : M → N` induces `S(φ)` with components `φ mod l^{n+1}`. -/
@[weil "def_fk112_l_adic_system_of_module"]
def ofModule : ModuleCat.{v} Λ ⥤ ProjectiveSystem.{v} Λ l :=
  (isTorsionBounded.{v} Λ l).lift (adicDiagram (Ideal.span {l}))
    (isTorsionBounded_adicDiagram_obj l)

variable {l}

@[simp]
lemma ofModule_term (M : ModuleCat.{v} Λ) (n : ℤ) :
    ((ofModule l).obj M).term n =
      ModuleCat.of Λ (M ⧸ ((Ideal.span {l}) ^ (n + 1).toNat • ⊤ : Submodule Λ M)) := rfl

/-- For `n ≥ 0`, the term `S(M)_n` is `M / l^{n+1} M`. -/
@[weil "def_fk112_l_adic_system_of_module"]
def ofModuleTermEquiv (l : Λ) (M : ModuleCat.{v} Λ) {n : ℤ} (hn : 0 ≤ n) :
    ((ofModule l).obj M).term n ≃ₗ[Λ] M ⧸ (l ^ (n.toNat + 1) • (⊤ : Submodule Λ M)) :=
  Submodule.quotEquivOfEq ((Ideal.span {l}) ^ (n + 1).toNat • ⊤) (l ^ (n.toNat + 1) • ⊤) (by
    rw [span_singleton_pow_smul_top, show (n + 1).toNat = n.toNat + 1 by omega])

@[simp]
lemma ofModuleTermEquiv_mk (M : ModuleCat.{v} Λ) {n : ℤ} (hn : 0 ≤ n) (x : M) :
    ofModuleTermEquiv l M hn (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- `S(M)_n = 0` for `n < 0`. -/
lemma isZero_ofModule_term (M : ModuleCat.{v} Λ) {n : ℤ} (hn : n < 0) :
    IsZero (((ofModule l).obj M).term n) :=
  isZero_adicDiagram_obj_obj _ M hn

/-- The transition maps of `S(M)` are the natural surjections `x mod l^{n+1} ↦ x mod l^n`. -/
@[simp]
lemma ofModule_transition_mk (M : ModuleCat.{v} Λ) (n : ℤ) (x : M) :
    (((ofModule l).obj M).transition n).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

/-- The components of `S(φ)` are `φ mod l^{n+1}`. -/
@[simp]
lemma ofModule_map_app_mk {M N : ModuleCat.{v} Λ} (φ : M ⟶ N) (n : ℤ) (x : M) :
    (app ((ofModule l).map φ) n).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ.hom x) := rfl

end ProjectiveSystem

end CategoryTheory

end
