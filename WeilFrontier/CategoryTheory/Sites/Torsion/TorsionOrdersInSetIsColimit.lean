module

public import Weil.Attr
public import StacksFrontier.CategoryTheory.Sites.Torsion.TorsionColimitOfKernels
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# A sheaf killed by a multiplicative set of integers is the colimit of its torsion subsheaves

Let `N` be a set of natural numbers closed under products (a subsemigroup of `(ℕ, *)`), and let
`𝓕` be a sheaf of abelian groups on a site such that every section of `𝓕` over every object is
annihilated by an element of `N`. For `n ∈ N` write `𝓕[n] = ker (n : 𝓕 ⟶ 𝓕)`. Then `N`, ordered
by divisibility, is directed, and the inclusions `𝓕[n] ⟶ 𝓕` exhibit `𝓕` as the colimit of the
`𝓕[n]`, `n ∈ N`.

The proof works on sections: over every object `U` the maps `𝓕[n](U) ⟶ 𝓕(U)` are injective, and
every section lies in the image of one of them, so `𝓕(U)` is the directed union of the
`𝓕[n](U)`. Hence the cocone is a colimit of presheaves, and so of sheaves, since sheaves form a
full subcategory of presheaves.

## Main definitions

* `Subsemigroup.DvdIndex N`: a subsemigroup `N` of `(ℕ, *)`, ordered by divisibility.
* `CategoryTheory.Sheaf.subsemigroupTorsionKernels 𝓕 N`: the system `n ↦ 𝓕[n]` over `N`.
* `CategoryTheory.Sheaf.subsemigroupTorsionKernelsCocone 𝓕 N`: the inclusions `𝓕[n] ⟶ 𝓕`.

## Main results

* `Subsemigroup.DvdIndex.isDirected`: `N` ordered by divisibility is directed.
* `CategoryTheory.Sheaf.nonempty_isColimit_subsemigroupTorsionKernelsCocone`: if every section
  of `𝓕` is killed by an element of `N`, then `𝓕` is the colimit of the `𝓕[n]`, `n ∈ N`.

## Implementation notes

The result is stated for an arbitrary site; the small étale site
`AlgebraicGeometry.SmallEtale.topology B S hS` is a special case. The set `N` need not contain
`1`, nor consist of positive integers: `0 ∈ N` is allowed (then `𝓕[0] = 𝓕`). For a submonoid
`M` the same system over `Stacks.Torsion.DvdIndex M` is `Stacks.Torsion.torsionKernels`, whose
transition maps `Stacks.Torsion.torsionKernelsMap` are used here.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Subsemigroup

/-- A subsemigroup `N` of `(ℕ, *)`, ordered by divisibility. -/
def DvdIndex (N : Subsemigroup ℕ) : Type := N

namespace DvdIndex

variable {N : Subsemigroup ℕ}

/-- The natural number underlying an index. -/
def val (n : DvdIndex N) : ℕ := (show N from n : ℕ)

/-- The index attached to an element of `N`. -/
def mk (n : N) : DvdIndex N := n

/-- The natural number underlying `mk n` is `n`. -/
@[simp] theorem val_mk (n : N) : (mk n).val = n := rfl

/-- The natural number underlying an index lies in `N`. -/
theorem val_mem (n : DvdIndex N) : n.val ∈ N := (show N from n).2

/-- The divisibility preorder: `a ≤ b` when `a.val ∣ b.val`. -/
instance : Preorder (DvdIndex N) where
  le a b := a.val ∣ b.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

/-- `a ≤ b` if and only if `a.val` divides `b.val`. -/
theorem le_iff {a b : DvdIndex N} : a ≤ b ↔ a.val ∣ b.val := Iff.rfl

/-- **`N` ordered by divisibility is directed**: `a` and `b` both divide `a * b ∈ N`. -/
@[weil "lem_fk108_torsion_orders_in_set_is_colimit"]
theorem isDirected : IsDirected (DvdIndex N) (· ≤ ·) where
  directed a b :=
    ⟨mk ⟨a.val * b.val, N.mul_mem a.val_mem b.val_mem⟩, dvd_mul_right a.val b.val,
      dvd_mul_left b.val a.val⟩

instance : IsDirected (DvdIndex N) (· ≤ ·) := isDirected

end DvdIndex

end Subsemigroup

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝓕 : Sheaf J AddCommGrpCat.{w}) (N : Subsemigroup ℕ)

/-- **The system `n ↦ 𝓕[n]`** of kernels of multiplication by `n ∈ N`, over `N` ordered by
divisibility. -/
def subsemigroupTorsionKernels : Subsemigroup.DvdIndex N ⥤ Sheaf J AddCommGrpCat.{w} where
  obj n := kernel (n.val • 𝟙 𝓕)
  map h := Stacks.Torsion.torsionKernelsMap 𝓕 (Subsemigroup.DvdIndex.le_iff.1 (leOfHom h))
  map_id _ := (cancel_mono (kernel.ι _)).1 (by simp)
  map_comp _ _ := (cancel_mono (kernel.ι _)).1 (by simp)

/-- **The inclusions `𝓕[n] ⟶ 𝓕`**, a cocone over the system of `n`-torsion subsheaves. -/
@[simps]
def subsemigroupTorsionKernelsCocone : Cocone (subsemigroupTorsionKernels 𝓕 N) where
  pt := 𝓕
  ι :=
    { app n := kernel.ι (n.val • 𝟙 𝓕)
      naturality _ _ h := by simp [subsemigroupTorsionKernels] }

/-- The inclusion `𝓕[n] ⟶ 𝓕` is injective on sections over every object. -/
private theorem injective_kernel_ι_app (n : ℕ) (U : Cᵒᵖ) :
    Function.Injective ((kernel.ι (n • 𝟙 𝓕)).hom.app U) := by
  let G : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  have : Mono (G.map (kernel.ι (n • 𝟙 𝓕))) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- **A sheaf whose sections are killed by elements of `N` is the colimit of its
`n`-torsion subsheaves.** If every section of `𝓕` over every object is annihilated by an element
of `N`, then the inclusions `𝓕[n] ⟶ 𝓕`, `n ∈ N`, exhibit `𝓕` as the colimit of the system of
the `𝓕[n]` over `N` ordered by divisibility. -/
@[weil "lem_fk108_torsion_orders_in_set_is_colimit"]
theorem nonempty_isColimit_subsemigroupTorsionKernelsCocone
    (h𝓕 : ∀ (U : C) (x : 𝓕.obj.obj (op U)), ∃ n ∈ N, n • x = 0) :
    Nonempty (IsColimit (subsemigroupTorsionKernelsCocone 𝓕 N)) := by
  refine ⟨?_⟩
  let D := subsemigroupTorsionKernels 𝓕 N
  let c := subsemigroupTorsionKernelsCocone 𝓕 N
  refine isColimitOfReflects (sheafToPresheaf J AddCommGrpCat.{w}) ?_
  refine evaluationJointlyReflectsColimits _ (fun U => ?_)
  have : Nonempty (Subsemigroup.DvdIndex N) := by
    obtain ⟨n₀, hn₀, -⟩ := h𝓕 U.unop 0
    exact ⟨Subsemigroup.DvdIndex.mk ⟨n₀, hn₀⟩⟩
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  let t : Cocone (D ⋙ E) := E.mapCocone c
  change IsColimit t
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{w}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : HasColimitsOfShape (Subsemigroup.DvdIndex N) AddCommGrpCat.{w} :=
    hasColimitsOfShape_of_equivalence (AsSmall.equiv (C := Subsemigroup.DvdIndex N)).symm
  have : ReflectsColimitsOfShape (Subsemigroup.DvdIndex N) (forget AddCommGrpCat.{w}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget AddCommGrpCat.{w}) ?_
  refine Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i j xi xj h => ?_)
  · obtain ⟨n, hn, hx⟩ := h𝓕 U.unop x
    obtain ⟨z, hz⟩ := Stacks.Torsion.exists_kernel_ι_app_eq 𝓕 n x hx
    exact ⟨Subsemigroup.DvdIndex.mk ⟨n, hn⟩, z, hz.symm⟩
  · let k : Subsemigroup.DvdIndex N :=
      Subsemigroup.DvdIndex.mk ⟨i.val * j.val, N.mul_mem i.val_mem j.val_mem⟩
    let f : i ⟶ k := homOfLE (dvd_mul_right i.val j.val)
    let g : j ⟶ k := homOfLE (dvd_mul_left j.val i.val)
    refine ⟨k, f, g, injective_kernel_ι_app 𝓕 k.val U ?_⟩
    have hf := congrArg (fun φ : D.obj i ⟶ 𝓕 => φ.hom.app U xi) (c.w f)
    have hg := congrArg (fun φ : D.obj j ⟶ 𝓕 => φ.hom.app U xj) (c.w g)
    exact hf.trans (h.trans hg.symm)

end CategoryTheory.Sheaf

end
