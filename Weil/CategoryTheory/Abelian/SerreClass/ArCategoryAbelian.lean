module

public import Weil.Attr
public import Weil.CategoryTheory.Abelian.ArKernel
public import Weil.Defs.CategoryTheory.ObjectProperty.ArIsomorphism
public import Weil.Defs.CategoryTheory.ObjectProperty.NullSystem
public import Weil.CategoryTheory.Preadditive.Biproducts
public import Weil.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# The Artin–Rees category is abelian

Let `𝒫` be the abelian category of projective systems of `l`-power torsion `Λ`-modules, `AR` its
Artin–Rees category and `q : 𝒫 ⥤ AR` the canonical functor. We show that `AR` is an abelian
category.

Every A–R morphism `[r, f] : F ⟶ G`, with `f : F[r] ⟶ G`, is `q(f) ∘ [r, id_{F[r]}]`, and `[r,
id_{F[r]}] : F ⟶ F[r]` is the inverse of the isomorphism `q(ε^r_F)` (`shiftIso`), and `q(f) = 0` if
and only if `f ∘ ε^t_F = 0` for some `t` (`toArCategory_map_eq_zero_iff`). From these two facts, `q`
preserves monomorphisms, epimorphisms, kernels and cokernels: for `f` in `𝒫`, `q(ker f) ⟶ q(F)` is a
kernel and `q(G) ⟶ q(coker f)` a cokernel of `q(f)`. Hence every morphism of `AR`, being isomorphic
as an arrow to some `q(f)`, has a kernel and a cokernel, and its canonical morphism from the coimage
to the image is isomorphic to `q` of the one of `f`, an isomorphism since `𝒫` is abelian. With the
finite biproducts of `AR`, this makes `AR` abelian.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.exists_eq_shiftIso_inv_comp`: every A–R morphism
  `F ⟶ Y` is `q(f) ∘ q(ε^r_F)⁻¹` for some `r` and `f : F[r] ⟶ Y`.
* `CategoryTheory.ProjectiveSystem.ArCategory.toArCategory_map_comp_shiftIso_inv`: the
  isomorphisms `q(ε^r_F)⁻¹ : F ≅ F[r]` are natural in `F`.
* `CategoryTheory.ProjectiveSystem.toArCategory_preservesKernel`,
  `CategoryTheory.ProjectiveSystem.toArCategory_preservesCokernel`: `q` preserves kernels and
  cokernels.
* `CategoryTheory.ProjectiveSystem.ArCategory.isIso_coimageImageComparison`: in the A–R category
  the canonical morphism from the coimage to the image is an isomorphism.
* `CategoryTheory.ProjectiveSystem.ArCategory.abelian`: the A–R category is abelian.

## Implementation notes

The abelian structure is built with `Abelian.ofCoimageImageComparisonIsIso` on the preadditive
structure `ArCategory.preadditive`, so its underlying preadditive structure is that one. The
source reduces the coimage–image comparison of an arbitrary morphism to that of some `q(f)` by
composing with an isomorphism; here this is the functoriality of the comparison
(`Abelian.coimageImageComparisonFunctor`) applied to an isomorphism of arrows, and the
comparison for `q(f)` is `q` of the one for `f` because `q` preserves kernels and cokernels
(`Abelian.PreservesCoimageImageComparison.iso`).

The A–R category is also the Serre quotient of `𝒫` by the null systems, and Mathlib's
`ObjectProperty.SerreClassLocalization.abelian` would give an abelian structure once `q` is shown
to be a localization functor; the direct construction here does not need that comparison.

The objects `q(F)` and `ArCategory.of F` agree only after unfolding `toArCategory`, which makes
rewriting with lemmas about one inside morphisms typed with the other fail at the instances
transparency; the file therefore disables `backward.isDefEq.respectTransparency`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

set_option backward.isDefEq.respectTransparency false

namespace ArCategory

/-- Every A–R morphism `φ : F ⟶ Y` is `q(f) ∘ [r, id_{F[r]}]` for some `r` and some
`f : F[r] ⟶ Y`. -/
lemma exists_eq_shiftIso_inv_comp {F : ProjectiveSystem.{v} Λ l} {Y : ArCategory.{v} Λ l}
    (φ : of F ⟶ Y) : ∃ (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ Y.obj),
      φ = (shiftIso F r).inv ≫ (toArCategory Λ l).map f := by
  obtain ⟨r, f, rfl⟩ := homMk_surjective (G := Y.obj) φ
  exact ⟨r, f, homMk_eq_shiftIso_inv_comp f⟩

/-- The isomorphisms `F ≅ F[r]` are natural: `[r, id] ∘ q(f) = q(f[r]) ∘ [r, id]`. -/
@[reassoc]
lemma toArCategory_map_comp_shiftIso_inv {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G)
    (r : ℕ) : (toArCategory Λ l).map f ≫ (shiftIso G r).inv =
      (shiftIso F r).inv ≫ (toArCategory Λ l).map ((shift (r : ℤ)).map f) := by
  rw [← cancel_mono (shiftIso G r).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, shiftIso_hom, ← Functor.map_comp, natMap_naturality, Functor.map_comp,
    ← shiftIso_hom, Iso.inv_hom_id_assoc]

end ArCategory

open ArCategory

/-- If `q(g ∘ ε^t_F) = 0` then `q(g) = 0`. -/
lemma toArCategory_map_eq_zero_of_natMap_comp {F G : ProjectiveSystem.{v} Λ l} {t : ℕ}
    {g : F ⟶ G} (h : (toArCategory Λ l).map (natMap F t ≫ g) = 0) :
    (toArCategory Λ l).map g = 0 := by
  rw [Functor.map_comp, ← shiftIso_hom] at h
  exact (cancel_epi (shiftIso F t).hom).1 (h.trans comp_zero.symm)

/-- The canonical functor `q` preserves monomorphisms. -/
instance toArCategory_preservesMonomorphisms :
    (toArCategory.{v} Λ l).PreservesMonomorphisms where
  preserves {F G} m _ := Preadditive.mono_of_cancel_zero _ fun {P} z hz => by
    obtain ⟨r, g, rfl⟩ := exists_eq_shiftIso_inv_comp (F := P.obj) z
    rw [Category.assoc, ← Functor.map_comp] at hz
    obtain ⟨t, ht⟩ := (toArCategory_map_eq_zero_iff _).1
      ((cancel_epi _).1 (hz.trans comp_zero.symm))
    have h0 : natMap _ t ≫ g = 0 := (cancel_mono m).1 (by simpa using ht)
    rw [toArCategory_map_eq_zero_of_natMap_comp (by rw [h0, Functor.map_zero]), comp_zero]

/-- The canonical functor `q` preserves epimorphisms. -/
instance toArCategory_preservesEpimorphisms :
    (toArCategory.{v} Λ l).PreservesEpimorphisms where
  preserves {F G} p _ := Preadditive.epi_of_cancel_zero _ fun {W} z hz => by
    obtain ⟨r, g, rfl⟩ := exists_eq_shiftIso_inv_comp (F := G) z
    rw [toArCategory_map_comp_shiftIso_inv_assoc, ← Functor.map_comp] at hz
    obtain ⟨t, ht⟩ := (toArCategory_map_eq_zero_iff _).1
      ((cancel_epi _).1 (hz.trans comp_zero.symm))
    rw [← natMap_naturality_assoc] at ht
    have h0 : natMap _ t ≫ g = 0 := (cancel_epi _).1 (ht.trans comp_zero.symm)
    rw [toArCategory_map_eq_zero_of_natMap_comp (by rw [h0, Functor.map_zero]), comp_zero]

/-- The canonical functor `q` preserves kernels: `q(ker f) ⟶ q(F)` is a kernel of `q(f)`. -/
instance toArCategory_preservesKernel {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) :
    PreservesLimit (parallelPair f 0) (toArCategory.{v} Λ l) := by
  suffices ∀ (W : ArCategory.{v} Λ l) (z : W ⟶ of F) (_ : z ≫ (toArCategory Λ l).map f = 0),
      ∃ l' : W ⟶ of (kernel f), l' ≫ (toArCategory Λ l).map (kernel.ι f) = z from
    preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      ((KernelFork.isLimitMapConeEquiv _ _).2
        (Fork.IsLimit.ofExistsUnique
          (fun s ↦ existsUnique_of_exists_of_unique
            (this _ _ (KernelFork.condition s))
            (fun _ _ h₁ h₂ ↦ by simpa [cancel_mono] using h₁.trans h₂.symm))))
  intro W z hz
  obtain ⟨r, g, rfl⟩ := exists_eq_shiftIso_inv_comp (F := W.obj) z
  rw [Category.assoc, ← Functor.map_comp] at hz
  obtain ⟨t, ht⟩ := (toArCategory_map_eq_zero_iff _).1
    ((cancel_epi _).1 (hz.trans comp_zero.symm))
  refine ⟨(shiftIso W.obj r).inv ≫ (shiftIso _ t).inv ≫
    (toArCategory Λ l).map (kernel.lift f (natMap _ t ≫ g) (by simpa using ht)), ?_⟩
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, kernel.lift_ι, Functor.map_comp,
    ← shiftIso_hom, Iso.inv_hom_id_assoc]

/-- The canonical functor `q` preserves cokernels: `q(G) ⟶ q(coker f)` is a cokernel of
`q(f)`. -/
instance toArCategory_preservesCokernel {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) :
    PreservesColimit (parallelPair f 0) (toArCategory.{v} Λ l) := by
  suffices ∀ (W : ArCategory.{v} Λ l) (z : of G ⟶ W) (_ : (toArCategory Λ l).map f ≫ z = 0),
      ∃ l' : of (cokernel f) ⟶ W, (toArCategory Λ l).map (cokernel.π f) ≫ l' = z from
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).2
        (Cofork.IsColimit.ofExistsUnique
          (fun s ↦ existsUnique_of_exists_of_unique
            (this _ _ (CokernelCofork.condition s))
            (fun _ _ h₁ h₂ ↦ by simpa [cancel_epi] using h₁.trans h₂.symm))))
  intro W z hz
  obtain ⟨r, g, rfl⟩ := exists_eq_shiftIso_inv_comp (F := G) z
  rw [toArCategory_map_comp_shiftIso_inv_assoc, ← Functor.map_comp] at hz
  obtain ⟨t, ht⟩ := (toArCategory_map_eq_zero_iff _).1
    ((cancel_epi _).1 (hz.trans comp_zero.symm))
  rw [← natMap_naturality_assoc] at ht
  let T := shift.{v} (Λ := Λ) (l := l) (r : ℤ) ⋙ shift (t : ℤ)
  have hc := (CokernelCofork.isColimitMapCoconeEquiv _ T).1
    (isColimitOfPreserves T (cokernelIsCokernel f))
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc (natMap _ t ≫ g) ht
  have hd' : T.map (cokernel.π f) ≫ d = natMap _ t ≫ g := hd
  refine ⟨(shiftIso _ r).inv ≫ (shiftIso _ t).inv ≫ (toArCategory Λ l).map d, ?_⟩
  rw [toArCategory_map_comp_shiftIso_inv_assoc, toArCategory_map_comp_shiftIso_inv_assoc,
    ← Functor.map_comp]
  change (shiftIso G r).inv ≫ (shiftIso _ t).inv ≫ (toArCategory Λ l).map (T.map _ ≫ d) = _
  rw [hd', Functor.map_comp, ← shiftIso_hom, Iso.inv_hom_id_assoc]

namespace ArCategory

/-- The A–R category has kernels. -/
instance hasKernels : HasKernels (ArCategory.{v} Λ l) where
  has_limit {X Y} φ := by
    obtain ⟨r, f, rfl⟩ := exists_eq_shiftIso_inv_comp (F := X.obj) φ
    have : HasKernel ((toArCategory Λ l).map f) :=
      HasLimit.mk ⟨_, (KernelFork.isLimitMapConeEquiv _ _).1
        (isLimitOfPreserves _ (kernelIsKernel f))⟩
    infer_instance

/-- The A–R category has cokernels. -/
instance hasCokernels : HasCokernels (ArCategory.{v} Λ l) where
  has_colimit {X Y} φ := by
    obtain ⟨r, f, rfl⟩ := exists_eq_shiftIso_inv_comp (F := X.obj) φ
    have : HasCokernel ((toArCategory Λ l).map f) :=
      HasColimit.mk ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ _).1
        (isColimitOfPreserves _ (cokernelIsCokernel f))⟩
    infer_instance

/-- In the A–R category the canonical morphism from the coimage to the image of a morphism is an
isomorphism. -/
instance isIso_coimageImageComparison {X Y : ArCategory.{v} Λ l} (φ : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison φ) := by
  obtain ⟨r, f, rfl⟩ := exists_eq_shiftIso_inv_comp (F := X.obj) φ
  have e : Arrow.mk ((shiftIso X.obj r).inv ≫ (toArCategory Λ l).map f) ≅
      Arrow.mk ((toArCategory Λ l).map f) :=
    Arrow.isoMk (shiftIso X.obj r).symm (Iso.refl _) (by simp)
  have : IsIso (Abelian.coimageImageComparison ((toArCategory Λ l).map f)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Abelian.PreservesCoimageImageComparison.iso (toArCategory Λ l) f)).1
      (by simp only [MorphismProperty.isomorphisms.iff]; infer_instance)
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Abelian.coimageImageComparisonFunctor.mapIso e)).2 this

/-- **The A–R category is an abelian category.** -/
@[weil "lem_fk112_ar_category_abelian"]
noncomputable instance abelian : Abelian (ArCategory.{v} Λ l) :=
  Abelian.ofCoimageImageComparisonIsIso

end ArCategory

/-- The canonical functor `q` is left exact. -/
instance toArCategory_preservesFiniteLimits : PreservesFiniteLimits (toArCategory.{v} Λ l) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The canonical functor `q` is right exact. -/
instance toArCategory_preservesFiniteColimits : PreservesFiniteColimits (toArCategory.{v} Λ l) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

end ProjectiveSystem

end CategoryTheory
