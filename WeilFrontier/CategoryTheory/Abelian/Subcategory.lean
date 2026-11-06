module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.FullSubcategory
public import Weil.Attr

/-!
# The category of projective systems of torsion modules is abelian

Let `Λ` be a commutative ring and `l ∈ Λ`. The category `CategoryTheory.ProjectiveSystem Λ l` of
projective systems `(F_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules vanishing in sufficiently
negative degrees is a full subcategory of the abelian functor category `ℤᵒᵖ ⥤ ModuleCat Λ`. It
contains `0` and is closed under subobjects, quotients and finite products (submodules,
quotients and finite products of `l`-power torsion modules are `l`-power torsion, and they vanish
where the given systems vanish). Hence it is abelian, and its kernels, cokernels and images are
computed degreewise: the `n`-th term of the kernel (cokernel, image) of `f` is the kernel
(cokernel, image) of `f_n`, compatibly with the induced maps. A short complex is exact if and
only if it is exact in every degree.

## Main results

* `CategoryTheory.ProjectiveSystem.instAbelian`: projective systems form an abelian category.
* `CategoryTheory.ProjectiveSystem.kernelIso`, `CategoryTheory.ProjectiveSystem.cokernelIso`,
  `CategoryTheory.ProjectiveSystem.imageIso`: kernels, cokernels and images are degreewise.
* `CategoryTheory.ProjectiveSystem.shortComplex_exact_iff`: exactness is degreewise.

## Implementation notes

The image of a morphism is `Abelian.image`, the kernel of its cokernel. The degreewise
statements are expressed through the exact functor
`CategoryTheory.ProjectiveSystem.termFunctor n : F ↦ F_n`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

section Closure

variable (Λ l)

/-- A zero functor is a projective system of torsion modules. -/
lemma isTorsionBounded_of_isZero {F : ℤᵒᵖ ⥤ ModuleCat.{v} Λ} (hF : IsZero F) :
    isTorsionBounded Λ l F := by
  have h : ∀ n : ℤ, IsZero (F.obj (op n)) := fun n => hF.obj _
  refine ⟨fun n x => ⟨1, ?_⟩, 0, fun n _ => h n⟩
  have : Subsingleton (F.obj (op n)) := ModuleCat.subsingleton_of_isZero (h n)
  exact Subsingleton.elim _ _

instance : (isTorsionBounded.{v} Λ l).ContainsZero where
  exists_zero := ⟨_, isZero_zero _, isTorsionBounded_of_isZero Λ l (isZero_zero _)⟩

instance : (isTorsionBounded.{v} Λ l).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    have hinj : ∀ n : ℤ, Function.Injective (f.app (op n)) := fun n =>
      (ModuleCat.mono_iff_injective _).1
        ((NatTrans.mono_iff_mono_app' (η := f)).1 inferInstance (op n))
    refine ⟨fun n x => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hY.1 n (x := f.app (op n) x)
      refine ⟨a, hinj n ?_⟩
      rw [map_zero]
      exact ((f.app (op n)).hom.map_smul a.1 x).trans ha
    · obtain ⟨n₀, h⟩ := hY.2
      refine ⟨n₀, fun n hn => ?_⟩
      have := (NatTrans.mono_iff_mono_app' (η := f)).1 inferInstance (op n)
      exact (h n hn).of_mono (f.app (op n))

instance : (isTorsionBounded.{v} Λ l).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    have hsurj : ∀ n : ℤ, Function.Surjective (f.app (op n)) := fun n =>
      (ModuleCat.epi_iff_surjective _).1
        ((NatTrans.epi_iff_epi_app' (η := f)).1 inferInstance (op n))
    refine ⟨fun n y => ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := hsurj n y
      obtain ⟨a, ha⟩ := hX.1 n (x := x)
      refine ⟨a, ?_⟩
      have ha' : (a : Λ) • x = 0 := ha
      exact ((f.app (op n)).hom.map_smul a.1 x).symm.trans (by rw [ha', map_zero])
    · obtain ⟨n₀, h⟩ := hX.2
      refine ⟨n₀, fun n hn => ?_⟩
      have := (NatTrans.epi_iff_epi_app' (η := f)).1 inferInstance (op n)
      exact (h n hn).of_epi (f.app (op n))

instance (J : Type) [Finite J] :
    (isTorsionBounded.{v} Λ l).IsClosedUnderLimitsOfShape (Discrete J) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have := Fintype.ofFinite J
    have hn : ∀ n : ℤ, IsLimit (((evaluation ℤᵒᵖ (ModuleCat.{v} Λ)).obj (op n)).mapCone
        (Cone.mk _ p.π)) := fun n => isLimitOfPreserves _ p.isLimit
    have hext : ∀ (n : ℤ) (x y : X.obj (op n)),
        (∀ j, (p.π.app j).app (op n) x = (p.π.app j).app (op n) y) → x = y :=
      fun n x y h => Concrete.isLimit_ext _ (hn n) x y h
    refine ⟨fun n x => ?_, ?_⟩
    · choose k hk using fun j => (p.prop_diag_obj j).1 n (x := (p.π.app j).app (op n) x)
      refine ⟨∏ j, k j, hext n _ _ fun j => ?_⟩
      rw [map_zero]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ j)
      have hkj : (k j : Λ) • (p.π.app j).app (op n) x = 0 := hk j
      rw [hc, mul_comm, mul_smul]
      change (p.π.app j).app (op n) ((c : Λ) • (k j : Λ) • x) = 0
      rw [map_smul, map_smul, hkj, smul_zero]
    · choose n₀ hn₀ using fun j => (p.prop_diag_obj j).2
      refine ⟨-∑ j, |n₀ j|, fun n hn => ?_⟩
      have hz : ∀ j, IsZero ((p.diag.obj j).obj (op n)) := fun j => hn₀ j n (by
        have := Finset.single_le_sum (f := fun j => |n₀ j|) (fun j _ => abs_nonneg (n₀ j))
          (Finset.mem_univ j)
        have := neg_abs_le (n₀ j)
        omega)
      refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => hext n x y fun j => ?_⟩
      have := ModuleCat.isZero_iff_subsingleton.mp (hz j)
      exact Subsingleton.elim _ _

instance : (isTorsionBounded.{v} Λ l).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := inferInstance

end Closure

/-- **Projective systems form an abelian category.** -/
@[weil "lem_fk112_projective_systems_abelian"]
noncomputable instance instAbelian : Abelian (ProjectiveSystem.{v} Λ l) := inferInstance

/-- The functor `F ↦ F_n` from projective systems to `Λ`-modules. -/
abbrev termFunctor (n : ℤ) : ProjectiveSystem.{v} Λ l ⥤ ModuleCat.{v} Λ :=
  (isTorsionBounded.{v} Λ l).ι ⋙ (evaluation ℤᵒᵖ (ModuleCat.{v} Λ)).obj (op n)

instance : PreservesFiniteLimits (isTorsionBounded.{v} Λ l).ι :=
  have := (isTorsionBounded.{v} Λ l).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels _

instance : PreservesFiniteColimits (isTorsionBounded.{v} Λ l).ι :=
  have := (isTorsionBounded.{v} Λ l).preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels _

instance (n : ℤ) : PreservesFiniteLimits (termFunctor.{v} (Λ := Λ) (l := l) n) :=
  comp_preservesFiniteLimits _ _

instance (n : ℤ) : PreservesFiniteColimits (termFunctor.{v} (Λ := Λ) (l := l) n) :=
  comp_preservesFiniteColimits _ _

variable {F G : ProjectiveSystem.{v} Λ l}

/-- The `n`-th term of the kernel of `f` is the kernel of `f_n`. -/
@[weil "lem_fk112_projective_systems_abelian"]
noncomputable def kernelIso (f : F ⟶ G) (n : ℤ) : (kernel f).term n ≅ kernel (app f n) :=
  PreservesKernel.iso (termFunctor n) f

@[weil "lem_fk112_projective_systems_abelian", reassoc (attr := simp)]
lemma kernelIso_hom_ι (f : F ⟶ G) (n : ℤ) :
    (kernelIso f n).hom ≫ kernel.ι (app f n) = app (kernel.ι f) n := by
  simpa [kernelIso] using kernelComparison_comp_ι f (termFunctor n)

/-- The `n`-th term of the cokernel of `f` is the cokernel of `f_n`. -/
@[weil "lem_fk112_projective_systems_abelian"]
noncomputable def cokernelIso (f : F ⟶ G) (n : ℤ) : (cokernel f).term n ≅ cokernel (app f n) :=
  PreservesCokernel.iso (termFunctor n) f

@[weil "lem_fk112_projective_systems_abelian", reassoc (attr := simp)]
lemma π_cokernelIso_hom (f : F ⟶ G) (n : ℤ) :
    app (cokernel.π f) n ≫ (cokernelIso f n).hom = cokernel.π (app f n) :=
  PreservesCokernel.π_iso_hom (termFunctor n) f

/-- The `n`-th term of the image of `f` is the image of `f_n`. -/
@[weil "lem_fk112_projective_systems_abelian"]
noncomputable def imageIso (f : F ⟶ G) (n : ℤ) :
    (Abelian.image f).term n ≅ Abelian.image (app f n) :=
  Abelian.PreservesImage.iso (termFunctor n) f

@[weil "lem_fk112_projective_systems_abelian", reassoc (attr := simp)]
lemma imageIso_hom_ι (f : F ⟶ G) (n : ℤ) :
    (imageIso f n).hom ≫ Abelian.image.ι (app f n) = app (Abelian.image.ι f) n :=
  Abelian.PreservesImage.iso_hom_ι (termFunctor n) f

@[weil "lem_fk112_projective_systems_abelian", reassoc (attr := simp)]
lemma factorThruImage_imageIso_hom (f : F ⟶ G) (n : ℤ) :
    app (Abelian.factorThruImage f) n ≫ (imageIso f n).hom =
      Abelian.factorThruImage (app f n) :=
  Abelian.PreservesImage.factorThruImage_iso_hom (termFunctor n) f

/-- A short complex of projective systems is exact if and only if it is exact in every
degree. -/
@[weil "lem_fk112_projective_systems_abelian"]
theorem shortComplex_exact_iff (S : ShortComplex (ProjectiveSystem.{v} Λ l)) :
    S.Exact ↔ ∀ n : ℤ, (S.map (termFunctor n)).Exact := by
  refine ⟨fun h n => h.map (termFunctor n), fun h => ?_⟩
  rw [← S.exact_map_iff_of_faithful (isTorsionBounded.{v} Λ l).ι,
    ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
  rintro ⟨n⟩
  exact .of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (h n))
    ((S.map (isTorsionBounded.{v} Λ l).ι).mapHomologyIso
      ((evaluation ℤᵒᵖ (ModuleCat.{v} Λ)).obj (op n))).symm

end ProjectiveSystem

end CategoryTheory
