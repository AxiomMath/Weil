module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Abelian.ArKernel
public import WeilFrontier.CategoryTheory.Abelian.SerreClass.ArCategoryAbelian
public import WeilFrontier.CategoryTheory.Abelian.SerreClass.Localization
public import WeilFrontier.CategoryTheory.Abelian.Subcategory
public import WeilFrontier.CategoryTheory.Preadditive.ArZeroObjectIffNull
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArIsomorphism
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.NullSystem

/-!
# A–R isomorphisms via kernels and cokernels

Let `𝒫` be the abelian category of projective systems of `l`-power torsion `Λ`-modules. A
morphism `f : F[r] ⟶ G` of `𝒫` represents an A–R isomorphism if and only if its kernel and its
cokernel in `𝒫` are null systems. Indeed, in the abelian A–R category a morphism is an
isomorphism iff its kernel and cokernel are zero objects; a kernel of `[r, f]` has source
`ker f` and a cokernel has target `coker f`, and these are zero objects of the A–R category iff
they are null systems.

## Main results

* `CategoryTheory.ProjectiveSystem.representsArIso_iff_isNull_kernel_and_isNull_cokernel`:
  `f : F[r] ⟶ G` represents an A–R isomorphism iff `ker f` and `coker f` are null systems.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- **A–R isomorphisms via kernel and cokernel.** A morphism `f : F[r] ⟶ G` of projective
systems represents an A–R isomorphism if and only if its kernel and its cokernel in the
category of projective systems are null systems. -/
@[weil "lem_fk112_ar_isomorphism_iff_kernel_cokernel_null"]
theorem representsArIso_iff_isNull_kernel_and_isNull_cokernel {F G : ProjectiveSystem.{v} Λ l}
    (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) :
    RepresentsArIso r f ↔ isNull (kernel f) ∧ isNull (cokernel f) := by
  have eK : ArCategory.of (kernel f) ≅ kernel (ArCategory.homMk r f) :=
    IsLimit.conePointUniqueUpToIso (ArCategory.isLimitKernelForkHomMkKernelι f)
      (limit.isLimit _)
  have eC : ArCategory.of (cokernel f) ≅ cokernel (ArCategory.homMk r f) :=
    IsColimit.coconePointUniqueUpToIso
      (ArCategory.isColimitCokernelCoforkHomMk (w := cokernel.condition f) (cokernelIsCokernel f))
      (colimit.isColimit _)
  rw [representsArIso_iff, ← ArCategory.isZero_of_iff_isNull, ← ArCategory.isZero_of_iff_isNull,
    eK.isZero_iff, eC.isZero_iff, ← Preadditive.mono_iff_isZero_kernel,
    ← Preadditive.epi_iff_isZero_cokernel]
  exact ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => isIso_of_mono_of_epi _⟩

end ProjectiveSystem

end CategoryTheory
