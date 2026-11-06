module

public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Weil.Attr

/-!
# An epimorphism of sheaves of sets is the cokernel of its kernel pair

Let `φ : G ⟶ H` be an epimorphism of sheaves of sets on a site `(C, J)`, let
`p₁ p₂ : G ×_H G ⟶ G` be the two projections of the fibre product, and let `c : G ⟶ Q` be the
cokernel (coequalizer) of `p₁` and `p₂`. Then the unique morphism `ψ : Q ⟶ H` with `c ≫ ψ = φ`
is an isomorphism.

Every epimorphism in the category of sheaves of sets is a regular epimorphism, and a regular
epimorphism is a coequalizer of its kernel pair; two colimit coforks of the same pair are
identified by the morphism induced by the universal property.

## Main results

* `CategoryTheory.Sheaf.isIso_desc_of_isKernelPair`: the statement for any kernel pair of `φ`
  and any colimit cofork of it.
* `CategoryTheory.Sheaf.isIso_coequalizer_desc_pullback`: the statement for the chosen fibre
  product `pullback φ φ` and the chosen coequalizer.

## Implementation notes

The statement is proved for an arbitrary site on which type-valued presheaves can be
sheafified (`HasSheafify J (Type w)`); Freitag–Kiehl state it for the étale site of a scheme.
The kernel pair is any limit cone of the cospan `(φ, φ)` (`IsKernelPair`), which covers both
Mathlib's chosen `pullback φ φ` and the sectionwise fibre product
`CategoryTheory.Sheaf.sectionwisePullbackCone` (by
`CategoryTheory.Sheaf.isLimitSectionwisePullbackCone`). The cokernel of a pair of sheaf morphisms
is the coequalizer in the category of sheaves, i.e. any colimit cofork.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J (Type w)]

namespace Sheaf

/-- **An epimorphism of sheaves of sets is the cokernel of its kernel pair** (Freitag–Kiehl I.4):
if `φ : G ⟶ H` is an epimorphism of sheaves of sets, `(p₁, p₂)` is a kernel pair of `φ` and
`c` is a coequalizer of `p₁` and `p₂`, then the morphism `ψ : c.pt ⟶ H` with `c.π ≫ ψ = φ`
given by the universal property of `c` is an isomorphism. -/
@[weil "lem_fk104_epi_is_cokernel_of_kernel_pair"]
theorem isIso_desc_of_isKernelPair {K G H : Sheaf J (Type w)} (φ : G ⟶ H) [Epi φ]
    {p₁ p₂ : K ⟶ G} (hk : IsKernelPair φ p₁ p₂) {c : Cofork p₁ p₂} (hc : IsColimit c) :
    IsIso (hc.desc (Cofork.ofπ φ hk.w)) := by
  have : IsRegularEpi φ := IsRegularEpiCategory.regularEpiOfEpi φ
  have h := (hc.coconePointUniqueUpToIso hk.toCoequalizer').isIso_hom
  exact h

/-- **An epimorphism of sheaves of sets is the cokernel of its kernel pair**, for the chosen
fibre product and coequalizer: if `φ : G ⟶ H` is an epimorphism of sheaves of sets, the morphism
`coequalizer (pullback.fst φ φ) (pullback.snd φ φ) ⟶ H` induced by `φ` is an isomorphism. -/
@[weil "lem_fk104_epi_is_cokernel_of_kernel_pair"]
theorem isIso_coequalizer_desc_pullback {G H : Sheaf J (Type w)} (φ : G ⟶ H) [Epi φ]
    [HasPullback φ φ] [HasCoequalizer (pullback.fst φ φ) (pullback.snd φ φ)] :
    IsIso (coequalizer.desc φ pullback.condition :
      coequalizer (pullback.fst φ φ) (pullback.snd φ φ) ⟶ H) :=
  isIso_desc_of_isKernelPair φ (IsKernelPair.of_hasPullback φ) (coequalizerIsCoequalizer _ _)

end Sheaf

end CategoryTheory
