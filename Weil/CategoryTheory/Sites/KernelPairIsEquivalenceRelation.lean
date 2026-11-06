module

public import Weil.Attr
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Weil.CategoryTheory.Sites.Limits

/-!
# The kernel pair of a morphism of sheaves of sets is an equivalence relation

Let `φ : G ⟶ H` be a morphism of sheaves of sets on a site `(C, J)`, and let
`p₁, p₂ : G ×_H G ⟶ G` be the two projections of the sectionwise fibre product
`U ↦ G(U) ×_{H(U)} G(U)`. Then `p₁, p₂` is an equivalence relation on `G`, in two senses:

* internally, in the category of sheaves of sets: the pair is an
  `CategoryTheory.EquivalenceRelation` (it is jointly monic, with reflexivity, symmetry and
  transitivity morphisms), since it is a kernel pair of `φ`;
* sectionwise: for every object `U`, the map `(p₁, p₂) : (G ×_H G)(U) → G(U) × G(U)` is
  injective, and its image, the relation `φ_U(s) = φ_U(t)`, is an equivalence relation on `G(U)`.

## Main results

* `CategoryTheory.Sheaf.isKernelPair_sectionwisePullbackCone`: the projections of the
  sectionwise fibre product `G ×_H G` are a kernel pair of `φ`.
* `CategoryTheory.Sheaf.sectionwiseKernelPairEquivalenceRelation`: the projections form an
  internal equivalence relation in `Sheaf J (Type w)`.
* `CategoryTheory.Sheaf.isEquivalenceRelation_sectionwiseKernelPair`: the same, as a `Prop`.
* `CategoryTheory.Sheaf.injective_sectionwiseKernelPair_app`: on sections over every `U`, the map
  `(p₁, p₂)` is injective.
* `CategoryTheory.Sheaf.equivalence_sectionwiseKernelPair_app`: on sections over every `U`, the
  image of `(p₁, p₂)` is an equivalence relation on `G(U)`.
* `CategoryTheory.Sheaf.sectionwiseKernelPair_app_rel_iff`: that image is the relation
  `φ_U(s) = φ_U(t)`.

## Implementation notes

The statement is proved for an arbitrary Grothendieck topology; the étale site of a scheme is a
special case. An equivalence relation on a sheaf of sets is stated in two equivalent forms: as
Mathlib's internal `CategoryTheory.EquivalenceRelation` in `Sheaf J (Type w)`, and sectionwise
(injectivity of `(p₁, p₂)` on sections, and the image being an equivalence relation).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G H : Sheaf J (Type w)} (φ : G ⟶ H)

/-- The two projections of the sectionwise fibre product `G ×_H G` are a kernel pair of `φ`. -/
theorem isKernelPair_sectionwisePullbackCone :
    IsKernelPair φ (sectionwisePullbackCone φ φ).fst (sectionwisePullbackCone φ φ).snd :=
  IsPullback.of_isLimit (isLimitSectionwisePullbackCone φ φ)

/-- **The projections `p₁, p₂ : G ×_H G ⟶ G` of the sectionwise fibre product form an internal
equivalence relation in the category of sheaves of sets.** -/
@[weil "lem_fk104_kernel_pair_is_equivalence_relation"]
noncomputable def sectionwiseKernelPairEquivalenceRelation :
    EquivalenceRelation (sectionwisePullbackCone φ φ).fst (sectionwisePullbackCone φ φ).snd :=
  IsKernelPair.equivalenceRelation φ _ _
    (isLimitSectionwisePullbackCone (sectionwisePullbackCone φ φ).snd
      (sectionwisePullbackCone φ φ).fst)
    (isKernelPair_sectionwisePullbackCone φ)

/-- The projections `p₁, p₂ : G ×_H G ⟶ G` are an equivalence relation on `G`. -/
@[weil "lem_fk104_kernel_pair_is_equivalence_relation"]
theorem isEquivalenceRelation_sectionwiseKernelPair :
    IsEquivalenceRelation (sectionwisePullbackCone φ φ).fst (sectionwisePullbackCone φ φ).snd :=
  (sectionwiseKernelPairEquivalenceRelation φ).isEquivalenceRelation

/-- On sections over `U`, the map `(p₁, p₂) : (G ×_H G)(U) → G(U) × G(U)` is injective. -/
@[weil "lem_fk104_kernel_pair_is_equivalence_relation"]
theorem injective_sectionwiseKernelPair_app (U : Cᵒᵖ) :
    Function.Injective fun x : (sectionwisePullbackCone φ φ).pt.obj.obj U =>
      ((sectionwisePullbackCone φ φ).fst.hom.app U x,
        (sectionwisePullbackCone φ φ).snd.hom.app U x) := by
  intro x y h
  exact Subtype.ext h

/-- On sections over `U`, two sections are related by the image of `(p₁, p₂)` exactly when they
have the same image under `φ_U`. -/
theorem sectionwiseKernelPair_app_rel_iff (U : Cᵒᵖ) (s t : G.obj.obj U) :
    (∃ x : (sectionwisePullbackCone φ φ).pt.obj.obj U,
        (sectionwisePullbackCone φ φ).fst.hom.app U x = s ∧
          (sectionwisePullbackCone φ φ).snd.hom.app U x = t) ↔
      φ.hom.app U s = φ.hom.app U t := by
  constructor
  · rintro ⟨x, rfl, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨(s, t), h⟩, rfl, rfl⟩

/-- On sections over `U`, the image of `(p₁, p₂)` is an equivalence relation on `G(U)`. -/
@[weil "lem_fk104_kernel_pair_is_equivalence_relation"]
theorem equivalence_sectionwiseKernelPair_app (U : Cᵒᵖ) :
    _root_.Equivalence fun s t : G.obj.obj U =>
      ∃ x : (sectionwisePullbackCone φ φ).pt.obj.obj U,
        (sectionwisePullbackCone φ φ).fst.hom.app U x = s ∧
          (sectionwisePullbackCone φ φ).snd.hom.app U x = t := by
  simp only [sectionwiseKernelPair_app_rel_iff]
  exact ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

end CategoryTheory.Sheaf
