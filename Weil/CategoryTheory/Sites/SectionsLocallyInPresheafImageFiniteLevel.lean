module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.CokernelOfPairIsCoequalizer
public import Weil.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Sections of the target of an epimorphism of étale sheaves lie locally in its image

Let `φ : F ⟶ G` be an epimorphism of sheaves of sets on the small étale site of a scheme `X`.
For finitely many sections of `G` over an étale `X`-scheme `U`, here two sections `s` and `s'`,
there is a single surjective étale morphism `V ⟶ U` along which both restrictions lie in the
presheaf image `V ↦ φ_V(F(V))` of `φ` (`CategoryTheory.Subfunctor.range`).

This applies to the canonical map `c : G ⟶ Coker(u, v)` onto the cokernel of a pair of
morphisms of sheaves, which is a coequalizer and hence an epimorphism, and to its image under
any functor which is a left adjoint, such as the inverse image along a morphism of schemes.

## Main results

* `AlgebraicGeometry.Scheme.exists_surjective_map_mem_range_of_epi`: two sections of the target
  of an epimorphism of étale sheaves lie in its presheaf image after restriction along one
  surjective étale morphism.
* `AlgebraicGeometry.Scheme.exists_surjective_map_mem_range_map_pairCokernelπ`: the same for the
  image of the canonical map onto the cokernel of a pair under a left adjoint functor.

## Implementation notes

Freitag and Kiehl state the second result in a presentation along a projective system of
schemes: `G_{α₁}` is the inverse image of the cokernel of a pair of representable sheaves on
`X_{α₀}`, and `π_{α₁}` is the inverse image of the canonical map. The statement here is for an
arbitrary pair of morphisms of sheaves and an arbitrary left adjoint functor between the
categories of étale sheaves, which contains that case. Instead of the fibre product of two
surjective étale morphisms used by Freitag and Kiehl, the second morphism is taken over the
first, and the composite is surjective.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.4.17 2).
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- For an epimorphism `φ : F ⟶ G` of sheaves of sets on the small étale site of `X` and two
sections `s, s'` of `G` over `U`, there is a surjective étale morphism `f : V ⟶ U` such that
both `s|_V` and `s'|_V` lie in the presheaf image of `φ`. -/
theorem exists_surjective_map_mem_range_of_epi {X : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology (Type w)] {F G : Sheaf X.smallEtaleTopology (Type w)}
    (φ : F ⟶ G) [Epi φ] (U : X.Etale) (s s' : G.obj.obj (op U)) :
    ∃ (V : X.Etale) (f : V ⟶ U), Surjective f.left ∧
      G.obj.map f.op s ∈ (Subfunctor.range φ.hom).obj (op V) ∧
      G.obj.map f.op s' ∈ (Subfunctor.range φ.hom).obj (op V) := by
  have h := (epi_iff_forall_exists_surjective φ).1 inferInstance
  obtain ⟨V₁, f₁, hf₁, t₁, ht₁⟩ := h U s
  obtain ⟨V₂, f₂, hf₂, t₂, ht₂⟩ := h V₁ (G.obj.map f₁.op s')
  refine ⟨V₂, f₂ ≫ f₁, ?_, ⟨F.obj.map f₂.op t₁, ?_⟩, ⟨t₂, ?_⟩⟩
  · change Surjective (f₂.left ≫ f₁.left)
    infer_instance
  · rw [NatTrans.naturality_apply, ht₁, op_comp, Functor.map_comp_apply]
  · rw [ht₂, op_comp, Functor.map_comp_apply]

/-- **Sections lie locally in the presheaf image of the projection onto a cokernel.**
Let `u v : R ⟶ H` be morphisms of sheaves of sets on the small étale site of `X`, let
`π : H ⟶ Coker(u, v)` be the canonical map onto their cokernel, and let `P` be a left adjoint
functor from étale sheaves on `X` to étale sheaves on `Y` (for instance the inverse image along
a morphism `Y ⟶ X`). For two sections `s, s'` of `P(Coker(u, v))` over an étale `Y`-scheme `U`
there is a surjective étale morphism `V ⟶ U` such that `s|_V` and `s'|_V` lie in the presheaf
image of `P(π)`. -/
@[weil "lem_fk104_sections_locally_in_presheaf_image_finite_level"]
theorem exists_surjective_map_mem_range_map_pairCokernelπ {X Y : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology (Type w)] [HasSheafify Y.smallEtaleTopology (Type w')]
    {R H : Sheaf X.smallEtaleTopology (Type w)} (u v : R ⟶ H)
    (P : Sheaf X.smallEtaleTopology (Type w) ⥤ Sheaf Y.smallEtaleTopology (Type w'))
    [P.IsLeftAdjoint] (U : Y.Etale)
    (s s' : (P.obj (Sheaf.pairCokernel u v)).obj.obj (op U)) :
    ∃ (V : Y.Etale) (f : V ⟶ U), Surjective f.left ∧
      (P.obj (Sheaf.pairCokernel u v)).obj.map f.op s ∈
        (Subfunctor.range (P.map (Sheaf.pairCokernelπ u v)).hom).obj (op V) ∧
      (P.obj (Sheaf.pairCokernel u v)).obj.map f.op s' ∈
        (Subfunctor.range (P.map (Sheaf.pairCokernelπ u v)).hom).obj (op V) := by
  have : Epi (Sheaf.pairCokernelπ u v) :=
    epi_of_isColimit_cofork (Sheaf.isColimitPairCokernelCofork u v)
  exact exists_surjective_map_mem_range_of_epi _ U s s'

end AlgebraicGeometry.Scheme
