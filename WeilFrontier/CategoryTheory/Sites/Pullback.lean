module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# The inverse image is left adjoint to the direct image on small étale sites

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B`. For a sheaf `G` on the small
étale site of `S` (of sets, of abelian groups, or with values in any category `A` with the
relevant colimits and sheafification), there is a morphism `η_G : G ⟶ f_* f^* G`, natural in
`G`, such that for every sheaf `F` on the small étale site of `T` the map
`Hom(f^* G, F) → Hom(G, f_* F)`, `φ ↦ f_*(φ) ∘ η_G`, is bijective: `f^*` is left adjoint to
`f_*`. Here `f^*` is `AlgebraicGeometry.smallEtaleInverseImage` and
`f_*` is `AlgebraicGeometry.BigEtaleSite.smallPushforward`, `(f_* F)(U) = F(T ×_S U)`.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageUnit` — the natural transformation
  `η : 𝟭 ⟶ f^* ⋙ f_*`.

## Main results

* `AlgebraicGeometry.bijective_smallPushforward_map_comp_smallEtaleInverseImageUnit` — for all
  `G` and `F`, the map `φ ↦ η_G ≫ f_*(φ)` is a bijection
  `Hom(f^* G, F) ≃ Hom(G, f_* F)`.
* `AlgebraicGeometry.smallEtaleInverseImageHomEquiv` — this bijection as an equivalence, natural
  in both variables.

## Implementation notes

The unit `η` is the unit of the adjunction `AlgebraicGeometry.smallEtaleInverseImageAdjunction`,
which is Mathlib's `CategoryTheory.Functor.sheafAdjunctionContinuous` for base change
`AlgebraicGeometry.smallEtaleBaseChange B f`. The source's proof identifies both hom sets with
compatible families `G(U) → F(V)` indexed by triples `(V, U, h)`; the adjunction obtained from
the presheaf-level left Kan extension and sheafification is the same bijection, since the
inverse image is, canonically, the sheafification of the inverse image presheaf
(`AlgebraicGeometry.smallEtaleInverseImageIsoSheafify`). The statement covers sheaves of sets
(`A = Type (u + 1)`) and of abelian groups (`A = AddCommGrpCat.{u + 1}`) as special cases.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03Q0](https://stacks.math.columbia.edu/tag/03Q0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **The unit `η : G ⟶ f_* f^* G`** of the inverse image, natural in the sheaf `G` on the small
étale site of `S`. -/
@[weil "prop_fk102_inverse_image_adjunction"]
abbrev smallEtaleInverseImageUnit :
    𝟭 (Sheaf (SmallEtale.topology B S.obj S.property) A) ⟶
      smallEtaleInverseImage B f A ⋙ B.smallPushforward f A :=
  (smallEtaleInverseImageAdjunction B f A).unit

/-- **`f^*` is left adjoint to `f_*`.** For sheaves `G` on the small étale site of `S` and `F`
on the small étale site of `T`, the map `Hom(f^* G, F) → Hom(G, f_* F)`,
`φ ↦ f_*(φ) ∘ η_G`, is bijective. -/
@[weil "prop_fk102_inverse_image_adjunction"]
theorem bijective_smallPushforward_map_comp_smallEtaleInverseImageUnit
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) A) :
    Function.Bijective fun φ : (smallEtaleInverseImage B f A).obj G ⟶ F ↦
      (smallEtaleInverseImageUnit B f A).app G ≫ (B.smallPushforward f A).map φ := by
  convert ((smallEtaleInverseImageAdjunction B f A).homEquiv G F).bijective using 1
  funext φ
  exact ((smallEtaleInverseImageAdjunction B f A).homEquiv_unit G F φ).symm

/-- The bijection `Hom(f^* G, F) ≃ Hom(G, f_* F)`, `φ ↦ f_*(φ) ∘ η_G`. -/
abbrev smallEtaleInverseImageHomEquiv
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) A) :
    ((smallEtaleInverseImage B f A).obj G ⟶ F) ≃ (G ⟶ (B.smallPushforward f A).obj F) :=
  (smallEtaleInverseImageAdjunction B f A).homEquiv G F

lemma smallEtaleInverseImageHomEquiv_apply
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) A)
    (φ : (smallEtaleInverseImage B f A).obj G ⟶ F) :
    smallEtaleInverseImageHomEquiv B f A G F φ =
      (smallEtaleInverseImageUnit B f A).app G ≫ (B.smallPushforward f A).map φ :=
  (smallEtaleInverseImageAdjunction B f A).homEquiv_unit G F φ

/-- The bijection `Hom(f^* G, F) ≃ Hom(G, f_* F)` is natural in `G`. -/
lemma smallEtaleInverseImageHomEquiv_naturality_left
    {G' G : Sheaf (SmallEtale.topology B S.obj S.property) A}
    {F : Sheaf (SmallEtale.topology B T.obj T.property) A} (g : G' ⟶ G)
    (φ : (smallEtaleInverseImage B f A).obj G ⟶ F) :
    smallEtaleInverseImageHomEquiv B f A G' F ((smallEtaleInverseImage B f A).map g ≫ φ) =
      g ≫ smallEtaleInverseImageHomEquiv B f A G F φ :=
  (smallEtaleInverseImageAdjunction B f A).homEquiv_naturality_left g φ

/-- The bijection `Hom(f^* G, F) ≃ Hom(G, f_* F)` is natural in `F`. -/
lemma smallEtaleInverseImageHomEquiv_naturality_right
    {G : Sheaf (SmallEtale.topology B S.obj S.property) A}
    {F F' : Sheaf (SmallEtale.topology B T.obj T.property) A}
    (φ : (smallEtaleInverseImage B f A).obj G ⟶ F) (ψ : F ⟶ F') :
    smallEtaleInverseImageHomEquiv B f A G F' (φ ≫ ψ) =
      smallEtaleInverseImageHomEquiv B f A G F φ ≫ (B.smallPushforward f A).map ψ :=
  (smallEtaleInverseImageAdjunction B f A).homEquiv_naturality_right φ ψ

end AlgebraicGeometry

end
