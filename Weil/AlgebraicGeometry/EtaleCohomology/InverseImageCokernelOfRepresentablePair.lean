module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.CategoryTheory.Sites.CokernelOfPairIsCoequalizer

/-!
# The inverse image of the cokernel of a pair of representable sheaves

Let `h : T ⟶ S` be a morphism of schemes of a big étale site `B`, and let `r₁ r₂ : R ⟶ H` be
morphisms of étale `S`-schemes. Write `R' = T ×_S R`, `H' = T ×_S H` and `r'ᵢ = r_i ×_S T` for the
base changes. The inverse image `h^*` carries the cokernel of the pair of sheaf morphisms
`h_R ⇉ h_H` to the cokernel of `h_{R'} ⇉ h_{H'}`, compatibly with the projections from
`h^* h_H ≅ h_{H'}`.

The cokernel of a pair is a coequalizer in the category of sheaves of sets
(`CategoryTheory.Sheaf.isColimitPairCokernelCofork`); the inverse image is a left adjoint, so it
preserves coequalizers; and `h^* h_Z ≅ h_{T ×_S Z}` naturally in `Z`
(`AlgebraicGeometry.smallEtaleInverseImageRepresentableSheafIso`). Two coequalizers of the same
pair are isomorphic by a unique isomorphism compatible with the projections.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImagePairCokernelIso` — the isomorphism
  `h^* Coker(h_R ⇉ h_H) ≅ Coker(h_{R'} ⇉ h_{H'})`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_map_pairCokernelπ_comp_pairCokernelIso_hom` — its
  compatibility with the projections from `h^* h_H ≅ h_{H'}`.

## Implementation notes

Freitag–Kiehl state the result for noetherian separated schemes; the argument uses neither
hypothesis, and the statement is made for every morphism of the big étale site. As in
`AlgebraicGeometry.smallEtaleInverseImageRepresentableSheafIso`, the representable sheaves are
lifted to `Type (max (u + 1) w)`, the universe in which the inverse image is formed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (h : T ⟶ S)

/-- The representable sheaf `h_Z : U ↦ Hom_S(U, Z)` on the small étale site of `S`, lifted to the
universe `Type (max (u + 1) w)` in which inverse images are formed. -/
abbrev smallEtaleRepresentableSheafULift (S : B.Scheme) :
    SmallEtale B S.obj S.property ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) w)) :=
  SmallEtale.representableSheaf B S.obj S.property ⋙
    sheafCompose (SmallEtale.topology B S.obj S.property) uliftFunctor.{max (u + 1) w}

variable {R H : SmallEtale B S.obj S.property}

/-- Naturality of `h^* h_Z ≅ h_{T ×_S Z}` in `Z`, in the form used to transport coforks. -/
lemma smallEtaleRepresentableSheafULift_map_baseChange_comp_inv
    (r : R ⟶ H) :
    (smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r) ≫
        ((smallEtaleInverseImageRepresentableSheafIso.{w} B h).app H).inv =
      ((smallEtaleInverseImageRepresentableSheafIso.{w} B h).app R).inv ≫
        (smallEtaleInverseImage B h (Type (max (u + 1) w))).map
          ((smallEtaleRepresentableSheafULift.{w} B S).map r) :=
  (smallEtaleInverseImageRepresentableSheafIso.{w} B h).inv.naturality r

variable (r₁ r₂ : R ⟶ H)

/-- The image under `h^*` of the cokernel cofork of `h_R ⇉ h_H`, regarded as a cofork of
`h_{R'} ⇉ h_{H'}` through `h^* h_Z ≅ h_{T ×_S Z}`. -/
def smallEtaleInverseImagePairCokernelCofork :
    Cofork ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₁))
      ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₂)) :=
  Cofork.ofπ
    (((smallEtaleInverseImageRepresentableSheafIso.{w} B h).app H).inv ≫
      (smallEtaleInverseImage B h (Type (max (u + 1) w))).map
        (Sheaf.pairCokernelπ ((smallEtaleRepresentableSheafULift.{w} B S).map r₁)
          ((smallEtaleRepresentableSheafULift.{w} B S).map r₂))) (by
    rw [← Category.assoc, smallEtaleRepresentableSheafULift_map_baseChange_comp_inv,
      ← Category.assoc, smallEtaleRepresentableSheafULift_map_baseChange_comp_inv,
      Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Sheaf.pairCokernelπ_condition])

lemma smallEtaleInverseImagePairCokernelCofork_π :
    (smallEtaleInverseImagePairCokernelCofork.{w} B h r₁ r₂).π =
      ((smallEtaleInverseImageRepresentableSheafIso.{w} B h).app H).inv ≫
        (smallEtaleInverseImage B h (Type (max (u + 1) w))).map
          (Sheaf.pairCokernelπ ((smallEtaleRepresentableSheafULift.{w} B S).map r₁)
            ((smallEtaleRepresentableSheafULift.{w} B S).map r₂)) :=
  rfl

/-- The cofork `smallEtaleInverseImagePairCokernelCofork` is a coequalizer: `h^*` is a left
adjoint, so it preserves the coequalizer `h_H ⟶ Coker(h_R ⇉ h_H)`. -/
def isColimitSmallEtaleInverseImagePairCokernelCofork :
    IsColimit (smallEtaleInverseImagePairCokernelCofork.{w} B h r₁ r₂) := by
  let L := smallEtaleInverseImage B h (Type (max (u + 1) w))
  let e := smallEtaleInverseImageRepresentableSheafIso.{w} B h
  haveI : PreservesColimitsOfSize.{0, 0} L :=
    (smallEtaleInverseImageAdjunction B h (Type (max (u + 1) w))).leftAdjoint_preservesColimits
  have hL : IsColimit (L.mapCocone (Sheaf.pairCokernelCofork
      ((smallEtaleRepresentableSheafULift.{w} B S).map r₁)
      ((smallEtaleRepresentableSheafULift.{w} B S).map r₂))) :=
    isColimitOfPreserves L (Sheaf.isColimitPairCokernelCofork
      ((smallEtaleRepresentableSheafULift.{w} B S).map r₁)
      ((smallEtaleRepresentableSheafULift.{w} B S).map r₂))
  refine Cofork.isColimitOfIsos _ ((isColimitMapCoconeCoforkEquiv L _).1 hL) _
    (e.app R) (e.app H) (Iso.refl _) ?_ ?_ ?_
  · exact (e.hom.naturality r₁).symm
  · exact (e.hom.naturality r₂).symm
  · simp only [Iso.refl_hom, Cofork.π_ofπ, smallEtaleInverseImagePairCokernelCofork_π]
    exact congrArg ((e.app H).inv ≫ ·) (Category.comp_id _)

/-- **The inverse image of the cokernel of a pair of representable sheaves.** For a morphism
`h : T ⟶ S` and morphisms `r₁ r₂ : R ⟶ H` of étale `S`-schemes, with base changes
`r'ᵢ : T ×_S R ⟶ T ×_S H`, there is an isomorphism
`h^* Coker(h_R ⇉ h_H) ≅ Coker(h_{R'} ⇉ h_{H'})`; it is compatible with the projections from
`h^* h_H ≅ h_{H'}` (`smallEtaleInverseImage_map_pairCokernelπ_comp_pairCokernelIso_hom`). -/
@[weil "lem_fk104_inverse_image_cokernel_of_representable_pair"]
def smallEtaleInverseImagePairCokernelIso :
    (smallEtaleInverseImage B h (Type (max (u + 1) w))).obj
        (Sheaf.pairCokernel ((smallEtaleRepresentableSheafULift.{w} B S).map r₁)
          ((smallEtaleRepresentableSheafULift.{w} B S).map r₂)) ≅
      Sheaf.pairCokernel
        ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₁))
        ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₂)) :=
  (isColimitSmallEtaleInverseImagePairCokernelCofork.{w} B h r₁ r₂).coconePointUniqueUpToIso
    (Sheaf.isColimitPairCokernelCofork
      ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₁))
      ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₂)))

/-- **Compatibility with the projections.** Under `h^* h_H ≅ h_{H'}`, the isomorphism
`smallEtaleInverseImagePairCokernelIso` carries `h^*` of the projection
`h_H ⟶ Coker(h_R ⇉ h_H)` to the projection `h_{H'} ⟶ Coker(h_{R'} ⇉ h_{H'})`. -/
@[weil "lem_fk104_inverse_image_cokernel_of_representable_pair", reassoc]
theorem smallEtaleInverseImage_map_pairCokernelπ_comp_pairCokernelIso_hom :
    (smallEtaleInverseImage B h (Type (max (u + 1) w))).map
        (Sheaf.pairCokernelπ ((smallEtaleRepresentableSheafULift.{w} B S).map r₁)
          ((smallEtaleRepresentableSheafULift.{w} B S).map r₂)) ≫
        (smallEtaleInverseImagePairCokernelIso.{w} B h r₁ r₂).hom =
      ((smallEtaleInverseImageRepresentableSheafIso.{w} B h).app H).hom ≫
        Sheaf.pairCokernelπ
          ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₁))
          ((smallEtaleRepresentableSheafULift.{w} B T).map
            ((smallEtaleBaseChange B h).map r₂)) := by
  have hc : (smallEtaleInverseImagePairCokernelCofork.{w} B h r₁ r₂).π ≫
      (smallEtaleInverseImagePairCokernelIso.{w} B h r₁ r₂).hom =
        Sheaf.pairCokernelπ
          ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₁))
          ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₂)) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitSmallEtaleInverseImagePairCokernelCofork.{w} B h r₁ r₂)
      (Sheaf.isColimitPairCokernelCofork
        ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₁))
        ((smallEtaleRepresentableSheafULift.{w} B T).map ((smallEtaleBaseChange B h).map r₂)))
      WalkingParallelPair.one
  rw [smallEtaleInverseImagePairCokernelCofork_π] at hc
  rw [← Iso.inv_comp_eq]
  exact (Category.assoc _ _ _).symm.trans hc

end AlgebraicGeometry

end
