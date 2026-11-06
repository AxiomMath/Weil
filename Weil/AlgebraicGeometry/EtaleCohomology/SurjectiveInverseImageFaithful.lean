module

public import Weil.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk
public import Weil.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import Weil.CategoryTheory.Sites.Pullback
public import Weil.Attr

/-!
# The unit of the inverse image along a surjective morphism is injective

Let `f : T ⟶ S` be a surjective morphism of schemes of a big étale site `B`, and let `G` be a
sheaf of abelian groups on the small étale site of `S`. Then the unit `G ⟶ f_* f^* G` of the
adjunction `f^* ⊣ f_*` is a monomorphism: it is injective on the sections over every étale
`S`-scheme.

The proof is stalkwise. For a geometric point `x` of `T` with image `y = f ∘ x`, the stalk of
`f^* G` at `x` is the stalk of `G` at `y`, and composing the stalk at `y` of the unit with this
identification and with the stalk at `x` of the counit at `f^* G` gives back the identification,
by the triangle identity of the adjunction; so the stalk of the unit at `y` is injective. Since
`f` is surjective, every point of `S` is the image of a point of `T`, so every geometric point of
`S` has the same underlying point as the image of a geometric point of `T`; stalk functors at
geometric points over the same point are isomorphic, so the stalk of the unit is injective at
every geometric point of `S`. Stalks at all geometric points are jointly faithful, hence the
unit is a monomorphism.

## Main results

* `AlgebraicGeometry.injective_sheafFiber_map_smallEtaleInverseImageUnit_app` — the stalk of
  the unit at the image of a geometric point of `T` is injective.
* `AlgebraicGeometry.mono_smallEtaleInverseImageUnit_app_of_surjective` — for surjective `f`
  the unit `G ⟶ f_* f^* G` is a monomorphism of abelian sheaves.
* `AlgebraicGeometry.injective_smallEtaleInverseImageUnit_app_hom_app_of_surjective` — for
  surjective `f` the unit is injective on the sections over every étale `S`-scheme.

## Implementation notes

The source assumes `f` finite and surjective and computes the stalk of `f_* f^* G` at a
geometric point as a product over the points of the geometric fibre; only surjectivity is
needed, since the stalk of the unit is already split injective at every geometric point lying
over the image of `f`. The small étale site is the one of the Stacks project, with geometric
points over algebraically closed fields.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The stalk of the unit `G ⟶ f_* f^* G` at the image `f ∘ x` of a geometric point `x` of `T`
is injective: it is split by the identification `(f^* G)_x ≅ G_{f ∘ x}` composed with the stalk
of the counit. -/
theorem injective_sheafFiber_map_smallEtaleInverseImageUnit_app (x : GeometricPoint T.obj)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}) :
    Function.Injective
      ((geometricPointSitePoint B S.obj S.property (x.map (B.inclusion.map f))).sheafFiber.map
        ((smallEtaleInverseImageUnit B f AddCommGrpCat.{max (u + 1) v}).app G)) := by
  set A := AddCommGrpCat.{max (u + 1) v}
  set adj := smallEtaleInverseImageAdjunction B f A
  set e := smallEtaleInverseImageSheafFiberIso B f x A
  have htri : (geometricPointSitePoint B T.obj T.property x).sheafFiber.map
        ((smallEtaleInverseImage B f A).map (adj.unit.app G)) ≫
      (geometricPointSitePoint B T.obj T.property x).sheafFiber.map
        (adj.counit.app ((smallEtaleInverseImage B f A).obj G)) = 𝟙 _ := by
    rw [← Functor.map_comp, adj.left_triangle_components G]
    exact CategoryTheory.Functor.map_id _ _
  have hfac : (geometricPointSitePoint B S.obj S.property
        (x.map (B.inclusion.map f))).sheafFiber.map (adj.unit.app G) ≫
      (e.hom.app _ ≫ (geometricPointSitePoint B T.obj T.property x).sheafFiber.map
        (adj.counit.app ((smallEtaleInverseImage B f A).obj G))) = e.hom.app G := by
    rw [← Category.assoc, e.hom.naturality (adj.unit.app G), Category.assoc]
    erw [htri]
    exact Category.comp_id _
  have : Mono ((geometricPointSitePoint B S.obj S.property
      (x.map (B.inclusion.map f))).sheafFiber.map (adj.unit.app G)) := mono_of_mono_fac hfac
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- For a surjective morphism `f`, the stalk of the unit `G ⟶ f_* f^* G` at every geometric point
of `S` is injective. -/
theorem injective_sheafFiber_map_smallEtaleInverseImageUnit_app_of_surjective
    [Surjective (B.inclusion.map f)] (s : GeometricPoint S.obj)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}) :
    Function.Injective
      ((geometricPointSitePoint B S.obj S.property s).sheafFiber.map
        ((smallEtaleInverseImageUnit B f AddCommGrpCat.{max (u + 1) v}).app G)) := by
  set A := AddCommGrpCat.{max (u + 1) v}
  obtain ⟨t, ht⟩ := (B.inclusion.map f).surjective (s.hom default)
  set x := GeometricPoint.ofPoint T.obj t
  have hx : (x.map (B.inclusion.map f)).hom default = s.hom default := by
    change (x.hom ≫ B.inclusion.map f) default = _
    rw [Scheme.Hom.comp_apply, GeometricPoint.ofPoint_liesOver T.obj t, ht]
  set φ := presheafFiberIsoOfEqBase B S.obj S.property hx A
  set η := (smallEtaleInverseImageUnit B f A).app G
  have hfac : (geometricPointSitePoint B S.obj S.property s).sheafFiber.map η =
      φ.inv.app _ ≫ (geometricPointSitePoint B S.obj S.property
        (x.map (B.inclusion.map f))).sheafFiber.map η ≫ φ.hom.app _ := by
    change (geometricPointSitePoint B S.obj S.property s).presheafFiber.map η.hom = _
    erw [φ.hom.naturality η.hom, Iso.inv_hom_id_app_assoc]
  have : Mono ((geometricPointSitePoint B S.obj S.property
      (x.map (B.inclusion.map f))).sheafFiber.map η) :=
    (AddCommGrpCat.mono_iff_injective _).2
      (injective_sheafFiber_map_smallEtaleInverseImageUnit_app B f x G)
  rw [← AddCommGrpCat.mono_iff_injective, hfac]
  have h₁ : Mono (φ.app ((sheafToPresheaf _ A).obj G)).inv := inferInstance
  have h₂ : Mono (φ.app ((sheafToPresheaf _ A).obj
    ((smallEtaleInverseImage B f A ⋙ B.smallPushforward f A).obj G))).hom := inferInstance
  exact @mono_comp _ _ _ _ _ _ h₁ _ (@mono_comp _ _ _ _ _ _ this _ h₂)

/-- **The unit of the inverse image along a surjective morphism is a monomorphism.** For a
surjective morphism `f : T ⟶ S` and a sheaf of abelian groups `G` on the small étale site of `S`,
the unit `G ⟶ f_* f^* G` of the adjunction `f^* ⊣ f_*` is a monomorphism. -/
@[weil "lem_fk104_finite_surjective_adjunction_injective"]
theorem mono_smallEtaleInverseImageUnit_app_of_surjective [Surjective (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}) :
    Mono ((smallEtaleInverseImageUnit B f AddCommGrpCat.{max (u + 1) v}).app G) := by
  set η := (smallEtaleInverseImageUnit B f AddCommGrpCat.{max (u + 1) v}).app G
  apply Preadditive.mono_of_cancel_zero
  intro K g hg
  apply (jointlyFaithful_etaleStalkSheafFiber.{u, v} B S.obj S.property).map_injective
  intro s
  have : Mono ((geometricPointSitePoint B S.obj S.property s).sheafFiber.map η) :=
    (AddCommGrpCat.mono_iff_injective _).2
      (injective_sheafFiber_map_smallEtaleInverseImageUnit_app_of_surjective B f s G)
  rw [Functor.map_zero,
    ← cancel_mono ((geometricPointSitePoint B S.obj S.property s).sheafFiber.map η),
    ← Functor.map_comp, hg, Functor.map_zero, zero_comp]

/-- **The unit of the inverse image along a surjective morphism is injective on sections.** For
a surjective morphism `f : T ⟶ S`, a sheaf of abelian groups `G` on the small étale site of `S`
and an étale `S`-scheme `U`, the unit `G(U) ⟶ (f^* G)(T ×_S U)` is injective. -/
@[weil "lem_fk104_finite_surjective_adjunction_injective"]
theorem injective_smallEtaleInverseImageUnit_app_hom_app_of_surjective
    [Surjective (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
    (U : (SmallEtale B S.obj S.property)ᵒᵖ) :
    Function.Injective
      (((smallEtaleInverseImageUnit B f AddCommGrpCat.{max (u + 1) v}).app G).hom.app U) := by
  have := mono_smallEtaleInverseImageUnit_app_of_surjective B f G
  rw [← AddCommGrpCat.mono_iff_injective]
  infer_instance

end AlgebraicGeometry
