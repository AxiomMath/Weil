module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkModule

/-!
# The map from the stalk of a direct image to the stalk at a point of the fibre

Let `f : X ⟶ Y` be a morphism in a big étale site, `x` a geometric point of `X` and `y` the
geometric point `f ∘ x` of `Y`, and let `G` be a presheaf of sets on the small étale site of
`X`. For an étale neighbourhood `(V, v)` of `y`, the base change `V ×_Y X` is an étale
neighbourhood of `x`, pointed by `(v, x)`. The germ maps
`(f_* G)(V) = G(V ×_Y X) ⟶ G_x` at these neighbourhoods are compatible with restriction, so they
induce a map on the colimit

  `ε_x : (f_* G)_y = colim_{(V, v)} (f_* G)(V) ⟶ G_x`.

For a sheaf `G` this is the map induced by the counit of `f^* ⊣ f_*` and the identification
of the stalk of an inverse image (Tag 03Q1), which is
`AlgebraicGeometry.pushforwardEtaleStalkComponent`.

## Main definitions

* `AlgebraicGeometry.directImageStalkToFibreStalk`: the map `ε_x : (f_* G)_y ⟶ G_x`, for a
  presheaf `G` of sets in any universe and a geometric point `x` of `X` over `y`.

## Main results

* `AlgebraicGeometry.directImageStalkToFibreStalk_germ_lifted`: on germs, `ε_x` sends the germ
  of `s ∈ G(V ×_Y X)` at `(V, v)` to the germ of `s` at `(V ×_Y X, (v, x))`.
* `AlgebraicGeometry.directImageStalkToFibreStalk_germ`: the same, computed at any pointed
  étale neighbourhood of `x` mapping to `V ×_Y X`.
* `AlgebraicGeometry.directImageStalkToFibreStalk_natural`: naturality in the presheaf.
* `AlgebraicGeometry.directImageStalkToFibreStalk_eq_pushforwardEtaleStalkComponent` and
  `AlgebraicGeometry.directImageStalkToFibreStalk_eq_pushforwardEtaleStalkComponentUniv`: for a
  sheaf, `ε_x` is the counit-induced map.

## Implementation notes

Geometric points are spectra of algebraically closed fields. The direct image of a presheaf is
the composite with the base change functor `smallEtaleBaseChange`; for a sheaf it is,
definitionally, the underlying presheaf of the direct image sheaf.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FK]
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The germ maps `G(V ×_Y X) ⟶ G_x` at the lifted neighbourhoods `(V ×_Y X, (v, x))`, as a
cocone over the neighbourhood diagram of the direct image at `f ∘ x`. -/
def directImageStalkToFibreStalkCocone (x : GeometricPoint X.1)
    (G : (SmallEtale B X.1 X.property)ᵒᵖ ⥤ Type w) [HasColimitsOfSize.{u, u} (Type w)] :
    Cocone ((CategoryOfElements.π
      (geometricPointFiber B Y.1 Y.property (x.map (B.inclusion.map f)))).op ⋙
        (smallEtaleBaseChange B f).op ⋙ G) where
  pt := etaleStalk B X.1 X.property x G
  ι :=
    { app := fun U => colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ G)
        (op (liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U.unop))
      naturality := fun U V g => by
        let m : liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ V.unop ⟶
            liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U.unop :=
          ⟨(smallEtaleBaseChange B f).map g.unop.1, liftedEtaleNeighborhood_map B f
            (x.map (B.inclusion.map f)) g.unop ⟨x.hom, rfl⟩⟩
        have := colimit.w
          ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ G) m.op
        exact this.trans (Category.comp_id _).symm }

/-- **The natural map `ε_x : (f_* G)_y ⟶ G_x`.** For a geometric point `x` of `X` with
`f ∘ x = y` and a presheaf of sets `G` on the small étale site of `X`, the map from the stalk at
`y` of the direct image `f_* G = G ∘ (- ×_Y X)` to the stalk of `G` at `x`, induced on the
colimit over the étale neighbourhoods `(V, v)` of `y` by the germ maps
`G(V ×_Y X) ⟶ G_x` at `(V ×_Y X, (v, x))`. -/
@[weil "def_fk103_direct_image_stalk_to_fibre_stalk_map"]
def directImageStalkToFibreStalk (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (G : (SmallEtale B X.1 X.property)ᵒᵖ ⥤ Type w) [HasColimitsOfSize.{u, u} (Type w)] :
    etaleStalk B Y.1 Y.property y ((smallEtaleBaseChange B f).op ⋙ G) →
      etaleStalk B X.1 X.property x G :=
  fun z => colimit.desc _ (directImageStalkToFibreStalkCocone B f x G) (h.symm ▸ z)

/-- On germs, `ε_x` sends the germ at `(V, v)` of `s ∈ G(V ×_Y X)` to the germ of `s` at the
lifted neighbourhood `(V ×_Y X, (v, x))`. -/
theorem directImageStalkToFibreStalk_germ_lifted (x : GeometricPoint X.1)
    (G : (SmallEtale B X.1 X.property)ᵒᵖ ⥤ Type w) [HasColimitsOfSize.{u, u} (Type w)]
    (U : (geometricPointFiber B Y.1 Y.property (x.map (B.inclusion.map f))).Elements)
    (s : G.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    directImageStalkToFibreStalk B f x _ rfl G
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property
          (x.map (B.inclusion.map f)))).op ⋙ (smallEtaleBaseChange B f).op ⋙ G) (op U) s) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ G)
        (op (liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U)) s :=
  ConcreteCategory.congr_hom (colimit.ι_desc (directImageStalkToFibreStalkCocone B f x G) (op U)) s

/-- **`ε_x` on germs.** The germ at `(U, u)` of a section `s` of `G` over `U ×_Y X` is sent to
the germ of the restriction of `s` to any étale neighbourhood `V` of `x` equipped with a map to
`U ×_Y X` compatible with the points. -/
theorem directImageStalkToFibreStalk_germ (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (G : (SmallEtale B X.1 X.property)ᵒᵖ ⥤ Type w) [HasColimitsOfSize.{u, u} (Type w)]
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property x).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (ht : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ U.2.1)
    (s : G.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    directImageStalkToFibreStalk B f x y h G
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (smallEtaleBaseChange B f).op ⋙ G) (op U) s) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ G)
        (op V) (G.map t.op s) := by
  subst h
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  simp only [eqToHom_refl, Category.id_comp] at ht
  rw [directImageStalkToFibreStalk_germ_lifted]
  let L := liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U
  have hpt : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t = L.2.1 := by
    apply ((IsPullback.of_hasPullback
      (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion).hom_ext
    · refine (Category.assoc _ _ _).trans (ht.trans ?_)
      exact (liftedEtaleNeighborhood_point_fst B f _ ⟨x.hom, rfl⟩ U).symm
    · have hV := V.2.2
      have hL := L.2.2
      have hc := SmallEtale.toScheme_map_comp B X.1 X.property t
      have e : ∀ {T : Scheme.{u}} (p : T ⟶ (SmallEtale.toScheme B X.1 X.property).obj
          ((smallEtaleBaseChange B f).obj U.1)), p ≫ B.inclusion.map
            (pullback.snd (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f) =
          p ≫ B.inclusion.map ((smallEtaleBaseChange B f).obj U.1).obj.hom := fun _ => rfl
      exact (e _).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc).trans
        (hV.trans (hL.symm.trans (e _).symm))))
  let m : V ⟶ L := ⟨t, Subtype.ext hpt⟩
  exact (ConcreteCategory.congr_hom (colimit.w
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ G) m.op) s).symm

/-- **Naturality of `ε_x` in the presheaf.** -/
theorem directImageStalkToFibreStalk_natural (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    {G H : (SmallEtale B X.1 X.property)ᵒᵖ ⥤ Type w} [HasColimitsOfSize.{u, u} (Type w)]
    (α : G ⟶ H) (z : etaleStalk B Y.1 Y.property y ((smallEtaleBaseChange B f).op ⋙ G)) :
    directImageStalkToFibreStalk B f x y h H
        (colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op
          (Functor.whiskerLeft (smallEtaleBaseChange B f).op α)) z) =
      colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op α)
        (directImageStalkToFibreStalk B f x y h G z) := by
  subst h
  obtain ⟨U, s, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) z
  have h1 := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property
            (x.map (B.inclusion.map f)))).op
          (Functor.whiskerLeft (smallEtaleBaseChange B f).op α)) U) s
  have h2 := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op α)
          (op (liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U.unop))) s
  dsimp only [types_comp_apply] at h1 h2
  erw [h1, directImageStalkToFibreStalk_germ_lifted, directImageStalkToFibreStalk_germ_lifted, h2]
  rfl

/-- **Bridge to the counit-induced map, for sheaves in any universe.** For a sheaf `F`, the map
`ε_x` on the underlying presheaf is `AlgebraicGeometry.pushforwardEtaleStalkComponentUniv`. -/
theorem directImageStalkToFibreStalk_eq_pushforwardEtaleStalkComponentUniv
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    directImageStalkToFibreStalk B f x y h F.obj =
      pushforwardEtaleStalkComponentUniv B f x y h F := by
  subst h
  funext z
  obtain ⟨U, s, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) z
  refine (directImageStalkToFibreStalk_germ_lifted B f x F.obj U.unop s).trans ?_
  refine (pushforwardEtaleStalkComponent_germ_univ B f x _ rfl F U.unop
    (liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U.unop) (𝟙 _)
    ?_ s).trans ?_ |>.symm
  · let := hasPullbacks_bigEtaleSite B
    let := preservesPullbacks_bigEtaleSiteInclusion B
    simp [liftedEtaleNeighborhood]
  · congr 1
    exact ConcreteCategory.congr_hom (F.obj.map_id _) s

/-- **Bridge to the counit-induced map.** For a sheaf `F` with values in `Type (u + 1)`, the map
`ε_x` on the underlying presheaf is `AlgebraicGeometry.pushforwardEtaleStalkComponent`. -/
theorem directImageStalkToFibreStalk_eq_pushforwardEtaleStalkComponent
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    directImageStalkToFibreStalk B f x y h F.obj =
      pushforwardEtaleStalkComponent B f x y h F := by
  subst h
  funext z
  obtain ⟨U, s, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) z
  refine (directImageStalkToFibreStalk_germ_lifted B f x F.obj U.unop s).trans ?_
  refine (pushforwardEtaleStalkComponent_germ B f x _ rfl F U.unop
    (liftedEtaleNeighborhood B f (x.map (B.inclusion.map f)) ⟨x.hom, rfl⟩ U.unop) (𝟙 _)
    ?_ s).trans ?_ |>.symm
  · let := hasPullbacks_bigEtaleSite B
    let := preservesPullbacks_bigEtaleSiteInclusion B
    simp [liftedEtaleNeighborhood]
  · congr 1
    exact ConcreteCategory.congr_hom (F.obj.map_id _) s

end AlgebraicGeometry

end
