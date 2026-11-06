module

public import Weil.Defs.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import Weil.Attr

/-!
# The direct image of presheaves along a composite

Let `B` be a big étale site, `f : X ⟶ Y` and `g : Y ⟶ Z` morphisms of it. For a presheaf `F`
on the small étale category of `X` (with values in any category `A`) there is an isomorphism
`(g ∘ f)_* F ≅ g_* (f_* F)`, natural in `F`. At an étale `Z`-scheme `W` it is the restriction
of `F` along the canonical isomorphism of étale `X`-schemes
`(W ×_Z Y) ×_Y X ≅ W ×_Z X`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.presheafDirectImageComp`: the natural isomorphism
  `(f ≫ g)_* ≅ f_* ⋙ g_*` of direct image functors on presheaves.
* `AlgebraicGeometry.BigEtaleSite.presheafDirectImageComp_hom_app_app`: its component at `F`
  and `W` is the restriction of `F` along the comparison of iterated and composite base
  changes.

## Implementation notes

Since `f_*` is precomposition with the base change functor `smallEtaleBaseChange B f`, the
isomorphism is obtained by whiskering the opposite of the comparison
`AlgebraicGeometry.smallEtaleBaseChange_compIso` of iterated and composite base changes.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2]
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (A : Type w) [Category.{v} A]

/-- **The direct image along a composite is the composite of the direct images**: for
morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` there is an isomorphism `(g ∘ f)_* F ≅ g_* (f_* F)`,
natural in the presheaf `F` on the small étale category of `X`. -/
@[weil "lem_fk102_direct_image_comp"]
def presheafDirectImageComp :
    presheafDirectImage B (f ≫ g) A ≅ presheafDirectImage B f A ⋙ presheafDirectImage B g A :=
  (Functor.whiskeringLeft _ _ A).mapIso (NatIso.op (smallEtaleBaseChange_compIso B X Y Z f g).val)

/-- The component of `presheafDirectImageComp` at a presheaf `F` and an étale `Z`-scheme `W`
is the restriction of `F` along the comparison `(W ×_Z Y) ×_Y X ⟶ W ×_Z X` of iterated and
composite base changes. -/
@[simp]
theorem presheafDirectImageComp_hom_app_app (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (W : (SmallEtale B Z.obj Z.property)ᵒᵖ) :
    ((presheafDirectImageComp B f g A).hom.app F).app W =
      F.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W.unop).op :=
  rfl

@[simp]
theorem presheafDirectImageComp_inv_app_app (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A)
    (W : (SmallEtale B Z.obj Z.property)ᵒᵖ) :
    ((presheafDirectImageComp B f g A).inv.app F).app W =
      F.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app W.unop).op :=
  rfl

end AlgebraicGeometry.BigEtaleSite
