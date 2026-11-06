module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import Weil.Attr

/-!
# The base change map of abelian étale sheaves, in degree zero

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. For an abelian sheaf `F` on the small étale site of `X`, the
*base change map* `β_F : g^* f_* F ⟶ f'_* g'^* F` is the morphism of sheaves on `Y'` which
corresponds, under the adjunction `g^* ⊣ g_*`, to the composite
`f_* F ⟶ f_* g'_* g'^* F ≅ g_* f'_* g'^* F` of `f_*` of the unit of `g'^* ⊣ g'_*` with the
identification `c` of the two composite direct images around the square. Equivalently, `β_F` is
the unique morphism with `g_*(β_F) ∘ η^g_{f_* F} = c ∘ f_*(η^{g'}_F)`.

The map is `Stacks.EtaleCohomology.etaleAbelianBaseChange`, a natural transformation
`f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`. This file proves that it is the map just described: it satisfies the
unit identity (`Stacks.EtaleCohomology.etaleAbelianBaseChange_unit`), and is the only morphism
that does (`Stacks.EtaleCohomology.eq_etaleAbelianBaseChange_app_iff`). Applied degreewise to a
cochain complex it gives the morphism of complexes
`Stacks.EtaleCohomology.etaleAbelianComplexBaseChange`.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDirectImageSquareIso` — the identification
  `c : g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images around the square.
* `Stacks.EtaleCohomology.etaleAbelianComplexBaseChange` — the base change map applied degreewise
  to cochain complexes, `g^* f_* K ⟶ f'_* g'^* K`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianBaseChange_unit` — the unit identity
  `η^g_{f_* F} ≫ g_*(β_F) = f_*(η^{g'}_F) ≫ c_{g'^* F}`.
* `Stacks.EtaleCohomology.eq_etaleAbelianBaseChange_app_iff` — `β_F` is the unique morphism
  satisfying the unit identity.

## Implementation notes

Sheaves are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology`, with coefficients
`AddCommGrpCat.{max (u + 1) v}`, the setting of `Stacks.EtaleCohomology.etaleAbelianBaseChange`.
That map is built as the mate of the comparison of composite inverse images along the vertical
adjunctions; the unit identity is its description as the mate of `c` along the horizontal
adjunctions (`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`),
read at a component (`CategoryTheory.unit_mateEquiv_symm`). The square need not be cartesian.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

/- As in `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange`, the preadditive structure on
abelian sheaves is taken from the abelian structure, so that the statements here carry the same
instance as their consumers in the base change development. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The identification `c : g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images of
abelian étale sheaves around a commutative square `g' ≫ f = f' ≫ g`. -/
def etaleAbelianDirectImageSquareIso :
    etaleAbelianDirectImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f ≅
      etaleAbelianDirectImage.{u, v} f' ⋙ etaleAbelianDirectImage.{u, v} g :=
  etaleAbelianDirectImageCompIso'.{u, v} g' f (g' ≫ f) rfl ≪≫
    (etaleAbelianDirectImageCompIso'.{u, v} f' g (g' ≫ f) h).symm

/-- **The unit identity of the base change map.** For an abelian sheaf `F` on the small étale site
of `X`, the base change map `β_F : g^* f_* F ⟶ f'_* g'^* F` satisfies
`g_*(β_F) ∘ η^g_{f_* F} = c ∘ f_*(η^{g'}_F)`, where `η` are the units of the inverse-image /
direct-image adjunctions and `c` is `etaleAbelianDirectImageSquareIso`. -/
@[weil "def_fk106_base_change_map_degree_zero", reassoc]
theorem etaleAbelianBaseChange_unit (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
        ((etaleAbelianDirectImage.{u, v} f).obj F) ≫
      (etaleAbelianDirectImage.{u, v} g).map ((etaleAbelianBaseChange.{u, v} f g g' f' h).app F) =
    (etaleAbelianDirectImage.{u, v} f).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} g').unit.app F) ≫
      (etaleAbelianDirectImageSquareIso.{u, v} f g g' f' h).hom.app
        ((etaleAbelianInverseImage.{u, v} g').obj F) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v} f g g' f' h
    (g' ≫ f) rfl h]
  exact (unit_mateEquiv_symm (etaleAbelianInverseImageDirectImageAdj.{u, v} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g) _ F).symm

/-- **The base change map is the unique morphism satisfying the unit identity.** A morphism
`φ : g^* f_* F ⟶ f'_* g'^* F` is the base change map `β_F` if and only if
`g_*(φ) ∘ η^g_{f_* F} = c ∘ f_*(η^{g'}_F)`. -/
@[weil "def_fk106_base_change_map_degree_zero"]
theorem eq_etaleAbelianBaseChange_app_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (φ : (etaleAbelianInverseImage.{u, v} g).obj ((etaleAbelianDirectImage.{u, v} f).obj F) ⟶
      (etaleAbelianDirectImage.{u, v} f').obj ((etaleAbelianInverseImage.{u, v} g').obj F)) :
    φ = (etaleAbelianBaseChange.{u, v} f g g' f' h).app F ↔
      (etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
          ((etaleAbelianDirectImage.{u, v} f).obj F) ≫ (etaleAbelianDirectImage.{u, v} g).map φ =
        (etaleAbelianDirectImage.{u, v} f).map
            ((etaleAbelianInverseImageDirectImageAdj.{u, v} g').unit.app F) ≫
          (etaleAbelianDirectImageSquareIso.{u, v} f g g' f' h).hom.app
            ((etaleAbelianInverseImage.{u, v} g').obj F) := by
  rw [← etaleAbelianBaseChange_unit.{u, v} f g g' f' h F]
  have := ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _).injective.eq_iff
    (a := φ) (b := (etaleAbelianBaseChange.{u, v} f g g' f' h).app F)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at this
  exact this.symm

/-- **The base change map on complexes.** For a cochain complex `K` of abelian sheaves on the small
étale site of `X`, the morphism of complexes `g^* f_* K ⟶ f'_* g'^* K` given in degree `n` by the
base change map `β_{K^n}` (`etaleAbelianComplexBaseChange_app_f`); it is natural in `K`. -/
@[weil "def_fk106_base_change_map_degree_zero"]
def etaleAbelianComplexBaseChange :
    (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (etaleAbelianInverseImage.{u, v} g' ⋙
        etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h) (ComplexShape.up ℤ)

/-- The base change map on complexes is the base change map applied degreewise. -/
theorem etaleAbelianComplexBaseChange_eq :
    etaleAbelianComplexBaseChange.{u, v} f g g' f' h =
      NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
        (ComplexShape.up ℤ) :=
  rfl

/- the complex below is stated over
`HomologicalComplex _ (ComplexShape.up ℤ)` rather than `CochainComplex _ ℤ`: the two spell the
additive structure of `ℤ` differently, and the kernel then unfolds the sheaf functors to compare
them (deterministic timeout). Likewise the proof goes through `etaleAbelianComplexBaseChange_eq`
and not `rfl`, which makes the kernel unfold `etaleAbelianBaseChange`. -/
/-- The component in degree `n` of the base change map on a complex `K` is `β_{K^n}`. -/
@[simp]
theorem etaleAbelianComplexBaseChange_app_f
    (K : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)) (n : ℤ) :
    ((etaleAbelianComplexBaseChange.{u, v} f g g' f' h).app K).f n =
      (etaleAbelianBaseChange.{u, v} f g g' f' h).app (K.X n) := by
  rw [etaleAbelianComplexBaseChange_eq]
  exact NatTrans.mapHomologicalComplex_app_f _ _ _ _

end Stacks.EtaleCohomology

end
