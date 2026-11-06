module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers
public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# Morphisms of represented sheaves are determined at one stalk

Let `X` be a connected scheme, `s` a geometric point of `X` and `Y`, `Y'` covering spaces
(finite étale schemes) of `X`. Two morphisms `α, β : Ỹ ⟶ Ỹ'` of the sheaves on the small étale
site of `X` represented by `Y` and `Y'` coincide as soon as their stalks `α_s, β_s` at `s`
coincide.

Indeed, `α` and `β` are induced by `X`-morphisms `v, w : Y ⟶ Y'`, the small étale topology
being subcanonical. The bijection `ε_Y : Ỹ_s ≃ Y(s)` between the stalk and the geometric fibre
is natural, so `α_s = β_s` gives `v(s) = w(s)` on the geometric fibre `Y(s)`. The geometric
fibre functor on the category of finite étale covers of the connected scheme `X` is the fibre
functor of a Galois category, hence faithful, so `v = w`.

## Main results

* `AlgebraicGeometry.SmallEtale.eq_of_etaleStalkFunctor_map_eq_of_isFinite`: the statement for
  objects of the small étale site with finite structure morphism.
* `AlgebraicGeometry.Scheme.CoveringSpace.eq_of_etaleStalkFunctor_map_eq`: the statement for
  covering spaces of `X`.

## Implementation notes

Geometric points take values in algebraically closed fields and the étale site is
`AlgebraicGeometry.SmallEtale`, following the Stacks project. The faithfulness of the geometric
fibre functor is used directly, in place of the equivalence of the category of covering spaces
with the category of finite continuous `π₁(X, s)`-sets of which it is a consequence.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 0BN0](https://stacks.math.columbia.edu/tag/0BN0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Morphisms of represented sheaves are determined at a stalk.** Let `X` be connected and
`Y`, `Y'` objects of the small étale site of `X` with finite structure morphisms. Two morphisms
`α, β : Ỹ ⟶ Ỹ'` of the represented sheaves whose stalks at a geometric point `s` coincide are
equal. -/
theorem eq_of_etaleStalkFunctor_map_eq_of_isFinite [ConnectedSpace X] (s : GeometricPoint X)
    {Y Y' : SmallEtale B X hX} [hY : IsFinite (B.inclusion.map Y.obj.hom)]
    [hY' : IsFinite (B.inclusion.map Y'.obj.hom)]
    (α β : representedSheaf Y ⟶ representedSheaf Y')
    (h : (etaleStalkFunctor.{u, u} B X hX s).map α = (etaleStalkFunctor.{u, u} B X hX s).map β) :
    α = β := by
  obtain ⟨v, rfl⟩ := (smallEtaleYoneda B X hX).map_surjective α
  obtain ⟨w, rfl⟩ := (smallEtaleYoneda B X hX).map_surjective β
  congr 1
  -- `v` and `w` agree on the geometric fibre at `s`.
  have hfib : (geometricPointFiber B X hX s).map v = (geometricPointFiber B X hX s).map w := by
    have hv := GeometricPoint.stalkToFiberMap_naturality s v
    have hw := GeometricPoint.stalkToFiberMap_naturality s w
    rw [h, hw] at hv
    exact (cancel_epi _).mp hv.symm
  -- Pass to the category of finite étale covers, where the fibre functor is faithful.
  let X' : B.Scheme := ⟨X, hX⟩
  let F := finiteEtaleFromSmallEtale B X'
  have : F.Faithful := (finiteEtaleFromSmallEtaleFullyFaithful B X').faithful
  let Z : (finiteSmallEtaleObjects B X').FullSubcategory := ⟨Y, hY⟩
  let Z' : (finiteSmallEtaleObjects B X').FullSubcategory := ⟨Y', hY'⟩
  let v' : Z ⟶ Z' := ObjectProperty.homMk v
  let w' : Z ⟶ Z' := ObjectProperty.homMk w
  suffices hvw : v' = w' from congrArg (fun f ↦ f.hom) hvw
  apply F.map_injective
  apply (finiteEtaleFiberFunctor s).map_injective
  ext y
  apply Subtype.ext
  exact congrArg Subtype.val (ConcreteCategory.congr_hom hfib
    (⟨y.1, y.2⟩ : (geometricPointFiber B X hX s).obj Y))

end SmallEtale

namespace Scheme.CoveringSpace

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A covering space of `X`, read as an object of the small étale site of `X`. -/
noncomputable abbrev toSmallEtale (hX : B.Contains X) (Y : X.CoveringSpace) :
    SmallEtale B X hX :=
  smallEtaleOfFiniteEtale (B := B) (X := ⟨X, hX⟩) Y

instance isFinite_toSmallEtale_hom (Y : X.CoveringSpace) :
    IsFinite (B.inclusion.map (toSmallEtale hX Y).obj.hom) := by
  rw [toSmallEtale, smallEtaleOfFiniteEtale_hom]
  exact Y.prop.1

/-- **Morphisms of represented sheaves are determined at a stalk.** Let `X` be connected and
`Y`, `Y'` covering spaces of `X`. Two morphisms `α, β : Ỹ ⟶ Ỹ'` of the sheaves on the small
étale site of `X` represented by `Y` and `Y'` whose stalks `α_s, β_s` at a geometric point `s`
coincide are equal. -/
@[weil "lem_fka1_represented_morphisms_determined_at_stalk"]
theorem eq_of_etaleStalkFunctor_map_eq [ConnectedSpace X] (s : GeometricPoint X)
    {Y Y' : X.CoveringSpace}
    (α β : SmallEtale.representedSheaf (toSmallEtale hX Y) ⟶
      SmallEtale.representedSheaf (toSmallEtale hX Y'))
    (h : (etaleStalkFunctor.{u, u} B X hX s).map α = (etaleStalkFunctor.{u, u} B X hX s).map β) :
    α = β :=
  SmallEtale.eq_of_etaleStalkFunctor_map_eq_of_isFinite s α β h

end Scheme.CoveringSpace

end AlgebraicGeometry

end
