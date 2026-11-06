module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import Weil.Attr

/-!
# The comparison of the stalk of a represented sheaf with the geometric fibre

Let `S` be a scheme, `s` a geometric point of `S`, `G` a sheaf of sets on the small étale site
of `S`, `Y` an object of the small étale site and `h : Ỹ ≅ G` an isomorphism from the sheaf
represented by `Y` to `G`. The *comparison map*
`c_h = ε_Y ∘ (h⁻¹)_s : G_s ⟶ Y(s)`
is the composite of the map induced by `h⁻¹` on stalks at `s` with the map
`ε_Y : Ỹ_s ⟶ Y(s)` from the stalk of `Ỹ` to the set of lifts of `s` to `Y`
(`AlgebraicGeometry.GeometricPoint.stalkToFiberMap`). It is bijective, and it sends the germ at
a pointed étale neighbourhood `(U, u)` of a section `g ∈ G(U)` to `u ≫ h⁻¹(g)`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.stalkFiberComparison`: the map `c_h : G_s ⟶ Y(s)`.
* `AlgebraicGeometry.GeometricPoint.stalkFiberComparisonIso`: `c_h` as an isomorphism.

## Main results

* `AlgebraicGeometry.GeometricPoint.stalkFiberComparison_etaleStalkGerm`: `c_h` on germs.
* `AlgebraicGeometry.GeometricPoint.bijective_stalkFiberComparison`: `c_h` is bijective.
* `AlgebraicGeometry.GeometricPoint.etaleStalkFunctor_map_comp_stalkFiberComparison`: `c_h` is
  natural in `G`: for `φ : G ≅ G'`, `c_{h ≪≫ φ} ∘ φ_s = c_h`.
* `AlgebraicGeometry.GeometricPoint.stalkFiberComparison_comp_geometricPointFiber_map`: `c_h` is
  natural in `Y`: for `v : Y ≅ Y'`, `v ∘ c_h = c_{ṽ⁻¹ ≪≫ h}`.

## Implementation notes

Geometric points take values in algebraically closed fields, and the étale site is the small
étale site `AlgebraicGeometry.SmallEtale` of a big étale site, following the Stacks project.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

/- StacksFrontier's
`AlgebraicGeometry.finiteLocallyConstantStalkIso` is a related but different object (finite
locally constant sheaves in `Type (u + 1)`, through a chosen representing cover); FK's `c_h`
depends on the given `h`, so it is defined here directly from `stalkToFiberMap`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GeometricPoint

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : GeometricPoint S)

/-- **The comparison map `c_h = ε_Y ∘ (h⁻¹)_s : G_s ⟶ Y(s)`** attached to an isomorphism
`h : Ỹ ≅ G` from the sheaf represented by `Y` to a sheaf of sets `G`: the map induced by `h⁻¹`
on stalks at `s`, followed by `ε_Y = stalkToFiberMap s Y`. -/
@[weil "def_fka1_stalk_fiber_comparison"]
def stalkFiberComparison {G : smallEtaleTopos.{u, u} B S hS} {Y : SmallEtale B S hS}
    (h : SmallEtale.representedSheaf Y ≅ G) :
    (etaleStalkFunctor.{u, u} B S hS s).obj G ⟶ (geometricPointFiber B S hS s).obj Y :=
  (etaleStalkFunctor.{u, u} B S hS s).map h.inv ≫ stalkToFiberMap s Y

variable {s}

theorem stalkFiberComparison_def {G : smallEtaleTopos.{u, u} B S hS} {Y : SmallEtale B S hS}
    (h : SmallEtale.representedSheaf Y ≅ G) :
    stalkFiberComparison s h =
      (etaleStalkFunctor.{u, u} B S hS s).map h.inv ≫ stalkToFiberMap s Y :=
  rfl

instance isIso_stalkFiberComparison {G : smallEtaleTopos.{u, u} B S hS}
    {Y : SmallEtale B S hS} (h : SmallEtale.representedSheaf Y ≅ G) :
    IsIso (stalkFiberComparison s h) := by
  rw [stalkFiberComparison_def]
  infer_instance

variable (s) in
/-- The comparison map `c_h : G_s ⟶ Y(s)` as an isomorphism. -/
def stalkFiberComparisonIso {G : smallEtaleTopos.{u, u} B S hS} {Y : SmallEtale B S hS}
    (h : SmallEtale.representedSheaf Y ≅ G) :
    (etaleStalkFunctor.{u, u} B S hS s).obj G ≅ (geometricPointFiber B S hS s).obj Y :=
  asIso (stalkFiberComparison s h)

@[simp]
theorem stalkFiberComparisonIso_hom {G : smallEtaleTopos.{u, u} B S hS}
    {Y : SmallEtale B S hS} (h : SmallEtale.representedSheaf Y ≅ G) :
    (stalkFiberComparisonIso s h).hom = stalkFiberComparison s h :=
  rfl

/-- The comparison map `c_h` is bijective. -/
theorem bijective_stalkFiberComparison {G : smallEtaleTopos.{u, u} B S hS}
    {Y : SmallEtale B S hS} (h : SmallEtale.representedSheaf Y ≅ G) :
    Function.Bijective (stalkFiberComparison s h) :=
  (isIso_iff_bijective _).mp inferInstance

/-- A morphism of sheaves carries the germ at `s` of a section to the germ of its image. -/
theorem etaleStalkFunctor_map_etaleStalkGerm' {F G : smallEtaleTopos.{u, u} B S hS} (α : F ⟶ G)
    (U : (geometricPointFiber B S hS s).Elements) (t : F.obj.obj (op U.1)) :
    (etaleStalkFunctor.{u, u} B S hS s).map α (etaleStalkGerm.{u, u} B S hS s F U t) =
      etaleStalkGerm.{u, u} B S hS s G U (α.hom.app (op U.1) t) := by
  change (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F.obj) (op U) ≫
    colim.map (Functor.whiskerLeft (CategoryOfElements.π
      (geometricPointFiber B S hS s)).op α.hom)) t = _
  rw [colimit.ι_map]
  rfl

/-- `c_h` sends the germ at a pointed étale neighbourhood `(U, u)` of a section `g ∈ G(U)` to
the lift `u ≫ h⁻¹(g)` of `s` to `Y`. -/
@[simp]
theorem stalkFiberComparison_etaleStalkGerm {G : smallEtaleTopos.{u, u} B S hS}
    {Y : SmallEtale B S hS} (h : SmallEtale.representedSheaf Y ≅ G)
    (U : (geometricPointFiber B S hS s).Elements) (g : G.obj.obj (op U.1)) :
    stalkFiberComparison s h (etaleStalkGerm.{u, u} B S hS s G U g) =
      (geometricPointFiber B S hS s).map (h.inv.hom.app (op U.1) g) U.2 := by
  rw [stalkFiberComparison_def, types_comp_apply, etaleStalkFunctor_map_etaleStalkGerm']
  exact stalkToFiberMap_etaleStalkGerm s Y U _

/-- `c_h` is natural in `G`: for an isomorphism `φ : G ≅ G'`, `c_{h ≪≫ φ} ∘ φ_s = c_h`. -/
@[reassoc (attr := simp)]
theorem etaleStalkFunctor_map_comp_stalkFiberComparison {G G' : smallEtaleTopos.{u, u} B S hS}
    {Y : SmallEtale B S hS} (h : SmallEtale.representedSheaf Y ≅ G) (φ : G ≅ G') :
    (etaleStalkFunctor.{u, u} B S hS s).map φ.hom ≫ stalkFiberComparison s (h ≪≫ φ) =
      stalkFiberComparison s h := by
  rw [stalkFiberComparison_def, stalkFiberComparison_def, Iso.trans_inv, ← Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_assoc]

/-- `c_h` is natural in `Y`: for an isomorphism `v : Y ≅ Y'` in the étale site,
`v ∘ c_h = c_{ṽ⁻¹ ≪≫ h}`, where `ṽ : Ỹ ≅ Ỹ'` is the induced isomorphism of represented
sheaves. -/
theorem stalkFiberComparison_comp_geometricPointFiber_map {G : smallEtaleTopos.{u, u} B S hS}
    {Y Y' : SmallEtale B S hS} (h : SmallEtale.representedSheaf Y ≅ G) (v : Y ≅ Y') :
    stalkFiberComparison s h ≫ (geometricPointFiber B S hS s).map v.hom =
      stalkFiberComparison s (((smallEtaleYoneda B S hS).mapIso v).symm ≪≫ h) := by
  simp only [stalkFiberComparison_def, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, stalkToFiberMap_naturality]

end AlgebraicGeometry.GeometricPoint

end
