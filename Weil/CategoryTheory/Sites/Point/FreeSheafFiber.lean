module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Weil.CategoryTheory.Sites.FreeLambdaModuleSheafConstant
public import Weil.Attr

/-!
# The stalk of the free sheaf of modules on a sheaf of sets

Let `(C, J)` be a site with a point `Φ`, `Λ` a ring and `M` a sheaf of sets on `C`. The free
sheaf of `Λ`-modules `M^Λ` is the sheafification of the presheaf `U ↦ Λ^(M(U))`, and
`ι_M : M ⟶ M^Λ` sends a section `p` to the image of the basis vector `[p]`. The stalk of `M^Λ`
at `Φ` is the free `Λ`-module on the stalk `M_Φ`: the `Λ`-linear map `Λ^(M_Φ) ⟶ (M^Λ)_Φ`
extending `(ι_M)_Φ` on the basis is an isomorphism. Indeed stalks do not see sheafification,
and the free module functor, a left adjoint, commutes with the filtered colimits computing
stalks.

Applied to the point of the small étale site of a scheme given by a geometric point, this is
the statement for the stalk of `M^Λ` at a geometric point.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.freeMaxSheafFiberIso`: the isomorphism
  `(M^Λ)_Φ ≅ Λ^(M_Φ)`, natural in `M`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.freeMaxSheafFiberIso_inv_app_single`: the inverse
  isomorphism sends the basis vector of the germ of `p` to the germ of `ι_M(p)`, so it is the
  `Λ`-linear extension of `(ι_M)_Φ`.
* `CategoryTheory.GrothendieckTopology.Point.isIso_of_map_single_toPresheafFiber`: any
  `Λ`-linear map `Λ^(M_Φ) ⟶ (M^Λ)_Φ` extending `(ι_M)_Φ` is an isomorphism.
* `AlgebraicGeometry.isIso_of_map_single_toPresheafFiber_geometricPointSitePoint`: the same
  at a geometric point of a scheme, on the small étale site.

## Implementation notes

The free module functor is `ModuleCat.freeMax`, so that the ring `Λ : Type w'` and the universe
`max w w'` of the sets and modules are independent (e.g. `Λ = ZMod n : Type` with sheaves of
sets in `Type u`). The map `(ι_M)_Φ` is described by its values on germs: the germ of a section
`p` of `M` over `X` goes to the germ of the image of the basis vector `[p]` in the sections of
the sheafification over `X`. Every element of the stalk `M_Φ` is such a germ.

On the small étale site of a scheme `S : Scheme.{u}` the stalks of sheaves of sets lie in
`Type u`, and the statement there takes `Λ : Type u`, the universe in which sheafification of
presheaves of `Λ`-modules on that site is available by instance search. For a ring in a smaller
universe (such as `ZMod n : Type`) the general statement applies once sheafification of
`ModuleCat.{u} Λ`-valued presheaves is supplied.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace ModuleCat

variable (R : Type w') [Ring R]

instance preservesColimitsOfSize_freeMax :
    PreservesColimitsOfSize.{v, u} (freeMax.{w} R) :=
  (adjMax.{w} R).leftAdjoint_preservesColimits

end ModuleCat

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{max w w'})
  [LocallySmall.{max w w'} C] (Λ : Type w') [Ring Λ]
  [HasWeakSheafify J (ModuleCat.{max w w'} Λ)]

/-- **The stalk of the free sheaf of modules on a sheaf of sets is the free module on its
stalk**, naturally in the sheaf of sets: `(M^Λ)_Φ ≅ Λ^(M_Φ)`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_stalk"]
def freeMaxSheafFiberIso :
    Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ) ⋙ Φ.sheafFiber ≅
      Φ.sheafFiber (A := Type (max w w')) ⋙ ModuleCat.freeMax.{w} Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type (max w w')))
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ((Functor.whiskeringRight _ _ _).obj
          (ModuleCat.freeMax.{w} Λ))
          (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{max w w'} Λ)) ≪≫
        Φ.presheafFiberCompIso (ModuleCat.freeMax.{w} Λ)) ≪≫
    (Functor.associator _ _ _).symm

/-- The isomorphism `freeMaxSheafFiberIso` sends the germ of the image `ι_M(p)` of the basis
vector `[p]` to the basis vector of the germ of `p`. -/
theorem freeMaxSheafFiberIso_hom_app_toPresheafFiber (M : Sheaf J (Type (max w w'))) (X : C)
    (x : Φ.fiber.obj X) (p : M.obj.obj (op X)) :
    ((Φ.freeMaxSheafFiberIso Λ).hom.app M).hom
      (Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ)).obj M).obj
        (((CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).app (op X)).hom
          (Finsupp.single p 1))) =
      Finsupp.single (Φ.toPresheafFiber X x M.obj p) 1 := by
  have h1 : Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J
        (ModuleCat.freeMax.{w} Λ)).obj M).obj
        (((CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).app (op X)).hom
          (Finsupp.single p 1)) =
      (Φ.presheafFiber.map (CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ))).hom
        ((Φ.toPresheafFiber X x (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).hom
          (Finsupp.single p 1)) :=
    (ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality
      (CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)) X x)
      (Finsupp.single p 1)).symm
  rw [h1]
  change ((Φ.presheafFiberCompIso (ModuleCat.freeMax.{w} Λ)).hom.app M.obj).hom
      ((inv (Φ.presheafFiber.map
        (CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)))).hom
        ((Φ.presheafFiber.map (CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ))).hom
          ((Φ.toPresheafFiber X x (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).hom
            (Finsupp.single p 1)))) = _
  have h2 := ConcreteCategory.congr_hom (IsIso.hom_inv_id
    (Φ.presheafFiber.map (CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ))))
    ((Φ.toPresheafFiber X x (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).hom (Finsupp.single p 1))
  rw [ModuleCat.comp_apply] at h2
  rw [h2]
  have h3 : ((Φ.presheafFiberCompIso (ModuleCat.freeMax.{w} Λ)).hom.app M.obj).hom
      ((Φ.toPresheafFiber X x (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).hom (Finsupp.single p 1)) =
      ((ModuleCat.freeMax.{w} Λ).map (Φ.toPresheafFiber X x M.obj)).hom (Finsupp.single p 1) :=
    ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (ModuleCat.freeMax.{w} Λ) X x M.obj) (Finsupp.single p 1)
  refine h3.trans ?_
  change Finsupp.mapDomain _ (Finsupp.single p 1) = _
  rw [Finsupp.mapDomain_single]

/-- **The inverse of `freeMaxSheafFiberIso` is the `Λ`-linear extension of `(ι_M)_Φ`**: it sends
the basis vector of the germ of a section `p` of `M` to the germ of `ι_M(p)`, the image of the
basis vector `[p]` in the sheafification. -/
@[weil "lem_fk104_free_lambda_module_sheaf_stalk"]
theorem freeMaxSheafFiberIso_inv_app_single (M : Sheaf J (Type (max w w'))) (X : C)
    (x : Φ.fiber.obj X) (p : M.obj.obj (op X)) :
    ((Φ.freeMaxSheafFiberIso Λ).inv.app M).hom
        (Finsupp.single (Φ.toPresheafFiber X x M.obj p) 1) =
      Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ)).obj M).obj
        (((CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).app (op X)).hom
          (Finsupp.single p 1)) := by
  have key : ∀ g, ((Φ.freeMaxSheafFiberIso Λ).inv.app M).hom
      (((Φ.freeMaxSheafFiberIso Λ).hom.app M).hom g) = g := fun g ↦
    congrArg (fun φ ↦ ModuleCat.Hom.hom φ g) ((Φ.freeMaxSheafFiberIso Λ).hom_inv_id_app M)
  exact (congrArg ((Φ.freeMaxSheafFiberIso Λ).inv.app M).hom
    (Φ.freeMaxSheafFiberIso_hom_app_toPresheafFiber Λ M X x p).symm).trans (key _)

/-- **The `Λ`-linear map `Λ^(M_Φ) ⟶ (M^Λ)_Φ` extending `(ι_M)_Φ` is an isomorphism.** A linear
map which sends the basis vector of the germ of every section `p` of `M` to the germ of
`ι_M(p)` is the inverse of `freeMaxSheafFiberIso`, hence an isomorphism. -/
@[weil "lem_fk104_free_lambda_module_sheaf_stalk"]
theorem isIso_of_map_single_toPresheafFiber (M : Sheaf J (Type (max w w')))
    (f : (ModuleCat.freeMax.{w} Λ).obj (Φ.sheafFiber.obj M) ⟶
      Φ.sheafFiber.obj ((Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ)).obj M))
    (hf : ∀ (X : C) (x : Φ.fiber.obj X) (p : M.obj.obj (op X)),
      f.hom (Finsupp.single (Φ.toPresheafFiber X x M.obj p) 1) =
        Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ)).obj M).obj
          (((CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).app (op X)).hom
            (Finsupp.single p 1))) :
    IsIso f := by
  have : f = (Φ.freeMaxSheafFiberIso Λ).inv.app M := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro m
    apply LinearMap.ext_ring
    obtain ⟨X, x, p, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := M.obj) m
    exact (hf X x p).trans (Φ.freeMaxSheafFiberIso_inv_app_single Λ M X x p).symm
  rw [this]
  infer_instance

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

open CategoryTheory.GrothendieckTopology

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : GeometricPoint S)
  (Λ : Type u) [Ring Λ]

/-- **The stalk of the free sheaf of `Λ`-modules at a geometric point.** Let `M` be a sheaf of
sets on the small étale site of `S`, `s` a geometric point of `S` and `M^Λ` the free sheaf of
`Λ`-modules on `M`. A `Λ`-linear map `Λ^(M_s) ⟶ (M^Λ)_s` which extends `(ι_M)_s`, i.e. sends
the basis vector of the germ of a section `p` at an étale neighbourhood `(X, x)` of `s` to the
germ of `ι_M(p)`, is an isomorphism. Such a map exists: it is the inverse of
`Point.freeMaxSheafFiberIso` (`Point.freeMaxSheafFiberIso_inv_app_single`). -/
@[weil "lem_fk104_free_lambda_module_sheaf_stalk"]
theorem isIso_of_map_single_toPresheafFiber_geometricPointSitePoint
    (M : Sheaf (SmallEtale.topology B S hS) (Type u))
    (f : (ModuleCat.freeMax.{u} Λ).obj ((geometricPointSitePoint B S hS s).sheafFiber.obj M) ⟶
      (geometricPointSitePoint B S hS s).sheafFiber.obj
        ((Sheaf.composeAndSheafify _ (ModuleCat.freeMax.{u} Λ)).obj M))
    (hf : ∀ (X : SmallEtale B S hS) (x : (geometricPointSitePoint B S hS s).fiber.obj X)
      (p : M.obj.obj (op X)),
      f.hom (Finsupp.single ((geometricPointSitePoint B S hS s).toPresheafFiber X x M.obj p) 1) =
        (geometricPointSitePoint B S hS s).toPresheafFiber X x
          ((Sheaf.composeAndSheafify _ (ModuleCat.freeMax.{u} Λ)).obj M).obj
          (((CategoryTheory.toSheafify _ (M.obj ⋙ ModuleCat.freeMax.{u} Λ)).app (op X)).hom
            (Finsupp.single p 1))) :
    IsIso f :=
  (geometricPointSitePoint B S hS s).isIso_of_map_single_toPresheafFiber Λ M f hf

end AlgebraicGeometry
