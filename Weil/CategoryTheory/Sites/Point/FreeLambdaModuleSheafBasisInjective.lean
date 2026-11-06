module

public import Weil.CategoryTheory.Sites.Point.FreeSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import Weil.Attr

/-!
# The basis map of the free sheaf of modules is injective

Let `(C, J)` be a site, `Λ ≠ 0` a ring and `M` a sheaf of sets on `C`. The free sheaf of
`Λ`-modules `M^Λ` is the sheafification of the presheaf `U ↦ Λ^(M(U))`, and
`ι_M : M ⟶ M^Λ` (the unit of the free–forget adjunction on sheaves) sends a section `p` to the
image of the basis vector `[p]`. At a point `Φ` of the site, the stalk of `ι_M` is the basis map
`M_Φ → Λ^(M_Φ)` under the identification `(M^Λ)_Φ ≅ Λ^(M_Φ)`, hence injective since `1 ≠ 0`
in `Λ`. When the site has enough points, `ι_M` is therefore a monomorphism, i.e. injective on
sections over every object.

The small étale site of a scheme has enough points, the geometric points, so `ι_M` is
injective on sections over every étale `U` over the scheme.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.injective_sheafFiber_map_adjunction_unit_app`:
  the stalk of `ι_M` at any point is injective.
* `CategoryTheory.Sheaf.mono_adjunction_unit_app_adjMax`: on a site with enough points,
  `ι_M` is a monomorphism.
* `CategoryTheory.Sheaf.injective_adjunction_unit_app_adjMax_app`: on a site with enough
  points, `ι_M` is injective on sections over every object.
* `AlgebraicGeometry.SmallEtale.injective_adjunction_unit_app_adjMax_app`: the same on the
  small étale site of a scheme.

## Implementation notes

The proof goes through the stalks, as in the source; the argument "equal germs at a geometric
point over each point of `U`, hence equality on an étale covering, hence equality" is the
conservativity of the family of geometric points
(`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`), applied to
monomorphisms. On the small étale site the ring `Λ` lies in the universe `u` of the scheme,
where sheafification of presheaves of `Λ`-modules is available by instance search.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{max w w'})
  [LocallySmall.{max w w'} C] (Λ : Type w') [Ring Λ]
  [HasWeakSheafify J (ModuleCat.{max w w'} Λ)]

/-- **The stalk of `ι_M : M ⟶ M^Λ` at a point is injective** when `Λ ≠ 0`: under the
identification `(M^Λ)_Φ ≅ Λ^(M_Φ)` it is the basis map `M_Φ → Λ^(M_Φ)`. -/
theorem injective_sheafFiber_map_adjunction_unit_app [Nontrivial Λ]
    (M : Sheaf J (Type (max w w'))) :
    Function.Injective (Φ.sheafFiber.map
      ((Sheaf.adjunction J (ModuleCat.adjMax.{w} Λ)).unit.app M)) := by
  set N := (Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ)).obj M
  set ι := (Sheaf.adjunction J (ModuleCat.adjMax.{w} Λ)).unit.app M
  let c := (Φ.isColimitPresheafFiberCocone (N.obj ⋙ forget (ModuleCat.{max w w'} Λ))).desc
    ((forget (ModuleCat.{max w w'} Λ)).mapCocone (Φ.presheafFiberCocone N.obj))
  have hc : ∀ (X : C) (x : Φ.fiber.obj X) (q : N.obj.obj (op X)),
      c (Φ.toPresheafFiber X x (N.obj ⋙ forget (ModuleCat.{max w w'} Λ)) q) =
        (Φ.toPresheafFiber X x N.obj).hom q := fun X x q ↦
    ConcreteCategory.congr_hom
      ((Φ.isColimitPresheafFiberCocone (N.obj ⋙ forget (ModuleCat.{max w w'} Λ))).fac
        ((forget (ModuleCat.{max w w'} Λ)).mapCocone (Φ.presheafFiberCocone N.obj))
        (op ⟨X, x⟩)) q
  let g : Φ.sheafFiber.obj ((sheafCompose J (forget (ModuleCat.{max w w'} Λ))).obj N) →
      ((Φ.sheafFiber.obj M) →₀ Λ) := fun y ↦ ((Φ.freeMaxSheafFiberIso Λ).hom.app M).hom (c y)
  have key : ∀ m, g (Φ.sheafFiber.map ι m) = Finsupp.single m 1 := by
    intro m
    obtain ⟨X, x, p, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := M.obj) m
    have h1 : Φ.presheafFiber.map ι.hom (Φ.toPresheafFiber X x M.obj p) =
        Φ.toPresheafFiber X x (N.obj ⋙ forget (ModuleCat.{max w w'} Λ))
          (((CategoryTheory.toSheafify J (M.obj ⋙ ModuleCat.freeMax.{w} Λ)).app (op X)).hom
            (Finsupp.single p 1)) :=
      ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality ι.hom X x) p
    refine (congrArg (fun y ↦ ((Φ.freeMaxSheafFiberIso Λ).hom.app M).hom (c y)) h1).trans ?_
    refine (congrArg (fun y ↦ ((Φ.freeMaxSheafFiberIso Λ).hom.app M).hom y)
      (hc X x _)).trans ?_
    exact Φ.freeMaxSheafFiberIso_hom_app_toPresheafFiber Λ M X x p
  intro a b hab
  have := congrArg g hab
  rw [key, key] at this
  exact (Finsupp.single_left_injective one_ne_zero) this

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [LocallySmall.{max w w'} C] [GrothendieckTopology.HasEnoughPoints.{max w w'} J]
  (Λ : Type w') [Ring Λ] [Nontrivial Λ] [HasWeakSheafify J (ModuleCat.{max w w'} Λ)]

/-- **On a site with enough points, `ι_M : M ⟶ M^Λ` is a monomorphism** for `Λ ≠ 0`. -/
theorem mono_adjunction_unit_app_adjMax (M : Sheaf J (Type (max w w'))) :
    Mono ((adjunction J (ModuleCat.adjMax.{w} Λ)).unit.app M) := by
  obtain ⟨P, _, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty.{max w w'} J
  have (Φ : P.FullSubcategory) :
      Mono (Φ.obj.sheafFiber.map ((adjunction J (ModuleCat.adjMax.{w} Λ)).unit.app M)) := by
    rw [mono_iff_injective]
    exact Φ.obj.injective_sheafFiber_map_adjunction_unit_app Λ M
  exact (hP.jointlyReflectMonomorphisms (Type (max w w'))).mono _

/-- **On a site with enough points, `ι_M : M ⟶ M^Λ` is injective on sections** over every
object, for `Λ ≠ 0`. -/
theorem injective_adjunction_unit_app_adjMax_app [HasWeakSheafify J (Type (max w w'))]
    (M : Sheaf J (Type (max w w'))) (U : C) :
    Function.Injective (((adjunction J (ModuleCat.adjMax.{w} Λ)).unit.app M).hom.app (op U)) := by
  have := mono_adjunction_unit_app_adjMax.{w} J Λ M
  rw [← mono_iff_injective]
  infer_instance

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type u) [Ring Λ]
  [Nontrivial Λ]

/-- **The basis map of the free sheaf of `Λ`-modules is injective** (FK I.4). Let `Λ ≠ 0` be a
ring and `M` a sheaf of sets on the small étale site of a scheme `S`. Then
`ι_M : M ⟶ M^Λ`, sending a section `p` to the image of the basis vector `[p]` in the
sheafification of `U ↦ Λ^(M(U))`, is injective on sections over every étale `U` over `S`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_basis_injective"]
theorem injective_adjunction_unit_app_adjMax_app
    (M : Sheaf (topology B S hS) (Type u)) (U : SmallEtale B S hS) :
    Function.Injective (((Sheaf.adjunction (topology B S hS)
      (ModuleCat.adjMax.{u} Λ)).unit.app M).hom.app (op U)) :=
  Sheaf.injective_adjunction_unit_app_adjMax_app.{u} (topology B S hS) Λ M U

end AlgebraicGeometry.SmallEtale
