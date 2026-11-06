module

public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import StacksFrontier.AlgebraicGeometry.Etale.GeometricSkyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import Weil.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# The Godement sheaf

Let `(C, J)` be a site, `A` a category with products and colimits, and `(Φ_i)_{i ∈ ι}` a family
of points of the site. For a sheaf `G` with values in `A`, the *Godement sheaf* is the product
`C⁰(G) = ∏_i (Φ_i)_* (G_{Φ_i})` of the skyscraper sheaves at the points `Φ_i` with value the
stalks `G_{Φ_i}`. Its sections over `U` are the families indexed by `i` of `G_{Φ_i}`-valued maps
on the fibre `Φ_i(U)`, restriction along `V ⟶ U` is precomposition with `Φ_i(V) ⟶ Φ_i(U)`,
and a morphism `G ⟶ G'` acts through the induced maps of stalks. So `G ↦ C⁰(G)` is a functor.

On the small étale site of a scheme `X` (relative to a big étale site `B` containing `X`) a
family `M : ι → GeometricPoint X` of geometric points gives points of the site, whose fibre at
`U` is the set `P_α(U)` of `X`-morphisms `Spec Ω_α ⟶ U` lifting `α`. The Godement sheaf of an
étale sheaf `G` is then
`C⁰(G)(U) = ∏_{α ∈ M} Map(P_α(U), G_α)`, the product over `α` of the skyscraper sheaves
`α_*(G_α)`. The family `X.algClosedPoint : X → GeometricPoint X` (one geometric point over each
point of `X`) is a choice of `M` meeting every point.

## Main definitions

* `CategoryTheory.GrothendieckTopology.godementFunctor`: the Godement functor attached to a family
  of points of a site.
* `CategoryTheory.GrothendieckTopology.godementSectionsEquiv`: for concrete coefficients, the
  sections of `C⁰(G)` over `U` are the families of maps `Φ_i(U) → G_{Φ_i}`.
* `AlgebraicGeometry.godementSheafFunctor`: the Godement functor on the small étale site attached
  to a family of geometric points.
* `AlgebraicGeometry.godementSheafSectionsEquiv`: its sections over `U` are the families of maps
  `P_α(U) → G_α`.

## Main results

* `CategoryTheory.GrothendieckTopology.godementSectionsEquiv_map`: restriction is precomposition.
* `CategoryTheory.GrothendieckTopology.godementSectionsEquiv_functor_map`: morphisms act through
  the maps of stalks.
* `AlgebraicGeometry.godementSheafSectionsEquiv_map`,
  `AlgebraicGeometry.godementSheafSectionsEquiv_functor_map`: the same on the small étale site.
* `AlgebraicGeometry.godementSheafFunctor_obj`: `C⁰(G)` is the product of the étale skyscraper
  sheaves `α_*(G_α)`.

## Implementation notes

Geometric points take values in algebraically closed fields and the étale site is the bounded
small étale site `SmallEtale B X hX`, as in the Stacks project. The set `𝔐` of the source is a
family `M : ι → GeometricPoint X` indexed by a type `ι` in the universe of `X`, so that the
product exists in categories of sheaves of abelian groups or modules in that universe; the
condition that `𝔐` meets every point is not needed for the definition and is a hypothesis of
the results that use it. The source writes `α^*`; the skyscraper sheaf is `α_*`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12.
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
  {ι : Type w} (Φ : ι → Point.{w} J)

/-- The Godement functor attached to a family of points `Φ_i` of a site: a sheaf `G` goes to
the product `∏_i (Φ_i)_* (G_{Φ_i})` of the skyscraper sheaves at the points with value the
stalks of `G`. -/
def godementFunctor : Sheaf J A ⥤ Sheaf J A where
  obj G := ∏ᶜ fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)
  map f := Limits.Pi.map fun i => (Φ i).skyscraperSheafFunctor.map ((Φ i).sheafFiber.map f)
  map_id G := by
    ext i : 1
    simp
  map_comp f g := by
    ext i : 1
    simp

lemma godementFunctor_obj (G : Sheaf J A) :
    (godementFunctor Φ).obj G = ∏ᶜ fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G) :=
  rfl

@[reassoc (attr := simp)]
lemma godementFunctor_map_π {G G' : Sheaf J A} (f : G ⟶ G') (i : ι) :
    (godementFunctor Φ).map f ≫
        Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G')) i =
      Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i ≫
        (Φ i).skyscraperSheafFunctor.map ((Φ i).sheafFiber.map f) :=
  Limits.Pi.map_π (fun i => (Φ i).skyscraperSheafFunctor.map ((Φ i).sheafFiber.map f)) i

/-- The sections of the Godement sheaf over `U`: the product over `i` of the products of copies
of the stalk `G_{Φ_i}` indexed by the fibre `Φ_i(U)`. -/
def godementSectionsIso (G : Sheaf J A) (U : Cᵒᵖ) :
    ((godementFunctor Φ).obj G).obj.obj U ≅
      ∏ᶜ fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G :=
  PreservesProduct.iso (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj U)
    (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G))

@[reassoc (attr := simp)]
lemma godementSectionsIso_hom_π (G : Sheaf J A) (U : Cᵒᵖ) (i : ι) :
    (godementSectionsIso Φ G U).hom ≫
        Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G) i =
      (Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i).hom.app U := by
  rw [godementSectionsIso, PreservesProduct.iso_hom]
  exact piComparison_comp_π _ _ i

/-- Restriction in the Godement sheaf along `h : V ⟶ U`, read on sections: the component at
`(i, v)` of the restriction of a section is its component at `(i, Φ_i(h)(v))`. -/
@[reassoc]
lemma godementSectionsIso_map {U V : C} (G : Sheaf J A) (h : V ⟶ U) (i : ι)
    (v : (Φ i).fiber.obj V) :
    ((godementFunctor Φ).obj G).obj.map h.op ≫ (godementSectionsIso Φ G (op V)).hom ≫
        Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj V => (Φ i).sheafFiber.obj G) i ≫
          Pi.π (fun _ : (Φ i).fiber.obj V => (Φ i).sheafFiber.obj G) v =
      (godementSectionsIso Φ G (op U)).hom ≫
        Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U => (Φ i).sheafFiber.obj G) i ≫
          Pi.π (fun _ : (Φ i).fiber.obj U => (Φ i).sheafFiber.obj G) ((Φ i).fiber.map h v) := by
  rw [godementSectionsIso_hom_π_assoc, godementSectionsIso_hom_π_assoc]
  refine ((Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i).hom.naturality_assoc
    h.op _).trans ?_
  congr 1
  change ((Φ i).skyscraperPresheafFunctor.obj ((Φ i).sheafFiber.obj G)).map h.op ≫ _ = _
  simp only [Point.skyscraperPresheafFunctor_obj_map]
  exact (Pi.map'_comp_π _ _ _).trans (Category.comp_id _)

/-- Functoriality of the Godement sheaf, read on sections: a morphism `f : G ⟶ G'` acts on the
component at `(i, u)` through the map of stalks `f_{Φ_i}`. -/
@[reassoc]
lemma godementSectionsIso_functor_map {G G' : Sheaf J A} (f : G ⟶ G') (U : Cᵒᵖ) (i : ι)
    (u : (Φ i).fiber.obj U.unop) :
    ((godementFunctor Φ).map f).hom.app U ≫ (godementSectionsIso Φ G' U).hom ≫
        Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G') i ≫
          Pi.π (fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G') u =
      (godementSectionsIso Φ G U).hom ≫
        Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G) i ≫
          Pi.π (fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G) u ≫
            (Φ i).sheafFiber.map f := by
  rw [godementSectionsIso_hom_π_assoc, godementSectionsIso_hom_π_assoc]
  have key : ((godementFunctor Φ).map f).hom.app U ≫
        (Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G')) i).hom.app U =
      (Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i).hom.app U ≫
        ((Φ i).skyscraperSheafFunctor.map ((Φ i).sheafFiber.map f)).hom.app U :=
    congrArg (fun g => g.hom.app U) (godementFunctor_map_π Φ f i)
  refine ((Category.assoc _ _ _).symm.trans ((congrArg
    (· ≫ Pi.π (fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G') u) key).trans
      (Category.assoc _ _ _))).trans ?_
  congr 1
  simp only [Point.skyscraperSheafFunctor_map_hom, Point.skyscraperPresheafFunctor_map_app]
  exact Limits.Pi.map_π _ _

section Concrete

variable {FA : A → A → Type*} {CA : A → Type (max w v')} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory.{max w v'} A FA] [PreservesLimitsOfSize.{w, w} (forget A)]

/-- For concrete coefficients whose forgetful functor preserves products, the sections of the
Godement sheaf `C⁰(G)` over `U` are the families, indexed by `i`, of maps from the fibre
`Φ_i(U)` to the stalk `G_{Φ_i}`. -/
def godementSectionsEquiv (G : Sheaf J A) (U : Cᵒᵖ) :
    ToType (((godementFunctor Φ).obj G).obj.obj U) ≃
      ∀ i, (Φ i).fiber.obj U.unop → ToType ((Φ i).sheafFiber.obj G) :=
  ((forget A).mapIso (godementSectionsIso Φ G U)).toEquiv.trans
    ((Concrete.productEquiv _).trans (Equiv.piCongrRight fun _ => Concrete.productEquiv _))

lemma godementSectionsEquiv_apply (G : Sheaf J A) (U : Cᵒᵖ)
    (c : ToType (((godementFunctor Φ).obj G).obj.obj U)) (i : ι) (u : (Φ i).fiber.obj U.unop) :
    godementSectionsEquiv Φ G U c i u =
      Pi.π (fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G) u
        (Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U.unop => (Φ i).sheafFiber.obj G) i
          ((godementSectionsIso Φ G U).hom c)) := by
  simp only [godementSectionsEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    Concrete.productEquiv_apply_apply]
  try rfl

/-- Restriction in the Godement sheaf is precomposition: for `h : V ⟶ U`, the restriction of a
section `c = (c_i)_i` with `c_i : Φ_i(U) → G_{Φ_i}` is `(c_i ∘ Φ_i(h))_i`. -/
lemma godementSectionsEquiv_map {U V : C} (G : Sheaf J A) (h : V ⟶ U)
    (c : ToType (((godementFunctor Φ).obj G).obj.obj (op U))) (i : ι) :
    godementSectionsEquiv Φ G (op V) (((godementFunctor Φ).obj G).obj.map h.op c) i =
      godementSectionsEquiv Φ G (op U) c i ∘ (Φ i).fiber.map h := by
  funext v
  have key := ConcreteCategory.congr_hom (godementSectionsIso_map Φ G h i v) c
  simp only [ConcreteCategory.comp_apply] at key
  rw [godementSectionsEquiv_apply, Function.comp_apply, godementSectionsEquiv_apply]
  exact key

/-- A morphism `f : G ⟶ G'` acts on the sections of the Godement sheaf through the maps of
stalks: `(c_i)_i ↦ (f_{Φ_i} ∘ c_i)_i`. -/
lemma godementSectionsEquiv_functor_map {G G' : Sheaf J A} (f : G ⟶ G') (U : Cᵒᵖ)
    (c : ToType (((godementFunctor Φ).obj G).obj.obj U)) (i : ι) :
    godementSectionsEquiv Φ G' U (((godementFunctor Φ).map f).hom.app U c) i =
      (Φ i).sheafFiber.map f ∘ godementSectionsEquiv Φ G U c i := by
  funext u
  have key := ConcreteCategory.congr_hom (godementSectionsIso_functor_map Φ f U i u) c
  simp only [ConcreteCategory.comp_apply] at key
  rw [godementSectionsEquiv_apply, Function.comp_apply, godementSectionsEquiv_apply]
  exact key

end Concrete

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

/-- The geometric point `X.algClosedPoint x` lies over `x`: the family `X.algClosedPoint` of
geometric points meets every point of `X`. -/
@[simp]
lemma Scheme.point_algClosedPoint (X : Scheme.{u}) (x : X) : (X.algClosedPoint x).point = x := by
  rw [GeometricPoint.point_eq_hom_closedPoint, Scheme.algClosedPoint_hom]
  exact Scheme.algClosedPointHom_apply X x _

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {ι : Type u}
  (M : ι → GeometricPoint X) (A : Type u') [Category.{v'} A] [HasProducts.{u} A]
  [HasColimitsOfSize.{u, u} A]

/-- **The Godement sheaf** on the small étale site of `X`, attached to a family `M` of geometric
points: an étale sheaf `G` goes to `C⁰(G) = ∏_{α ∈ M} α_*(G_α)`, whose sections over `U` are the
families of maps `P_α(U) → G_α` on the sets `P_α(U)` of lifts of `α` to `U`. -/
@[weil "def_fk112_godement_resolution_degree_zero"]
abbrev godementSheafFunctor :
    Sheaf (SmallEtale.topology B X hX) A ⥤ Sheaf (SmallEtale.topology B X hX) A :=
  GrothendieckTopology.godementFunctor fun i => geometricPointSitePoint B X hX (M i)

/-- The Godement sheaf `C⁰(G)` is the product over `α ∈ M` of the étale skyscraper sheaves
`α_*(G_α)` with value the stalks of `G`. -/
lemma godementSheafFunctor_obj (G : Sheaf (SmallEtale.topology B X hX) A) :
    (godementSheafFunctor B hX M A).obj G =
      ∏ᶜ fun i => etaleSkyscraper B X hX (M i) A
        ((geometricPointSitePoint B X hX (M i)).sheafFiber.obj G) :=
  rfl

section Concrete

variable {A} {FA : A → A → Type*} {CA : A → Type (max u v')}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{max u v'} A FA]
  [PreservesLimitsOfSize.{u, u} (forget A)]

/-- The sections of the Godement sheaf `C⁰(G)` over an object `U` of the small étale site: the
families, indexed by `α ∈ M`, of maps from the set `P_α(U)` of `X`-morphisms
`Spec Ω_α ⟶ U` lifting `α` to the stalk `G_α`. -/
@[weil "def_fk112_godement_resolution_degree_zero"]
def godementSheafSectionsEquiv (G : Sheaf (SmallEtale.topology B X hX) A)
    (U : (SmallEtale B X hX)ᵒᵖ) :
    ToType (((godementSheafFunctor B hX M A).obj G).obj.obj U) ≃
      ∀ i, (geometricPointFiber B X hX (M i)).obj U.unop →
        ToType ((geometricPointSitePoint B X hX (M i)).sheafFiber.obj G) :=
  GrothendieckTopology.godementSectionsEquiv _ G U

/-- Restriction in the Godement sheaf along `h : V ⟶ U` is precomposition with the map
`P_α(V) → P_α(U)`, `β ↦ h ∘ β`. -/
@[weil "def_fk112_godement_resolution_degree_zero"]
lemma godementSheafSectionsEquiv_map {U V : SmallEtale B X hX}
    (G : Sheaf (SmallEtale.topology B X hX) A) (h : V ⟶ U)
    (c : ToType (((godementSheafFunctor B hX M A).obj G).obj.obj (op U))) (i : ι) :
    godementSheafSectionsEquiv B hX M G (op V)
        (((godementSheafFunctor B hX M A).obj G).obj.map h.op c) i =
      godementSheafSectionsEquiv B hX M G (op U) c i ∘
        (geometricPointFiber B X hX (M i)).map h :=
  GrothendieckTopology.godementSectionsEquiv_map _ G h c i

/-- A morphism of étale sheaves `f : G ⟶ G'` acts on the Godement sheaf through the induced maps
of stalks `f_α : G_α → G'_α`. -/
@[weil "def_fk112_godement_resolution_degree_zero"]
lemma godementSheafSectionsEquiv_functor_map {G G' : Sheaf (SmallEtale.topology B X hX) A}
    (f : G ⟶ G') (U : (SmallEtale B X hX)ᵒᵖ)
    (c : ToType (((godementSheafFunctor B hX M A).obj G).obj.obj U)) (i : ι) :
    godementSheafSectionsEquiv B hX M G' U (((godementSheafFunctor B hX M A).map f).hom.app U c) i =
      (geometricPointSitePoint B X hX (M i)).sheafFiber.map f ∘
        godementSheafSectionsEquiv B hX M G U c i :=
  GrothendieckTopology.godementSectionsEquiv_functor_map _ f U c i

end Concrete

end AlgebraicGeometry

end
