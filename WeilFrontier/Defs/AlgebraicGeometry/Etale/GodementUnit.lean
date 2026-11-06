module

public import WeilFrontier.Defs.AlgebraicGeometry.Etale.GeometricSkyscraper
public import Weil.Attr

/-!
# The unit of the Godement sheaf

Let `(C, J)` be a site and `(Φ_i)_{i ∈ ι}` a family of points of the site. For a sheaf `G`, the
Godement sheaf is `C⁰(G) = ∏_i (Φ_i)_* (G_{Φ_i})`. The unit `η_G : G ⟶ C⁰(G)` is the morphism
whose `i`-th component is the unit `G ⟶ (Φ_i)_* (G_{Φ_i})` of the adjunction between the stalk
functor at `Φ_i` and the skyscraper functor at `Φ_i`. It is natural in `G`. On sections, it sends
`s ∈ G(U)` to the family `(x ↦ s_x)_i`, where for `x ∈ Φ_i(U)` the element `s_x ∈ G_{Φ_i}` is the
germ of `s` at `(U, x)`.

On the small étale site of a scheme `X` and a family `M` of geometric points of `X`, this is the
map `G ⟶ C⁰(G)` sending `s ∈ G(U)` to the family `(β ↦ s_β)_{α ∈ M}`, where `β` runs through
the lifts `Spec Ω_α ⟶ U` of `α` and `s_β ∈ G_α` is the germ of `s` in the étale neighbourhood
`(U, β)` of `α`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.godementUnit`: the natural transformation
  `𝟭 ⟶ godementFunctor Φ` attached to a family of points of a site.
* `AlgebraicGeometry.godementSheafUnit`: the same on the small étale site, for a family of
  geometric points.

## Main results

* `CategoryTheory.GrothendieckTopology.godementUnit_app_π`: the components of `η_G` are the
  units of the stalk–skyscraper adjunctions.
* `CategoryTheory.GrothendieckTopology.godementSectionsEquiv_godementUnit`: on sections, `η_G`
  sends `s` to the family of its germs.
* `AlgebraicGeometry.godementSheafSectionsEquiv_godementSheafUnit`: the same on the small étale
  site.

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

/-- The unit `η_G : G ⟶ C⁰(G)` of the Godement sheaf attached to a family of points `Φ_i` of a
site: its `i`-th component is the unit `G ⟶ (Φ_i)_* (G_{Φ_i})` of the adjunction between the
stalk functor and the skyscraper functor at `Φ_i`. -/
def godementUnit : 𝟭 (Sheaf J A) ⟶ godementFunctor Φ where
  app G := (Pi.lift fun i => (Φ i).skyscraperSheafAdjunction.unit.app G :
    G ⟶ (godementFunctor Φ).obj G)
  naturality G G' f := by
    refine Limits.Pi.hom_ext _ _ fun i => ?_
    let L : G ⟶ (godementFunctor Φ).obj G :=
      Pi.lift fun i => (Φ i).skyscraperSheafAdjunction.unit.app G
    let L' : G' ⟶ (godementFunctor Φ).obj G' :=
      Pi.lift fun i => (Φ i).skyscraperSheafAdjunction.unit.app G'
    let π' : (godementFunctor Φ).obj G' ⟶ _ :=
      Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G')) i
    let π : (godementFunctor Φ).obj G ⟶ _ :=
      Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i
    have h₁ : L' ≫ π' = (Φ i).skyscraperSheafAdjunction.unit.app G' := Limits.Pi.lift_π _ i
    have h₂ : L ≫ π = (Φ i).skyscraperSheafAdjunction.unit.app G := Limits.Pi.lift_π _ i
    change (f ≫ L') ≫ π' = (L ≫ (godementFunctor Φ).map f) ≫ π'
    have h₃ : (godementFunctor Φ).map f ≫ π' =
        π ≫ (Φ i).skyscraperSheafFunctor.map ((Φ i).sheafFiber.map f) :=
      godementFunctor_map_π Φ f i
    rw [Category.assoc, Category.assoc, h₁, h₃, ← Category.assoc, h₂]
    exact (Φ i).skyscraperSheafAdjunction.unit.naturality f

/-- The `i`-th component of the Godement unit `η_G` is the unit of the adjunction between the
stalk functor and the skyscraper functor at `Φ_i`. -/
@[reassoc (attr := simp)]
lemma godementUnit_app_π (G : Sheaf J A) (i : ι) :
    (godementUnit Φ).app G ≫ Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i =
      (Φ i).skyscraperSheafAdjunction.unit.app G :=
  Limits.Pi.lift_π _ i

/-- The Godement unit `η_G` read on sections over `U`: its component at `(i, x)`, for
`x ∈ Φ_i(U)`, is the germ map `G(U) ⟶ G_{Φ_i}` at `(U, x)`. -/
@[reassoc]
lemma godementUnit_app_godementSectionsIso (G : Sheaf J A) (U : C) (i : ι)
    (x : (Φ i).fiber.obj U) :
    ((godementUnit Φ).app G).hom.app (op U) ≫ (godementSectionsIso Φ G (op U)).hom ≫
        Pi.π (fun i => ∏ᶜ fun _ : (Φ i).fiber.obj U => (Φ i).sheafFiber.obj G) i ≫
          Pi.π (fun _ : (Φ i).fiber.obj U => (Φ i).sheafFiber.obj G) x =
      (Φ i).toPresheafFiber U x G.obj := by
  rw [godementSectionsIso_hom_π_assoc]
  have key : ((godementUnit Φ).app G).hom.app (op U) ≫
        (Pi.π (fun i => (Φ i).skyscraperSheaf ((Φ i).sheafFiber.obj G)) i).hom.app (op U) =
      ((Φ i).skyscraperSheafAdjunction.unit.app G).hom.app (op U) :=
    congrArg (fun g => g.hom.app (op U)) (godementUnit_app_π Φ G i)
  refine (Category.assoc _ _ _).symm.trans ((congrArg
    (· ≫ Pi.π (fun _ : (Φ i).fiber.obj U => (Φ i).sheafFiber.obj G) x) key).trans ?_)
  have hu : ((Φ i).skyscraperSheafAdjunction.unit.app G).hom =
      (Φ i).skyscraperPresheafHomEquiv (𝟙 ((Φ i).presheafFiber.obj G.obj)) := by
    rw [← Adjunction.homEquiv_id]
    exact (Φ i).skyscraperSheafAdjunction_homEquiv_apply_hom _
  rw [hu]
  exact ((Φ i).skyscraperPresheafHomEquiv_app_π _ U x).trans (Category.comp_id _)

section Concrete

variable {FA : A → A → Type*} {CA : A → Type (max w v')} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory.{max w v'} A FA] [PreservesLimitsOfSize.{w, w} (forget A)]

/-- For concrete coefficients, the Godement unit sends a section `s ∈ G(U)` to the family
`(x ↦ s_x)_i`, where `s_x ∈ G_{Φ_i}` is the germ of `s` at `(U, x)` for `x ∈ Φ_i(U)`. -/
lemma godementSectionsEquiv_godementUnit (G : Sheaf J A) (U : C)
    (s : ToType (G.obj.obj (op U))) (i : ι) (x : (Φ i).fiber.obj U) :
    godementSectionsEquiv Φ G (op U) (((godementUnit Φ).app G).hom.app (op U) s) i x =
      (Φ i).toPresheafFiber U x G.obj s := by
  have key := ConcreteCategory.congr_hom (godementUnit_app_godementSectionsIso Φ G U i x) s
  simp only [ConcreteCategory.comp_apply] at key
  rw [godementSectionsEquiv_apply]
  exact key

end Concrete

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {ι : Type u}
  (M : ι → GeometricPoint X) (A : Type u') [Category.{v'} A] [HasProducts.{u} A]
  [HasColimitsOfSize.{u, u} A]

/-- **The Godement unit** on the small étale site of `X`, attached to a family `M` of geometric
points: the morphism of sheaves `η_G : G ⟶ C⁰(G) = ∏_{α ∈ M} α_*(G_α)`, natural in `G`, whose
`α`-component is the unit of the adjunction between the stalk at `α` and the skyscraper sheaf
at `α`. On sections it sends `s ∈ G(U)` to the family of germs `(β ↦ s_β)_{α ∈ M}`
(`godementSheafSectionsEquiv_godementSheafUnit`). -/
@[weil "def_fk112_godement_unit"]
abbrev godementSheafUnit :
    𝟭 (Sheaf (SmallEtale.topology B X hX) A) ⟶ godementSheafFunctor B hX M A :=
  GrothendieckTopology.godementUnit fun i => geometricPointSitePoint B X hX (M i)

/-- The `α`-component of the Godement unit `η_G` is the unit `G ⟶ α_*(G_α)` of the adjunction
between the stalk functor and the skyscraper functor at the geometric point `α`. -/
lemma godementSheafUnit_app_π (G : Sheaf (SmallEtale.topology B X hX) A) (i : ι) :
    (godementSheafUnit B hX M A).app G ≫
        Pi.π (fun i => etaleSkyscraper B X hX (M i) A
          ((geometricPointSitePoint B X hX (M i)).sheafFiber.obj G)) i =
      (etaleStalkSkyscraperAdjunction B X hX (M i) A).unit.app G :=
  GrothendieckTopology.godementUnit_app_π _ G i

section Concrete

variable {A} {FA : A → A → Type*} {CA : A → Type (max u v')}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{max u v'} A FA]
  [PreservesLimitsOfSize.{u, u} (forget A)]

/-- The Godement unit sends a section `s ∈ G(U)` to the family `(β ↦ s_β)_{α ∈ M}`, where for
a lift `β : Spec Ω_α ⟶ U` of `α` the element `s_β ∈ G_α` is the germ of `s` in the étale
neighbourhood `(U, β)` of `α`. -/
@[weil "def_fk112_godement_unit"]
lemma godementSheafSectionsEquiv_godementSheafUnit (G : Sheaf (SmallEtale.topology B X hX) A)
    (U : SmallEtale B X hX) (s : ToType (G.obj.obj (op U))) (i : ι)
    (β : (geometricPointFiber B X hX (M i)).obj U) :
    godementSheafSectionsEquiv B hX M G (op U)
        (((godementSheafUnit B hX M A).app G).hom.app (op U) s) i β =
      (geometricPointSitePoint B X hX (M i)).toPresheafFiber U β G.obj s :=
  GrothendieckTopology.godementSectionsEquiv_godementUnit
    (fun i => geometricPointSitePoint B X hX (M i)) G U s i β

end Concrete

end AlgebraicGeometry

end
