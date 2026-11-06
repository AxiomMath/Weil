module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroCharacterization

/-!
# Stalks of the restriction of an étale presheaf to an open subscheme

Let `j : U ⟶ X` be an open immersion, regarded as an object of the small étale site of `X`,
let `Q` be a presheaf on the small étale site of `X` with values in a category `A`, and let `p`
be a geometric point of `U`. The restriction `Q|_U` is `Q` composed with the functor
`(V ⟶ U) ↦ (V ⟶ U ⟶ X)`. Regarding an étale neighbourhood `(V ⟶ U, v)` of `p` as the étale
neighbourhood `(V ⟶ U ⟶ X, v)` of `j ∘ p` induces a map of stalks
`(Q|_U)_p ⟶ Q_{j p}`, sending the germ of a section at `(V, v)` to its germ at `(V, v)`. This
map is an isomorphism, natural in `Q`.

The proof is the cofinality of the neighbourhoods coming from `U`: composition with `j` is a
fully faithful functor on étale neighbourhoods (as `j` is a monomorphism), every étale
neighbourhood `(W, w)` of `j p` is refined by its base change `W ×_X U`, which carries the lift
of `w`, and the neighbourhoods of `j p` are cofiltered; so the functor on neighbourhoods is
initial and the two colimits agree.

## Main definitions

* `AlgebraicGeometry.etaleStalkPostcomposeIso` — the natural isomorphism
  `(Q|_U)_p ≅ Q_{j p}` of stalk functors on presheaves with values in `A`.

## Main results

* `AlgebraicGeometry.germ_etaleStalkPostcomposeIso_hom` — the isomorphism sends the germ at
  `(V, v)` to the germ at the composed neighbourhood `(V ⟶ U ⟶ X, v)`.
* `AlgebraicGeometry.etaleStalkPostcomposeIso_hom_naturality` — naturality in `Q`.
* `AlgebraicGeometry.bijective_etaleStalkPostcomposeIso_hom` — for presheaves of sets, the map
  of stalks is bijective.

## Implementation notes

The statement is made on the small étale site `SmallEtale B X hX` of a big étale site, with
geometric points over algebraically closed fields, and for presheaves with values in any
category with colimits indexed by `u`-small categories (sets and abelian groups among them).
The restriction of the source to the étale category of noetherian separated `X`-schemes is
the same composition with `(V ⟶ U) ↦ (V ⟶ U ⟶ X)`. The initiality of the functor on
neighbourhoods is `AlgebraicGeometry.liftNeighborhoods_initial`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  [IsOpenImmersion (B.inclusion.map U.obj.hom)] (p : GeometricPoint U.obj.left.1)
  (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The stalk of the restriction to an open subscheme.** For an open immersion `j : U ⟶ X`
and a geometric point `p` of `U`, the stalk at `p` of the restriction `Q|_U` of a presheaf `Q`
on the small étale site of `X` is the stalk of `Q` at `j ∘ p`, naturally in `Q`; the map is
induced by regarding an étale neighbourhood of `p` as an étale neighbourhood of `j ∘ p`. -/
@[weil "lem_fk108_open_restriction_stalk"]
def etaleStalkPostcomposeIso :
    (Functor.whiskeringLeft _ _ A).obj (smallEtalePostcompose B X hX U).op ⋙
        etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property p A ≅
      etaleStalkPresheafFunctor B X hX (p.map (B.inclusion.map U.obj.hom)) A :=
  haveI := liftNeighborhoods_initial B X hX U p
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ A).obj
      (CategoryOfElements.π (geometricPointFiber B X hX
        (p.map (B.inclusion.map U.obj.hom)))).op)
    (Functor.Final.colimIso (liftNeighborhoods B X hX U p).op)

variable {A} in
/-- The isomorphism `(Q|_U)_p ≅ Q_{j p}` sends the germ of a section at an étale neighbourhood
`(V ⟶ U, v)` of `p` to its germ at the étale neighbourhood `(V ⟶ U ⟶ X, v)` of `j ∘ p`. -/
@[weil "lem_fk108_open_restriction_stalk", reassoc]
theorem germ_etaleStalkPostcomposeIso_hom (Q : (SmallEtale B X hX)ᵒᵖ ⥤ A)
    (V : (geometricPointFiber B U.obj.left.1 U.obj.left.property p).Elements) :
    colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B U.obj.left.1 U.obj.left.property p)).op ⋙
          (smallEtalePostcompose B X hX U).op ⋙ Q) (op V) ≫
        (etaleStalkPostcomposeIso B X hX U p A).hom.app Q =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X hX
        (p.map (B.inclusion.map U.obj.hom)))).op ⋙ Q)
        (op ((liftNeighborhoods B X hX U p).obj V)) := by
  have := liftNeighborhoods_initial B X hX U p
  exact Functor.Final.ι_colimitIso_hom (liftNeighborhoods B X hX U p).op
    ((CategoryOfElements.π (geometricPointFiber B X hX
      (p.map (B.inclusion.map U.obj.hom)))).op ⋙ Q) (op V)

variable {A} in
/-- The isomorphism `(Q|_U)_p ≅ Q_{j p}` is natural in the presheaf `Q`. -/
@[weil "lem_fk108_open_restriction_stalk", reassoc]
theorem etaleStalkPostcomposeIso_hom_naturality {Q Q' : (SmallEtale B X hX)ᵒᵖ ⥤ A}
    (φ : Q ⟶ Q') :
    (etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property p A).map
          (Functor.whiskerLeft (smallEtalePostcompose B X hX U).op φ) ≫
        (etaleStalkPostcomposeIso B X hX U p A).hom.app Q' =
      (etaleStalkPostcomposeIso B X hX U p A).hom.app Q ≫
        (etaleStalkPresheafFunctor B X hX (p.map (B.inclusion.map U.obj.hom)) A).map φ :=
  (etaleStalkPostcomposeIso B X hX U p A).hom.naturality φ

/-- For a presheaf of sets `Q` on the small étale site of `X`, the map `(Q|_U)_p ⟶ Q_{j p}`
induced on stalks by composing étale neighbourhoods of `p` with the open immersion `j` is
bijective. -/
@[weil "lem_fk108_open_restriction_stalk"]
theorem bijective_etaleStalkPostcomposeIso_hom (Q : (SmallEtale B X hX)ᵒᵖ ⥤ Type u) :
    Function.Bijective ((etaleStalkPostcomposeIso B X hX U p (Type u)).hom.app Q) :=
  (isIso_iff_bijective _).mp inferInstance

end AlgebraicGeometry

end
