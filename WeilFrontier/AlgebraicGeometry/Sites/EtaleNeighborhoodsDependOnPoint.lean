module

public import WeilFrontier.AlgebraicGeometry.Sites.EtaleNeighborhoodsSeparableClosure
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# Étale neighbourhoods depend only on the underlying point

Let `s : Spec K ⟶ X` and `t : Spec L ⟶ X` be morphisms from spectra of separably closed fields
with the same underlying point `x₀`. Then the categories of étale neighbourhoods of `s` and of
`t` are isomorphic, compatibly with the forgetful functors to the small étale site of `X`.

Indeed, let `k' ⊆ K` and `l' ⊆ L` be the separable closures of `κ(x₀)`, and `s'`, `t'` the
induced morphisms `Spec k' ⟶ X`, `Spec l' ⟶ X`. Both `k'` and `l'` are separable closures of
`κ(x₀)`, so there is a `κ(x₀)`-isomorphism `α : l' ≃ k'`, and `Spec α` is an isomorphism
`t' ≅ s'` of `X`-schemes. Precomposition with it identifies the étale neighbourhoods of `s'`
and of `t'`, and the étale neighbourhoods of `s'` (resp. `t'`) are those of `s` (resp. `t`) by
`AlgebraicGeometry.Scheme.neighborhoodsIsoResidueSeparableClosure`.

## Main definitions

* `AlgebraicGeometry.Scheme.residueSeparableClosurePointIsoOfEq`: the isomorphism `t' ≅ s'`
  over `X`.
* `AlgebraicGeometry.Scheme.neighborhoodsIsoOfEq`: the isomorphism of the categories of étale
  neighbourhoods of `t` and of `s`.
* `AlgebraicGeometry.GeometricPoint.neighborhoodsEquivOfLiesOver`: for geometric points `x`, `y`
  with the same underlying point, the equivalence `EtaleNeighborhood y ≌ EtaleNeighborhood x`.

## Main results

* `AlgebraicGeometry.Scheme.neighborhoodsIsoOfEq_hom_toFunctor_comp_π`: the isomorphism
  commutes with the forgetful functors to `X.Etale`.
* `AlgebraicGeometry.GeometricPoint.neighborhoodsEquivOfLiesOver_functor_comp_forget`: the
  equivalence commutes with the forgetful functors to `X.Etale`.

## Implementation notes

The statement is made for morphisms from spectra of separably closed fields, with the
categories of étale neighbourhoods taken as categories of elements of the fibre functors of
the points `AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site; for geometric
points (algebraically closed fields) it is transported to
`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood` by
`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.equivFiberElements`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

/- Stated on Mathlib's small étale site `X.Etale`, the site of the formalized `N(x)`
(`GeometricPoint.EtaleNeighborhood.forget`). FK's equivalence is obtained as an isomorphism of
categories (stronger). -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {K L : Type u} [Field K] [Field L]

/-- The separable closure in `K` of the residue field `κ(x₀)`, embedded in `K` by `φ`. -/
def sepClosureOfResidueField (x₀ : X) (φ : X.residueField x₀ ⟶ .of K) : Subfield K :=
  letI := φ.hom.toAlgebra
  (separableClosure (X.residueField x₀) K).toSubfield

lemma mem_sepClosureOfResidueField (x₀ : X) (φ : X.residueField x₀ ⟶ .of K)
    (a : X.residueField x₀) : φ a ∈ sepClosureOfResidueField x₀ φ := by
  let _ := φ.hom.toAlgebra
  exact isSeparable_algebraMap (F := X.residueField x₀) (K := K) a

/-- The morphism `Spec k' ⟶ X` given by `x₀` and `κ(x₀) ⟶ k'`, where `k'` is the separable
closure of `κ(x₀)` in `K` along `φ`. -/
def sepClosureOfResidueFieldPoint (x₀ : X) (φ : X.residueField x₀ ⟶ .of K) :
    Spec (.of (sepClosureOfResidueField x₀ φ)) ⟶ X :=
  (X.SpecToEquivOfField _).symm
    ⟨x₀, CommRingCat.ofHom (φ.hom.codRestrict _ (mem_sepClosureOfResidueField x₀ φ))⟩

lemma residueSeparableClosurePoint_eq (s : Spec (.of K) ⟶ X) :
    residueSeparableClosurePoint s =
      sepClosureOfResidueFieldPoint (X.SpecToEquivOfField K s).1 (X.SpecToEquivOfField K s).2 :=
  rfl

/-- For two embeddings of `κ(x₀)` in separably closed fields, the two morphisms from the
spectra of the separable closures of `κ(x₀)` are isomorphic over `X`. -/
lemma nonempty_iso_sepClosureOfResidueFieldPoint [IsSepClosed K] [IsSepClosed L] (x₀ : X)
    (φ : X.residueField x₀ ⟶ .of K) (ψ : X.residueField x₀ ⟶ .of L) :
    Nonempty (Over.mk (sepClosureOfResidueFieldPoint x₀ ψ) ≅
      Over.mk (sepClosureOfResidueFieldPoint x₀ φ)) := by
  let _ := φ.hom.toAlgebra
  let _ := ψ.hom.toAlgebra
  let e : separableClosure (X.residueField x₀) L ≃ₐ[X.residueField x₀]
      separableClosure (X.residueField x₀) K :=
    IsSepClosure.equiv (X.residueField x₀) _ _
  let e' : sepClosureOfResidueField x₀ φ ≃+* sepClosureOfResidueField x₀ ψ :=
    e.symm.toRingEquiv
  refine ⟨Over.isoMk (Scheme.Spec.mapIso e'.toCommRingCatIso.op) ?_⟩
  simp only [sepClosureOfResidueFieldPoint, SpecToEquivOfField_symm_apply, Over.mk_hom,
    Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
  have hc : CommRingCat.ofHom (φ.hom.codRestrict _ (mem_sepClosureOfResidueField x₀ φ)) ≫
      e'.toCommRingCatIso.hom =
        CommRingCat.ofHom (ψ.hom.codRestrict _ (mem_sepClosureOfResidueField x₀ ψ)) := by
    ext a
    exact congrArg Subtype.val (e.symm.commutes a)
  exact (Spec.map_comp_assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecResidueField x₀)
    (congrArg Spec.map hc))

variable [IsSepClosed K] [IsSepClosed L]

/-- For `s : Spec K ⟶ X` and `t : Spec L ⟶ X` from separably closed fields with the same
underlying point, the isomorphism over `X` between the induced morphisms `t' : Spec l' ⟶ X` and
`s' : Spec k' ⟶ X` from the separable closures of the residue field. -/
def residueSeparableClosurePointIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    Over.mk (residueSeparableClosurePoint t) ≅ Over.mk (residueSeparableClosurePoint s) :=
  Nonempty.some <| by
    have key : ∀ (p : Σ x, X.residueField x ⟶ .of K) (q : Σ x, X.residueField x ⟶ .of L),
        p.1 = q.1 → Nonempty (Over.mk (sepClosureOfResidueFieldPoint q.1 q.2) ≅
          Over.mk (sepClosureOfResidueFieldPoint p.1 p.2)) := by
      rintro ⟨x₀, φ⟩ ⟨_, ψ⟩ rfl
      exact nonempty_iso_sepClosureOfResidueFieldPoint x₀ φ ψ
    refine key (X.SpecToEquivOfField K s) (X.SpecToEquivOfField L t) ?_
    simp only [SpecToEquivOfField_apply_fst]
    have h₁ : IsLocalRing.closedPoint K = (default : Spec (.of K)) := Subsingleton.elim _ _
    have h₂ : IsLocalRing.closedPoint L = (default : Spec (.of L)) := Subsingleton.elim _ _
    rw [h₁, h₂]
    exact h

/-- Precomposition with the isomorphism `t' ≅ s'`, as an isomorphism of the fibre functors of
the points of the small étale site defined by `t'` and by `s'`. -/
def fiberIsoResidueSeparableClosurePointOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    (pointSmallEtale (residueSeparableClosurePoint t)).fiber ≅
      (pointSmallEtale (residueSeparableClosurePoint s)).fiber :=
  Functor.isoWhiskerLeft (Etale.forget X)
    (coyoneda.mapIso (residueSeparableClosurePointIsoOfEq s t h).symm.op)

/-- **Étale neighbourhoods depend only on the underlying point.** For morphisms
`s : Spec K ⟶ X` and `t : Spec L ⟶ X` from spectra of separably closed fields with the same
underlying point, the categories of étale neighbourhoods of `t` and of `s` (the categories of
elements of the fibre functors of the points of the small étale site defined by `t` and `s`)
are isomorphic. -/
@[weil "lem_fk102_etale_neighborhoods_depend_on_point"]
def neighborhoodsIsoOfEq (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    Cat.of (pointSmallEtale t).fiber.Elements ≅ Cat.of (pointSmallEtale s).fiber.Elements :=
  (neighborhoodsIsoResidueSeparableClosure t).symm ≪≫
    Functor.elementsFunctor.mapIso (fiberIsoResidueSeparableClosurePointOfEq s t h) ≪≫
    neighborhoodsIsoResidueSeparableClosure s

/-- The isomorphism of categories of étale neighbourhoods commutes with the forgetful functors
to the small étale site. -/
@[weil "lem_fk102_etale_neighborhoods_depend_on_point"]
lemma neighborhoodsIsoOfEq_hom_toFunctor_comp_π (s : Spec (.of K) ⟶ X) (t : Spec (.of L) ⟶ X)
    (h : s default = t default) :
    (neighborhoodsIsoOfEq s t h).hom.toFunctor ⋙ CategoryOfElements.π _ =
      CategoryOfElements.π _ :=
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.GeometricPoint

open Scheme

variable {X : Scheme.{u}}

/-- **Étale neighbourhoods depend only on the underlying point.** For geometric points `x` and
`y` of `X` with the same underlying point, the categories of étale neighbourhoods of `y` and of
`x` are equivalent, compatibly with the forgetful functors to the small étale site
(`neighborhoodsEquivOfLiesOver_functor_comp_forget`). -/
@[weil "lem_fk102_etale_neighborhoods_depend_on_point"]
def neighborhoodsEquivOfLiesOver (x y : GeometricPoint X) (h : y.LiesOver (x.hom default)) :
    EtaleNeighborhood y ≌ EtaleNeighborhood x :=
  (EtaleNeighborhood.equivFiberElements y).trans
    ((Cat.equivOfIso (neighborhoodsIsoOfEq x.hom y.hom h.symm)).trans
      (EtaleNeighborhood.equivFiberElements x).symm)

/-- The equivalence of categories of étale neighbourhoods commutes with the forgetful functors
to the small étale site. -/
@[weil "lem_fk102_etale_neighborhoods_depend_on_point"]
lemma neighborhoodsEquivOfLiesOver_functor_comp_forget (x y : GeometricPoint X)
    (h : y.LiesOver (x.hom default)) :
    (neighborhoodsEquivOfLiesOver x y h).functor ⋙ EtaleNeighborhood.forget x =
      EtaleNeighborhood.forget y := by
  rw [← EtaleNeighborhood.toFiberElements_comp_π]
  rfl

end AlgebraicGeometry.GeometricPoint
