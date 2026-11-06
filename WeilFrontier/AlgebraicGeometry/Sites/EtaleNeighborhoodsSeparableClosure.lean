module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# Étale neighbourhoods and the separable closure of the residue field

Let `s : Spec K ⟶ X` be a morphism from the spectrum of a separably closed field `K`, with
underlying point `x₀` and residue field embedding `φ : κ(x₀) ⟶ K`. Let `k' ⊆ K` be the separable
closure of `κ(x₀)` in `K`, `j : Spec K ⟶ Spec k'` the induced morphism and
`s' : Spec k' ⟶ X` the morphism given by `x₀` and `κ(x₀) ⟶ k'`, so that `s = j ≫ s'`.
Then `k'` is separably closed, and precomposition with `j` identifies the category of étale
neighbourhoods of `s'` with that of `s`: the induced functor is an isomorphism of categories,
commuting with the forgetful functors to the small étale site.

The key input is that the residue field extensions of an étale morphism are separable, so that
any lift `Spec K ⟶ U` of `s` to an étale `X`-scheme `U` has its residue field embedding with
image in `k'`; and that a morphism `Spec k' ⟶ U` is determined by its composite with `j`, since
`k' ⟶ K` is injective.

## Main definitions

* `AlgebraicGeometry.Scheme.residueSeparableClosure`: the separable closure `k'` of the residue
  field of the underlying point of `s` in `K`.
* `AlgebraicGeometry.Scheme.toResidueSeparableClosure`: the morphism `j : Spec K ⟶ Spec k'`.
* `AlgebraicGeometry.Scheme.residueSeparableClosurePoint`: the morphism `s' : Spec k' ⟶ X`.
* `AlgebraicGeometry.Scheme.fiberIsoResidueSeparableClosure`: precomposition with `j` as an
  isomorphism of the fibre functors `U ↦ Hom_X(Spec k', U)` and `U ↦ Hom_X(Spec K, U)`.
* `AlgebraicGeometry.Scheme.neighborhoodsIsoResidueSeparableClosure`: the induced isomorphism
  of categories `(U, u') ↦ (U, j ≫ u')` between the étale neighbourhoods of `s'` and of `s`.
* `AlgebraicGeometry.GeometricPoint.neighborhoodsEquivResidueSeparableClosure`: for a geometric
  point, the resulting equivalence with `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood`.

## Main results

* `AlgebraicGeometry.Scheme.toResidueSeparableClosure_comp_residueSeparableClosurePoint`:
  `s = j ≫ s'`.
* `AlgebraicGeometry.Scheme.isSepClosed_residueSeparableClosure`: `k'` is separably closed.
* `AlgebraicGeometry.Scheme.bijective_comp_toResidueSeparableClosure`: lifts of `s'` and of `s`
  to an étale `X`-scheme correspond bijectively under precomposition with `j`.
* `AlgebraicGeometry.Scheme.neighborhoodsIsoResidueSeparableClosure_hom_toFunctor_comp_π`: the
  isomorphism of categories commutes with the forgetful functors to `X.Etale`.

## Implementation notes

The category of étale neighbourhoods of a morphism `s : Spec K ⟶ X` from a separably closed
field is the category of elements of the fibre functor of the point
`AlgebraicGeometry.Scheme.pointSmallEtale s` of the small étale site; for an algebraically
closed `K` it is equivalent to `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood` by
`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.equivFiberElements`. The field `k'` is in
general only separably closed, so the statement is made for points with separably closed
fields, which contains the case of an algebraically closed `K`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

/- FK's `N(x)` is stated as the category of
elements of `(Scheme.pointSmallEtale s).fiber` (Mathlib's étale point), because `k'` is only
separably closed and StacksFrontier's `GeometricPoint` requires an algebraically closed field. The
bridge to `GeometricPoint.EtaleNeighborhood` is `equivFiberElements` (for `K` algebraically
closed), recorded in `GeometricPoint.neighborhoodsEquivResidueSeparableClosure`. -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {K : Type u} [Field K]

/-- Morphisms from the spectrum of a field are determined by their composite with the morphism
of spectra induced by a field embedding. -/
lemma Spec_map_comp_injective {L : Type u} [Field L] (ι : CommRingCat.of L ⟶ CommRingCat.of K)
    {U : Scheme.{u}} : Function.Injective (fun g : Spec (.of L) ⟶ U => Spec.map ι ≫ g) := by
  intro g₁ g₂ h
  obtain ⟨⟨y₁, a₁⟩, rfl⟩ := (U.SpecToEquivOfField L).symm.surjective g₁
  obtain ⟨⟨y₂, a₂⟩, rfl⟩ := (U.SpecToEquivOfField L).symm.surjective g₂
  have key (y : U) (a : U.residueField y ⟶ .of L) :
      Spec.map ι ≫ (U.SpecToEquivOfField L).symm ⟨y, a⟩ =
        (U.SpecToEquivOfField K).symm ⟨y, a ≫ ι⟩ := by
    simp [Spec.map_comp]
  simp only [key] at h
  obtain ⟨e, he⟩ := SpecToEquivOfField_eq_iff.mp ((U.SpecToEquivOfField K).symm.injective h)
  congr 1
  rw [SpecToEquivOfField_eq_iff]
  refine ⟨e, ?_⟩
  ext a
  apply ι.hom.injective
  exact congr($(he).hom a)

variable (s : Spec (.of K) ⟶ X)

/-- The separable closure in `K` of the residue field of the underlying point of a morphism
`s : Spec K ⟶ X`, embedded in `K` by `s`. -/
def residueSeparableClosure : Subfield K :=
  letI := (X.SpecToEquivOfField K s).2.hom.toAlgebra
  (separableClosure (X.residueField (X.SpecToEquivOfField K s).1) K).toSubfield

lemma mem_residueSeparableClosure_iff (a : K) :
    a ∈ residueSeparableClosure s ↔
      letI := (X.SpecToEquivOfField K s).2.hom.toAlgebra
      IsSeparable (X.residueField (X.SpecToEquivOfField K s).1) a :=
  Iff.rfl

lemma residueFieldHom_mem_residueSeparableClosure
    (a : X.residueField (X.SpecToEquivOfField K s).1) :
    (X.SpecToEquivOfField K s).2 a ∈ residueSeparableClosure s := by
  let _ := (X.SpecToEquivOfField K s).2.hom.toAlgebra
  exact isSeparable_algebraMap (F := X.residueField (X.SpecToEquivOfField K s).1) (K := K) a

/-- The separable closure of the residue field in a separably closed field is separably
closed. -/
@[weil "lem_fk102_etale_neighborhoods_separable_closure"]
instance isSepClosed_residueSeparableClosure [IsSepClosed K] :
    IsSepClosed (residueSeparableClosure s) := by
  let _ := (X.SpecToEquivOfField K s).2.hom.toAlgebra
  exact (separableClosure.isSepClosure (X.residueField (X.SpecToEquivOfField K s).1) K).sep_closed

/-- The morphism `j : Spec K ⟶ Spec k'` induced by the inclusion of the separable closure
`k'` of the residue field. -/
def toResidueSeparableClosure :
    Spec (.of K) ⟶ Spec (.of (residueSeparableClosure s)) :=
  Spec.map (CommRingCat.ofHom (residueSeparableClosure s).subtype)

/-- The embedding of the residue field of the underlying point into its separable closure
`k'`. -/
def residueFieldToResidueSeparableClosure :
    X.residueField (X.SpecToEquivOfField K s).1 ⟶ CommRingCat.of (residueSeparableClosure s) :=
  CommRingCat.ofHom ((X.SpecToEquivOfField K s).2.hom.codRestrict _
    (residueFieldHom_mem_residueSeparableClosure s))

/-- The morphism `s' : Spec k' ⟶ X` given by the underlying point of `s` and the embedding of
its residue field into the separable closure `k'`. -/
def residueSeparableClosurePoint : Spec (.of (residueSeparableClosure s)) ⟶ X :=
  (X.SpecToEquivOfField _).symm
    ⟨(X.SpecToEquivOfField K s).1, residueFieldToResidueSeparableClosure s⟩

@[reassoc (attr := simp), weil "lem_fk102_etale_neighborhoods_separable_closure"]
lemma toResidueSeparableClosure_comp_residueSeparableClosurePoint :
    toResidueSeparableClosure s ≫ residueSeparableClosurePoint s = s := by
  conv_rhs => rw [← (X.SpecToEquivOfField K).symm_apply_apply s]
  simp only [toResidueSeparableClosure, residueSeparableClosurePoint,
    SpecToEquivOfField_symm_apply, ← Spec.map_comp_assoc]
  congr 2

/-- Precomposition with `j` is injective on morphisms out of `Spec k'`. -/
lemma toResidueSeparableClosure_comp_injective {U : Scheme.{u}} :
    Function.Injective (fun g : Spec (.of (residueSeparableClosure s)) ⟶ U =>
      toResidueSeparableClosure s ≫ g) :=
  Spec_map_comp_injective _

/-- The image of a residue field embedding of a point of an étale `X`-scheme lying over `s`
consists of separable elements. -/
lemma isSeparable_of_etale {U : Scheme.{u}} (f : U ⟶ X) [Etale f] (y : U) (x₀ : X)
    (φ : X.residueField x₀ ⟶ .of K) (b : U.residueField y ⟶ .of K)
    (h : (⟨f y, f.residueFieldMap y ≫ b⟩ : Σ x, X.residueField x ⟶ .of K) = ⟨x₀, φ⟩)
    (a : U.residueField y) :
    letI := φ.hom.toAlgebra
    IsSeparable (X.residueField x₀) (b a) := by
  cases h
  algebraize [(f.residueFieldMap y).hom]
  let _ := (f.residueFieldMap y ≫ b).hom.toAlgebra
  let b' : U.residueField y →ₐ[X.residueField (f y)] K :=
    { b.hom with commutes' := fun _ => rfl }
  exact IsSeparable.map b' b.hom.injective (Algebra.IsSeparable.isSeparable _ a)

/-- **Lifts to étale schemes.** For an étale `X`-scheme `U`, precomposition with `j` is a
bijection from the lifts `Spec k' ⟶ U` of `s'` to the lifts `Spec K ⟶ U` of `s`. -/
theorem bijective_comp_toResidueSeparableClosure {U : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    Function.Bijective (fun g : {g : Spec (.of (residueSeparableClosure s)) ⟶ U //
        g ≫ f = residueSeparableClosurePoint s} =>
      (⟨toResidueSeparableClosure s ≫ g.1, by simp [g.2]⟩ :
        {h : Spec (.of K) ⟶ U // h ≫ f = s})) := by
  refine ⟨fun g₁ g₂ h => Subtype.ext (toResidueSeparableClosure_comp_injective s
    congr(($h).1)), ?_⟩
  rintro ⟨h, hh⟩
  obtain ⟨⟨y, b⟩, rfl⟩ := (U.SpecToEquivOfField K).symm.surjective h
  have hs : X.SpecToEquivOfField K s = ⟨f y, f.residueFieldMap y ≫ b⟩ := by
    rw [← hh]
    apply (X.SpecToEquivOfField K).symm.injective
    simp [Spec.map_comp]
  have hmem : ∀ a, b a ∈ residueSeparableClosure s := by
    intro a
    rw [mem_residueSeparableClosure_iff]
    exact isSeparable_of_etale f y _ _ b hs.symm a
  let b' : U.residueField y ⟶ .of (residueSeparableClosure s) :=
    CommRingCat.ofHom (b.hom.codRestrict _ hmem)
  have hj : toResidueSeparableClosure s ≫ (U.SpecToEquivOfField _).symm ⟨y, b'⟩ =
      (U.SpecToEquivOfField K).symm ⟨y, b⟩ := by
    simp only [toResidueSeparableClosure, SpecToEquivOfField_symm_apply, ← Spec.map_comp_assoc]
    rfl
  refine ⟨⟨(U.SpecToEquivOfField _).symm ⟨y, b'⟩, ?_⟩, Subtype.ext hj⟩
  apply toResidueSeparableClosure_comp_injective s
  simp only
  rw [reassoc_of% hj, hh, toResidueSeparableClosure_comp_residueSeparableClosurePoint]

/-- The morphism `Over.mk s ⟶ Over.mk s'` over `X` given by `j`. -/
def overHomToResidueSeparableClosure :
    Over.mk s ⟶ Over.mk (residueSeparableClosurePoint s) :=
  Over.homMk (toResidueSeparableClosure s)
    (toResidueSeparableClosure_comp_residueSeparableClosurePoint s)

/-- Precomposition with `j`, from lifts of `s'` to lifts of `s`, as a morphism of the fibre
functors `U ↦ Hom_X(Spec k', U)` and `U ↦ Hom_X(Spec K, U)` on the small étale site. -/
def fiberMapResidueSeparableClosure :
    Etale.forget X ⋙ coyoneda.obj (op (Over.mk (residueSeparableClosurePoint s))) ⟶
      Etale.forget X ⋙ coyoneda.obj (op (Over.mk s)) :=
  Functor.whiskerLeft (Etale.forget X) (coyoneda.map (overHomToResidueSeparableClosure s).op)

lemma fiberMapResidueSeparableClosure_app_apply (U : X.Etale)
    (g : Over.mk (residueSeparableClosurePoint s) ⟶ (Etale.forget X).obj U) :
    (fiberMapResidueSeparableClosure s).app U g = overHomToResidueSeparableClosure s ≫ g :=
  rfl

instance isIso_fiberMapResidueSeparableClosure : IsIso (fiberMapResidueSeparableClosure s) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  have : Etale U.hom := U.prop
  rw [isIso_iff_bijective]
  have hb := bijective_comp_toResidueSeparableClosure s U.hom
  refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
  · exact Over.OverMorphism.ext (toResidueSeparableClosure_comp_injective s congr(($h).left))
  · obtain ⟨⟨g', hg'⟩, hg⟩ := hb.2 ⟨g.left, Over.w g⟩
    exact ⟨Over.homMk g' hg', Over.OverMorphism.ext congr(($hg).1)⟩

/-- Precomposition with `j` as an isomorphism of fibre functors. -/
def fiberIsoResidueSeparableClosure :
    Etale.forget X ⋙ coyoneda.obj (op (Over.mk (residueSeparableClosurePoint s))) ≅
      Etale.forget X ⋙ coyoneda.obj (op (Over.mk s)) :=
  asIso (fiberMapResidueSeparableClosure s)

variable [IsSepClosed K]

/-- **Étale neighbourhoods and the separable closure of the residue field.** The functor
`(U, u') ↦ (U, j ≫ u')` from the étale neighbourhoods of `s' : Spec k' ⟶ X` to those of
`s : Spec K ⟶ X` (the categories of elements of the fibre functors of the points of the small
étale site defined by `s'` and by `s`), as an isomorphism of categories. -/
@[weil "lem_fk102_etale_neighborhoods_separable_closure"]
def neighborhoodsIsoResidueSeparableClosure :
    Cat.of (pointSmallEtale (residueSeparableClosurePoint s)).fiber.Elements ≅
      Cat.of (pointSmallEtale s).fiber.Elements :=
  Functor.elementsFunctor.mapIso (fiberIsoResidueSeparableClosure s)

/-- The isomorphism of categories of étale neighbourhoods is `(U, u') ↦ (U, j ≫ u')`. -/
lemma neighborhoodsIsoResidueSeparableClosure_hom_toFunctor_obj
    (V : (pointSmallEtale (residueSeparableClosurePoint s)).fiber.Elements) :
    (neighborhoodsIsoResidueSeparableClosure s).hom.toFunctor.obj V =
      ⟨V.1, overHomToResidueSeparableClosure s ≫ V.2⟩ :=
  rfl

/-- The isomorphism of categories of étale neighbourhoods is the identity on underlying
morphisms of étale `X`-schemes. -/
lemma neighborhoodsIsoResidueSeparableClosure_hom_toFunctor_map
    {V W : (pointSmallEtale (residueSeparableClosurePoint s)).fiber.Elements} (h : V ⟶ W) :
    ((neighborhoodsIsoResidueSeparableClosure s).hom.toFunctor.map h).1 = h.1 :=
  rfl

/-- The isomorphism of categories of étale neighbourhoods commutes with the forgetful functors
to the small étale site. -/
@[weil "lem_fk102_etale_neighborhoods_separable_closure"]
lemma neighborhoodsIsoResidueSeparableClosure_hom_toFunctor_comp_π :
    (neighborhoodsIsoResidueSeparableClosure s).hom.toFunctor ⋙ CategoryOfElements.π _ =
      CategoryOfElements.π _ :=
  rfl

/-- The inverse isomorphism of categories of étale neighbourhoods commutes with the forgetful
functors to the small étale site. -/
lemma neighborhoodsIsoResidueSeparableClosure_inv_toFunctor_comp_π :
    (neighborhoodsIsoResidueSeparableClosure s).inv.toFunctor ⋙ CategoryOfElements.π _ =
      CategoryOfElements.π _ :=
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.GeometricPoint

open Scheme

variable {X : Scheme.{u}} (x : GeometricPoint X)

/-- For a geometric point `x` (with algebraically closed field), the étale neighbourhoods of
`x` are equivalent to those of `x' : Spec k' ⟶ X`, `k'` the separable closure of the residue
field of the underlying point; the equivalence commutes with the forgetful functors to the small
étale site (`neighborhoodsEquivResidueSeparableClosure_functor_comp_π`). -/
def neighborhoodsEquivResidueSeparableClosure :
    EtaleNeighborhood x ≌
      (pointSmallEtale (residueSeparableClosurePoint x.hom)).fiber.Elements :=
  (EtaleNeighborhood.equivFiberElements x).trans
    (Cat.equivOfIso (neighborhoodsIsoResidueSeparableClosure x.hom).symm)

lemma neighborhoodsEquivResidueSeparableClosure_functor_comp_π :
    (neighborhoodsEquivResidueSeparableClosure x).functor ⋙ CategoryOfElements.π _ =
      EtaleNeighborhood.forget x := by
  rw [← EtaleNeighborhood.toFiberElements_comp_π]
  rfl

end AlgebraicGeometry.GeometricPoint
