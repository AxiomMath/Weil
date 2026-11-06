/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import Weil.Attr

/-!
# The strict local ring is invariant under étale morphisms

Let `h : U ⟶ V` be an étale morphism of schemes, `u` a geometric point of `U` and `v = h ∘ u`
its image in `V`. Composing structure morphisms with `h` sends an étale neighbourhood
`(W, w)` of `u` to the étale neighbourhood `(W, w)` of `v`; this is a functor
`N(u) ⥤ N(v)` between the categories of étale neighbourhoods, and the ring of functions
`Γ(W, 𝒪_W)` is the same for `(W, w)` and its image. The functor is initial: every étale
neighbourhood `(W, w)` of `v` receives the projection from the image of the neighbourhood
`(W ×_V U, (w, u))` of `u`, and two parallel morphisms out of the image of a neighbourhood of `u`
become equal after restriction to a smaller neighbourhood, because `N(u)` is cofiltered.
Hence the colimits of the rings of functions over the two categories agree: the strict local
rings `𝒪̃_{U,u}` and `𝒪̃_{V,v}` are isomorphic, by an isomorphism compatible with the germ maps
and therefore with the structures of `Γ(V, 𝒪_V)`-algebras.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.self`: the étale neighbourhood
  `(S, s)` of a geometric point `s` of `S`.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.postcomp`: the functor
  `N(u) ⥤ N(h ∘ u)` given by composing structure morphisms with an étale morphism `h`.
* `AlgebraicGeometry.strictLocalRingIsoOfEtale`: the isomorphism `𝒪̃_{U,u} ≅ 𝒪̃_{V,h ∘ u}`.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.postcomp_initial`: the functor
  `postcomp` is initial.
* `AlgebraicGeometry.germ_comp_strictLocalRingIsoOfEtale_hom`: the isomorphism carries the germ
  at an étale neighbourhood of `u` to the germ at its image.
* `AlgebraicGeometry.exists_ringEquiv_strictLocalRing_of_etale`: the strict local rings
  `𝒪̃_{U,u}` and `𝒪̃_{V,h ∘ u}` are isomorphic as `Γ(V, 𝒪_V)`-algebras.

## Implementation notes

The `Γ(V, 𝒪_V)`-algebra structure of a strict local ring `𝒪̃_{X,x}` over a scheme `X` with a
morphism `X ⟶ V` is the pullback of functions to `X` followed by the germ at the étale
neighbourhood `(X, x)` of `x`; the main result is stated in that explicit form. The source
assumes `U` and `V` noetherian; no finiteness hypothesis is used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.7
-/

/- FK's noetherian hypothesis is dropped (generalization). "Isomorphic as Γ(V,𝒪_V)-algebras" is
stated as a ring isomorphism commuting with the two canonical maps from Γ(V,𝒪_V). -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace GeometricPoint.EtaleNeighborhood

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- The étale neighbourhood `(S, s)` of a geometric point `s` of `S`, with the identity as
structure morphism. -/
@[simps]
def self : EtaleNeighborhood s where
  scheme := S
  toBase := 𝟙 S
  point := s.hom
  point_comp := Category.comp_id _

variable {U V : Scheme.{u}} (h : U ⟶ V) [Etale h] (u : GeometricPoint U)

/-- Composing the structure morphisms of étale neighbourhoods of `u` with an étale morphism
`h : U ⟶ V` gives étale neighbourhoods of `h ∘ u`: the functor `(W, w) ↦ (W ⟶ U ⟶ V, w)`. -/
@[simps]
abbrev postcomp : EtaleNeighborhood u ⥤ EtaleNeighborhood (u.map h) where
  obj W :=
    { scheme := W.scheme
      toBase := W.toBase ≫ h
      point := W.point
      point_comp := by rw [← Category.assoc, W.point_comp]; rfl }
  map f :=
    { hom := f.hom
      over := by rw [← Category.assoc, f.over]
      point_comp := f.point_comp }

/-- The rings of functions on an étale neighbourhood of `u` and on its image in `N(h ∘ u)`
agree. -/
lemma postcomp_op_comp_functionsDiagram :
    (postcomp h u).op ⋙ functionsDiagram (u.map h) = functionsDiagram u :=
  rfl

/-- The étale neighbourhood `(W ×_V U, (w, u))` of `u` attached to an étale neighbourhood
`(W, w)` of `h ∘ u`. -/
@[simps]
abbrev pullbackNeighborhood (W : EtaleNeighborhood (u.map h)) : EtaleNeighborhood u where
  scheme := Limits.pullback W.toBase h
  toBase := Limits.pullback.snd W.toBase h
  point := Limits.pullback.lift W.point u.hom W.point_comp
  point_comp := Limits.pullback.lift_snd _ _ _

/-- The projection from the image of `(W ×_V U, (w, u))` to `(W, w)`. -/
@[simps]
abbrev pullbackNeighborhoodFst (W : EtaleNeighborhood (u.map h)) :
    (postcomp h u).obj (pullbackNeighborhood h u W) ⟶ W where
  hom := Limits.pullback.fst W.toBase h
  over := Limits.pullback.condition
  point_comp := Limits.pullback.lift_fst _ _ _

/-- A morphism from the image of an étale neighbourhood `(W', w')` of `u` to an étale
neighbourhood `(W, w)` of `h ∘ u` gives a morphism `(W', w') ⟶ (W ×_V U, (w, u))`. -/
@[simps]
abbrev toPullbackNeighborhood {W' : EtaleNeighborhood u} {W : EtaleNeighborhood (u.map h)}
    (a : (postcomp h u).obj W' ⟶ W) : W' ⟶ pullbackNeighborhood h u W where
  hom := Limits.pullback.lift (a.hom : W'.scheme ⟶ W.scheme) W'.toBase a.over
  over := Limits.pullback.lift_snd _ _ _
  point_comp := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, pullbackNeighborhood_point,
        Limits.pullback.lift_fst]
      exact a.point_comp
    · rw [Category.assoc, Limits.pullback.lift_snd, pullbackNeighborhood_point,
        Limits.pullback.lift_snd]
      exact W'.point_comp

/-- **The functor `N(u) ⥤ N(h ∘ u)` is initial.** -/
instance postcomp_initial : (postcomp h u).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun W => ⟨pullbackNeighborhood h u W, ⟨pullbackNeighborhoodFst h u W⟩⟩)
    (fun {W} {W'} a b => by
      obtain ⟨e, he⟩ : ∃ e : IsCofiltered.eq (toPullbackNeighborhood h u a)
            (toPullbackNeighborhood h u b) ⟶ W',
          e ≫ toPullbackNeighborhood h u a = e ≫ toPullbackNeighborhood h u b :=
        ⟨IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
      refine ⟨_, e, ?_⟩
      apply GeometricPoint.EtaleNeighborhood.Hom.ext
      have hab := congrArg (fun k => k.hom ≫ Limits.pullback.fst W.toBase h) he
      have ha := Limits.pullback.lift_fst (a.hom : W'.scheme ⟶ W.scheme) W'.toBase a.over
      have hb := Limits.pullback.lift_fst (b.hom : W'.scheme ⟶ W.scheme) W'.toBase b.over
      exact (congrArg (e.hom ≫ ·) ha.symm).trans ((Category.assoc _ _ _).symm.trans
        (hab.trans ((Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) hb)))))

end GeometricPoint.EtaleNeighborhood

open GeometricPoint.EtaleNeighborhood

variable (B : BigEtaleSite.{u}) {U V : Scheme.{u}} (hU : B.Contains U) (hV : B.Contains V)
  (h : U ⟶ V) [Etale h] (u : GeometricPoint U)

/-- The isomorphism of strict local rings `𝒪̃_{U,u} ≅ 𝒪̃_{V,h ∘ u}` induced by an étale
morphism `h : U ⟶ V`: both are the colimit of the rings of functions on the étale
neighbourhoods of `u`. -/
def strictLocalRingIsoOfEtale :
    strictLocalRing B U hU u ≅ strictLocalRing B V hV (u.map h) :=
  (isColimitStrictLocalRingGermCocone u B hU).coconePointUniqueUpToIso
    ((Functor.Final.isColimitWhiskerEquiv (postcomp h u).op _).symm
      (isColimitStrictLocalRingGermCocone (u.map h) B hV))

/-- The isomorphism `𝒪̃_{U,u} ≅ 𝒪̃_{V,h ∘ u}` carries the germ at an étale neighbourhood `W`
of `u` to the germ at the image of `W` in `N(h ∘ u)`. -/
@[reassoc]
theorem germ_comp_strictLocalRingIsoOfEtale_hom (W : GeometricPoint.EtaleNeighborhood u) :
    (strictLocalRingGermCocone u B hU).ι.app (op W) ≫ (strictLocalRingIsoOfEtale B hU hV h u).hom =
      (strictLocalRingGermCocone (u.map h) B hV).ι.app (op ((postcomp h u).obj W)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (op W)

/-- The isomorphism `𝒪̃_{U,u} ≅ 𝒪̃_{V,h ∘ u}` is compatible with the canonical maps from
`Γ(V, 𝒪_V)`: pulling back a function along `h` and taking its germ at `(U, u)`, then applying
the isomorphism, is taking its germ at `(V, h ∘ u)`. -/
@[reassoc]
theorem appTop_comp_germ_comp_strictLocalRingIsoOfEtale_hom :
    h.appTop ≫ ((strictLocalRingGermCocone u B hU).ι.app (op (self u)) : Γ(U, ⊤) ⟶ _) ≫
        (strictLocalRingIsoOfEtale B hU hV h u).hom =
      ((strictLocalRingGermCocone (u.map h) B hV).ι.app (op (self (u.map h))) :
        Γ(V, ⊤) ⟶ _) := by
  let f : (postcomp h u).obj (self u) ⟶ self (u.map h) :=
    { hom := h
      over := (Category.comp_id h).trans (Category.id_comp h).symm
      point_comp := rfl }
  exact (congrArg (h.appTop ≫ ·)
    (germ_comp_strictLocalRingIsoOfEtale_hom B hU hV h u (self u))).trans
    ((strictLocalRingGermCocone (u.map h) B hV).w f.op)

/-- **The strict local ring is invariant under étale morphisms.** Let `h : U ⟶ V` be an étale
morphism of schemes, `u` a geometric point of `U` and `v = h ∘ u`. Then the strict local rings
`𝒪̃_{U,u}` and `𝒪̃_{V,v}` are isomorphic as `Γ(V, 𝒪_V)`-algebras: there is a ring isomorphism
between them carrying the image of a function `a` on `V` in `𝒪̃_{U,u}` (its pullback along `h`,
followed by the germ at `(U, u)`) to the image of `a` in `𝒪̃_{V,v}` (its germ at `(V, v)`). -/
@[weil "lem_fk107_strict_local_ring_etale_invariant"]
theorem exists_ringEquiv_strictLocalRing_of_etale :
    ∃ e : strictLocalRing B U hU u ≃+* strictLocalRing B V hV (u.map h),
      ∀ a : Γ(V, ⊤),
        e ((strictLocalRingGermCocone u B hU).ι.app (op (self u)) (h.appTop a)) =
          (strictLocalRingGermCocone (u.map h) B hV).ι.app (op (self (u.map h))) a :=
  ⟨(strictLocalRingIsoOfEtale B hU hV h u).commRingCatIsoToRingEquiv, fun a =>
    congrArg (fun k => k.hom a) (appTop_comp_germ_comp_strictLocalRingIsoOfEtale_hom B hU hV h u)⟩

end AlgebraicGeometry
