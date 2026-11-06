module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.GeometricPointComparison
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import WeilFrontier.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.BoundedSmallEtaleStandardCofinal
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Stalk tests on the bounded small étale site

Let `B` be a big étale site containing a scheme `S`, and `SmallEtale B S hS` the bounded small
étale site of `S` [Stacks, Tag 021B], with stalks taken at the points
`AlgebraicGeometry.geometricPointSitePoint B S hS s` of geometric points `s` of `S` (over
algebraically closed fields). This file states on that site the stalk tests proved on Mathlib's
small étale site `S.smallEtaleTopology`:

* a map of sheaves of sets is an epimorphism, equivalently locally surjective, exactly when it
  is surjective on the stalk at every geometric point;
* the stalk maps of the sheafification morphism of a presheaf are bijective;
* the germs of two sections at a lift of a geometric point agree iff the sections agree on an
  open subscheme around the image point, given as an object of the site.

## Main results

* `AlgebraicGeometry.GeometricPoint.epi_iff_forall_surjective_geometricPointSitePoint_sheafFiber`:
  a map of sheaves of sets on `SmallEtale B S hS` is an epimorphism iff it is surjective on all
  stalks at geometric points.
* `AlgebraicGeometry.GeometricPoint.forall_exists_mem_range_iff_forall_surjective_sheafFiber`:
  local surjectivity, tested by covering families, iff surjectivity on all stalks.
* `AlgebraicGeometry.Scheme.bijective_geometricPointSitePoint_presheafFiber_map_toSheafify`:
  the stalk maps of the sheafification morphism are bijective.
* `AlgebraicGeometry.Scheme.geometricPointSitePoint_toPresheafFiber_eq_iff_exists_isOpenImmersion`:
  germs agree iff the sections agree near the point.

## Implementation notes

The epimorphism test is transported from
`AlgebraicGeometry.GeometricPoint.exists_surjective_etale_iff_forall_surjective_stalkFunctor`
along the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` and the stalk comparison
`AlgebraicGeometry.SmallEtale.sheafEquivFunctorCompSheafFiberIso`. On Mathlib's site local
surjectivity is tested by a single surjective étale map, the disjoint union of a covering
family; on the bounded site only countable disjoint unions are known to stay below the size
cutoff, so local surjectivity is stated there with covering families, jointly surjective on
points.

The bijectivity of the stalk maps of the sheafification morphism is a statement about
presheaves, which do not move along `AlgebraicGeometry.SmallEtale.sheafEquiv`; it holds on the
bounded site for the same reason as on Mathlib's, the fiber functor of a point inverting the
morphisms of `J.W`.

An open subscheme of an object of `SmallEtale B S hS` need not be below the size cutoff unless
it is quasi-compact, so on the bounded site "agree on a Zariski open neighbourhood" reads "agree
on an object of the site mapping to `U` by an open immersion whose image contains the point";
the neighbourhood produced is an affine open. The argument is the one on Mathlib's site: the
image of an étale neighbourhood on which the sections agree is open, and an affine open around
the point inside it is covered by the pullback of the neighbourhood.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2–I.4.
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' v' u' u

namespace AlgebraicGeometry

/-- Surjectivity of the maps induced by a morphism under two isomorphic functors to types. -/
private lemma surjective_map_iff_of_iso {C : Type u'} [Category.{v'} C] {P Q : C ⥤ Type w'}
    (e : P ≅ Q) {X Y : C} (f : X ⟶ Y) :
    Function.Surjective (P.map f) ↔ Function.Surjective (Q.map f) := by
  have key : ∀ {P Q : C ⥤ Type w'} (e : P ≅ Q),
      Function.Surjective (P.map f) → Function.Surjective (Q.map f) := by
    intro P Q e h
    rw [← NatIso.naturality_1 e f]
    exact ((isIso_iff_bijective (e.hom.app Y)).1 inferInstance).2.comp
      (h.comp ((isIso_iff_bijective (e.inv.app X)).1 inferInstance).2)
  exact ⟨key e, key e.symm⟩

/-- A point of a scheme étale over `S` lies in an affine open which is an object of
`SmallEtale B S hS`, mapping into the scheme by an open immersion over `S`. This is
`AlgebraicGeometry.exists_smallEtale_affine_open_of_etale` of StacksFrontier, restated here with
the same proof. -/
private lemma exists_smallEtale_affine_open_of_etale' (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y : Scheme.{u}} (g : Y ⟶ S) [Etale g] (y : Y) :
    ∃ (V : SmallEtale B S hS) (j : (SmallEtale.toScheme B S hS).obj V ⟶ Y),
      IsOpenImmersion j ∧ B.inclusion.map V.obj.hom = j ≫ g ∧ y ∈ Set.range j.base := by
  obtain ⟨R, j, hjopen, hy, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := y) (U := ⊤) (by simp)
  have hjg : Etale (j ≫ g) := inferInstance
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ g)).trans_lt hS
  exact ⟨⟨Over.mk (ObjectProperty.homMk (j ≫ g) : B.obj (Spec R) hR ⟶ B.obj S hS), hjg⟩, j,
    hjopen, rfl, hy⟩

namespace GeometricPoint

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Transport of
`AlgebraicGeometry.GeometricPoint.exists_surjective_etale_iff_forall_surjective_stalkFunctor`:
a map of sheaves of sets on the bounded small étale site is an epimorphism iff it is surjective
on the stalk at every geometric point. -/
theorem epi_iff_forall_surjective_geometricPointSitePoint_sheafFiber
    {F G : Sheaf (SmallEtale.topology B S hS) (Type u)} (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : GeometricPoint S,
      Function.Surjective ((geometricPointSitePoint B S hS x).sheafFiber.map φ) := by
  let E := SmallEtale.sheafEquiv B S hS (Type u)
  rw [← E.functor.epi_map_iff_epi, ← Sheaf.isLocallySurjective_iff_epi,
    Scheme.Sheaf.isLocallySurjective_iff_exists_surjective,
    exists_surjective_etale_iff_forall_surjective_stalkFunctor]
  exact forall_congr' fun x =>
    (surjective_map_iff_of_iso (SmallEtale.sheafEquivFunctorCompSheafFiberIso B S hS (Type u) x)
      φ)

/-- Transport of
`AlgebraicGeometry.GeometricPoint.exists_surjective_etale_iff_forall_surjective_stalkFunctor`:
for a map `φ : F ⟶ G` of sheaves of sets on the bounded small étale site, every section of `G`
is locally, on a family of objects covering a neighbourhood of each point, in the image of `φ`
iff `φ` is surjective on the stalk at every geometric point. -/
@[weil "lem_fk104_locally_surjective_iff_stalks_surjective"]
theorem forall_exists_mem_range_iff_forall_surjective_sheafFiber
    {F G : Sheaf (SmallEtale.topology B S hS) (Type u)} (φ : F ⟶ G) :
    (∀ (U : SmallEtale B S hS) (s : G.obj.obj (op U)) (y : (SmallEtale.toScheme B S hS).obj U),
        ∃ (V : SmallEtale B S hS) (h : V ⟶ U), y ∈ Set.range ((SmallEtale.toScheme B S hS).map h)
          ∧ ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map h.op s) ↔
      ∀ x : GeometricPoint S,
        Function.Surjective ((geometricPointSitePoint B S hS x).sheafFiber.map φ) := by
  rw [← epi_iff_forall_surjective_geometricPointSitePoint_sheafFiber,
    ← Sheaf.isLocallySurjective_iff_epi]
  constructor
  · intro h
    refine ⟨fun {U} s => SmallEtale.mem_topology_of_jointlySurjective fun y => ?_⟩
    obtain ⟨V, g, hy, t, ht⟩ := h U s y
    exact ⟨V, g, ⟨t, ht⟩, hy⟩
  · intro h U s y
    obtain ⟨V, g, ⟨t, ht⟩, hy⟩ :=
      SmallEtale.exists_mem_arrows_mem_range B S hS (Presheaf.imageSieve_mem _ φ.hom s) y
    exact ⟨V, g, hy, t, ht⟩

end GeometricPoint

namespace Scheme

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The bounded-site form of
`AlgebraicGeometry.Scheme.bijective_pointSmallEtale_presheafFiber_map_toSheafify`: the map on
stalks at a geometric point induced by the sheafification morphism of a presheaf on
`SmallEtale B S hS` is bijective. -/
@[weil "lem_fk102_sheafification_stalks"]
theorem bijective_geometricPointSitePoint_presheafFiber_map_toSheafify
    {A : Type*} [Category A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [HasWeakSheafify (SmallEtale.topology B S hS) A] (x : GeometricPoint S)
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    Function.Bijective
      (ConcreteCategory.hom ((geometricPointSitePoint B S hS x).presheafFiber.map
        (toSheafify (SmallEtale.topology B S hS) F))) :=
  ConcreteCategory.bijective_of_isIso _

/-- The bounded-site form of
`AlgebraicGeometry.Scheme.bijective_pointSmallEtale_presheafFiber_map_toSheafify_type`. -/
theorem bijective_geometricPointSitePoint_presheafFiber_map_toSheafify_type
    (x : GeometricPoint S) (F : (SmallEtale B S hS)ᵒᵖ ⥤ Type u) :
    Function.Bijective
      ((geometricPointSitePoint B S hS x).presheafFiber.map
        (toSheafify (SmallEtale.topology B S hS) F)) :=
  (isIso_iff_bijective _).1 inferInstance

/-- The bounded-site form of
`AlgebraicGeometry.Scheme.bijective_pointSmallEtale_presheafFiber_map_toSheafify_addCommGrp`. -/
theorem bijective_geometricPointSitePoint_presheafFiber_map_toSheafify_addCommGrp
    (x : GeometricPoint S) (F : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Function.Bijective
      ((geometricPointSitePoint B S hS x).presheafFiber.map
        (toSheafify (SmallEtale.topology B S hS) F)) :=
  bijective_geometricPointSitePoint_presheafFiber_map_toSheafify B S hS x F

section Germs

variable {A : Type u'} [Category.{v'} A] {FC : A → A → Type*}
  {CC : A → Type w'} [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w'} A FC]
  [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- The bounded-site form of `AlgebraicGeometry.Scheme.toPresheafFiber_eq_iff_exists_opens`:
for a sheaf `F` on `SmallEtale B S hS`, sections `α β ∈ F(U)` and a lift `ū` of a geometric
point to `U`, the germs of `α` and `β` at `ū` agree iff `α` and `β` agree on an object of the
site mapping to `U` by an open immersion whose image contains the image point of `ū`. -/
@[weil "lem_fk103_germs_equal_iff_equal_near_point"]
theorem geometricPointSitePoint_toPresheafFiber_eq_iff_exists_isOpenImmersion
    [(SmallEtale.topology B S hS).HasSheafCompose (CategoryTheory.forget A)]
    (F : Sheaf (SmallEtale.topology B S hS) A) (U : SmallEtale B S hS)
    (α β : ToType (F.obj.obj (op U))) (x : GeometricPoint S)
    (ū : (geometricPointSitePoint B S hS x).fiber.obj U) :
    (geometricPointSitePoint B S hS x).toPresheafFiber U ū F.obj α =
        (geometricPointSitePoint B S hS x).toPresheafFiber U ū F.obj β ↔
      ∃ (V : SmallEtale B S hS) (j : V ⟶ U),
        IsOpenImmersion ((SmallEtale.toScheme B S hS).map j) ∧
          ū.1 (default : x.source) ∈ Set.range ((SmallEtale.toScheme B S hS).map j) ∧
          F.obj.map j.op α = F.obj.map j.op β := by
  rw [GrothendieckTopology.Point.toPresheafFiber_eq_iff']
  constructor
  · rintro ⟨V, f, y, hy, hf⟩
    let f₀ := (SmallEtale.toScheme B S hS).map f
    have : Etale f₀ := inferInstance
    have : Flat f₀ := inferInstance
    have : LocallyOfFinitePresentation f₀ := inferInstance
    have : UniversallyOpen f₀ := UniversallyOpen.of_flat f₀
    let W : ((SmallEtale.toScheme B S hS).obj U).Opens :=
      ⟨Set.range f₀, f₀.isOpenMap.isOpen_range⟩
    have hyū : y.1 ≫ f₀ = ū.1 := congrArg Subtype.val hy
    have hpt : ū.1 (default : x.source) ∈ W := ⟨y.1 default, by rw [← hyū]; rfl⟩
    obtain ⟨V', j₀, hj₀, hstr, hv⟩ := exists_smallEtale_affine_open_of_etale' B S hS
      (W.ι ≫ B.inclusion.map U.obj.hom) ⟨_, hpt⟩
    let j : V' ⟶ U := SmallEtale.homMk B S hS (j₀ ≫ W.ι) (by
      rw [Category.assoc]; exact hstr.symm)
    have hj : (SmallEtale.toScheme B S hS).map j = j₀ ≫ W.ι := rfl
    refine ⟨V', j, by rw [hj]; infer_instance, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := hv
      exact ⟨v, by rw [hj, Scheme.Hom.comp_apply, hv]; rfl⟩
    · -- `α` and `β` agree on the sieve of maps to `V'` factoring through `f` over `U`.
      let R : Sieve V' :=
        { arrows := fun T g => ∃ h : T ⟶ V, h ≫ f = g ≫ j
          downward_closed := by
            rintro T T' g ⟨h, hh⟩ e
            exact ⟨e ≫ h, by rw [Category.assoc, hh, Category.assoc]⟩ }
      have hR : R ∈ SmallEtale.topology B S hS V' := by
        refine SmallEtale.mem_topology_of_jointlySurjective fun v => ?_
        obtain ⟨t, ht⟩ : ((SmallEtale.toScheme B S hS).map j) v ∈ Set.range f₀ :=
          (j₀ v).2
        obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback v t ht.symm
        obtain ⟨T, k, -, hk, hpk⟩ := exists_smallEtale_affine_open_of_etale' B S hS
          (Limits.pullback.fst ((SmallEtale.toScheme B S hS).map j) f₀ ≫
            B.inclusion.map V'.obj.hom) p
        let g : T ⟶ V' := SmallEtale.homMk B S hS (k ≫ Limits.pullback.fst _ _) (by
          rw [Category.assoc]; exact hk.symm)
        let h : T ⟶ V := SmallEtale.homMk B S hS (k ≫ Limits.pullback.snd _ _) (by
          change (k ≫ Limits.pullback.snd _ _) ≫ B.inclusion.map V.obj.hom =
            B.inclusion.map T.obj.hom
          rw [hk, ← SmallEtale.toScheme_map_comp B S hS j, ← Category.assoc
            (Limits.pullback.fst _ _), Limits.pullback.condition,
            ← SmallEtale.toScheme_map_comp B S hS f]
          simp only [Category.assoc]
          rfl)
        refine ⟨T, g, ⟨h, (SmallEtale.toScheme B S hS).map_injective ?_⟩, ?_⟩
        · simp only [Functor.map_comp]
          change (k ≫ Limits.pullback.snd _ _) ≫ f₀ =
            (k ≫ Limits.pullback.fst _ _) ≫ (SmallEtale.toScheme B S hS).map j
          rw [Category.assoc, Category.assoc, Limits.pullback.condition]
        · obtain ⟨q, hq⟩ := hpk
          exact ⟨q, by
            change (k ≫ Limits.pullback.fst _ _) q = v
            rw [Scheme.Hom.comp_apply, hq, hp₁]⟩
      let G := F.obj ⋙ CategoryTheory.forget A
      have hG : Presieve.IsSheaf (SmallEtale.topology B S hS) G :=
        (isSheaf_iff_isSheaf_of_type _ _).1
          ((sheafCompose _ (CategoryTheory.forget A)).obj F).property
      refine (hG _ hR).isSeparatedFor.ext fun T g hg => ?_
      obtain ⟨h, hh⟩ := hg
      change G.map g.op (G.map j.op α) = G.map g.op (G.map j.op β)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← hh, op_comp,
        Functor.map_comp_apply, Functor.map_comp_apply]
      exact congrArg _ hf
  · rintro ⟨V, j, hj, ⟨v, hv⟩, h⟩
    have hsub : Set.range ū.1 ⊆ Set.range ((SmallEtale.toScheme B S hS).map j) := by
      rintro _ ⟨a, rfl⟩
      obtain rfl : a = (default : x.source) := Subsingleton.elim (α := x.source) _ _
      exact ⟨v, hv⟩
    let l := IsOpenImmersion.lift ((SmallEtale.toScheme B S hS).map j) ū.1 hsub
    have hl : l ≫ (SmallEtale.toScheme B S hS).map j = ū.1 := IsOpenImmersion.lift_fac _ _ _
    let y : (geometricPointSitePoint B S hS x).fiber.obj V := ⟨l, by
      rw [← SmallEtale.toScheme_map_comp B S hS j, ← Category.assoc, hl]
      exact ū.2⟩
    exact ⟨V, j, y, Subtype.ext hl, h⟩

end Germs

end Scheme

end AlgebraicGeometry
