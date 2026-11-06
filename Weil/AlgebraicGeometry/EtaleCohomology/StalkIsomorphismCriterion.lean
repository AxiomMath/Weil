module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# A morphism of étale sheaves is an isomorphism iff it is bijective on all stalks

Let `X` be a scheme. A morphism `φ : F ⟶ G` of sheaves of sets, or of abelian groups, on the
small étale site of `X` is an isomorphism if and only if the induced map `φₓ : Fₓ ⟶ Gₓ` on the
stalk at every geometric point `x` of `X` is bijective. One direction is functoriality of the
stalk; the other holds because the geometric points of `X` form a conservative family of points
of the small étale site, which is Stacks, Tag 03PU.

## Main results

* `AlgebraicGeometry.isIso_iff_forall_bijective_geometricPointSitePoint_sheafFiber` — the
  criterion for sheaves of types on the small étale site `SmallEtale B X hX` of a big étale site,
  with stalks at all geometric points of `X`.
* `AlgebraicGeometry.isIso_iff_forall_bijective_etaleStalkPresheafFunctor_map` — the same for
  sheaves of abelian groups.
* `AlgebraicGeometry.Scheme.isIso_iff_forall_bijective_pointSmallEtale_sheafFiber` — the
  criterion for sheaves of types on `X.smallEtaleTopology`, with stalks at all geometric points
  `Spec Ω ⟶ X` with `Ω` separably closed.

## Implementation notes

On `SmallEtale B X hX` a geometric point has an algebraically closed field (Stacks, Tag 03PO).
The criterion on `X.smallEtaleTopology` quantifies over separably closed fields, as in the
source; its converse direction only uses the separable closures of the residue fields.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FK]
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- A morphism of sheaves of types on the small étale site of `X` is an isomorphism if and only
if it is bijective on the stalk at every geometric point of `X`. -/
@[weil "lem_fk102_iso_iff_stalkwise_iso"]
theorem isIso_iff_forall_bijective_geometricPointSitePoint_sheafFiber
    {F G : Sheaf (SmallEtale.topology B X hX) (Type u)} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : GeometricPoint X, Function.Bijective
      (((geometricPointSitePoint B X hX x).sheafFiber (A := Type u)).map φ) := by
  refine ⟨fun _ x => (isIso_iff_bijective _).1 inferInstance, fun h => ?_⟩
  exact isIso_of_bijective_geometricSheafFiber B X hX φ fun x => h _

/-- A morphism of sheaves of abelian groups on the small étale site of `X` is an isomorphism if
and only if it is bijective on the stalk at every geometric point of `X`. -/
@[weil "lem_fk102_iso_iff_stalkwise_iso"]
theorem isIso_iff_forall_bijective_etaleStalkPresheafFunctor_map [UnivLE.{u, v}]
    {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v}} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : GeometricPoint X, Function.Bijective
      ((etaleStalkPresheafFunctor B X hX x AddCommGrpCat.{v}).map φ.hom) := by
  refine ⟨fun _ x => ?_, fun h => ?_⟩
  · exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  · exact isIso_of_isIso_etaleStalkMap B X hX φ fun x =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h x)

/-- A morphism of sheaves of types on the small étale site `X.smallEtaleTopology` is an
isomorphism if and only if it is bijective on the stalk at every geometric point `Spec Ω ⟶ X`
with `Ω` separably closed. -/
@[weil "lem_fk102_iso_iff_stalkwise_iso"]
theorem Scheme.isIso_iff_forall_bijective_pointSmallEtale_sheafFiber
    {F G : Sheaf X.smallEtaleTopology (Type u)} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Function.Bijective (((Scheme.pointSmallEtale x).sheafFiber (A := Type u)).map φ) := by
  refine ⟨fun _ Ω _ _ x => (isIso_iff_bijective _).1 inferInstance, fun h => ?_⟩
  refine @JointlyReflectIsomorphisms.isIso _ _ _ _ _ _
    (Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectIsomorphisms_type
    _ _ φ fun Φ => ?_
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
  rw [← hx]
  exact (isIso_iff_bijective _).2 (h _ _)

end AlgebraicGeometry

end

/-! ### Isomorphisms of étale sheaves are detected at algebraically closed geometric points -/

/-!
# Isomorphisms of étale sheaves are detected at algebraically closed geometric points

Let `X` be a scheme and `φ : F ⟶ G` a morphism of sheaves of sets, or of abelian groups, on the
small étale site of `X`. If the induced map `F_x → G_x` on the stalk at every geometric point
`x : Spec k ⟶ X` with `k` algebraically closed is bijective, then `φ` is an isomorphism; the
converse holds since the stalk functor is a functor.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_iff_forall_bijective_sheafFiber`: the statement for
  sheaves of sets.
* `AlgebraicGeometry.SmallEtale.isIso_iff_forall_bijective_etaleStalkMap`: the statement for
  sheaves of abelian groups.

## Implementation notes

Geometric points (`AlgebraicGeometry.GeometricPoint`) take values in algebraically closed
fields, and the small étale site is `AlgebraicGeometry.SmallEtale` over a big étale site `B`
containing `X`. The source deduces the statement from the analogous criterion for separably
closed geometric points, by comparing the stalk at a separably closed point with the stalk at
an algebraic closure. Here the criterion is obtained directly: the geometric points of `X`
with algebraically closed fields already form a conservative family of points of the small
étale site (Stacks, Tag 03PU), so the comparison of stalks is not needed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

/- The proof reuses StacksFrontier's
`isIso_iff_forall_bijective_sheafFiber` (sets) and `isIso_of_isIso_etaleStalkMap`
(abelian groups) rather than going through FK's stalkwise criterion over separably closed
points and the invariance of stalks under passage to an algebraic closure. -/

public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

namespace SmallEtale

/-- **Isomorphisms of étale sheaves of sets are detected at geometric points.** A morphism of
sheaves of sets on the small étale site of `X` is an isomorphism if and only if the induced map
on the stalk at every geometric point of `X` (with algebraically closed field) is bijective.
This is `AlgebraicGeometry.isIso_iff_forall_bijective_sheafFiber`. -/
@[weil "lem_fk103_iso_iff_stalkwise_iso_algebraically_closed"]
theorem isIso_iff_forall_bijective_sheafFiber
    {F G : Sheaf (SmallEtale.topology B X hX) (Type u)} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ s : GeometricPoint X, Function.Bijective
      (((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).map φ) :=
  AlgebraicGeometry.isIso_iff_forall_bijective_sheafFiber B X hX φ

/-- **Isomorphisms of abelian étale sheaves are detected at geometric points.** A morphism of
sheaves of abelian groups on the small étale site of `X` is an isomorphism if and only if the
induced map on the stalk at every geometric point of `X` (with algebraically closed field) is
bijective. -/
@[weil "lem_fk103_iso_iff_stalkwise_iso_algebraically_closed"]
theorem isIso_iff_forall_bijective_etaleStalkMap [UnivLE.{u, v}]
    {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v}} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ s : GeometricPoint X, Function.Bijective
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map φ.hom) := by
  refine ⟨fun _ s => ConcreteCategory.bijective_of_isIso _, fun h => ?_⟩
  refine isIso_of_isIso_etaleStalkMap B X hX φ fun s => ?_
  exact (ConcreteCategory.isIso_iff_bijective _).2 (h s)

end SmallEtale

end AlgebraicGeometry

end

/-! ### Local surjectivity from surjectivity on stalks at a detecting set of points -/

/-!
# Local surjectivity from surjectivity on stalks at a detecting set of points

Let `X` be a scheme, `P ⊆ X` a detecting set of points and `φ : F ⟶ G` a morphism of presheaves
on the small étale site of `X` (with values in a concrete category whose forgetful functor
preserves filtered colimits, e.g. sets). If `φ` is surjective on the stalk at every geometric
point of `X` lying over a point of `P`, then `φ` is locally surjective: every section `g` of `G`
over an étale `U` is, on the members of an étale covering of `U`, the image of a section of `F`.

The proof is the following. The image sieve of `g` is a sieve on `U`; the union `E` of the
images of its members is open, since morphisms of the small étale site are étale, hence open.
At a point `u ∈ U` mapping into `P`, the germ of `g` at the geometric point over `u` is the
image of a germ of `F`, and the two agree on an étale neighbourhood of that geometric point, so
`u ∈ E`. As `P` is detecting, the closed set `U \ E` is empty, and a sieve of the small étale
site whose members are jointly surjective is covering.

## Main results

* `AlgebraicGeometry.isLocallySurjective_of_surjective_etaleStalkMap_of_isDetecting` — the
  criterion for presheaves with values in a concrete category.
* `AlgebraicGeometry.isLocallySurjective_sheaf_of_surjective_etaleStalkMap_of_isDetecting` —
  the case of sheaves of sets.

## Implementation notes

The site is the small étale site `AlgebraicGeometry.SmallEtale` of [Stacks, Tag 021B], which
contains Freitag–Kiehl's category of noetherian separated étale `X`-schemes; geometric points
are over algebraically closed fields. The conclusion "there is an étale covering `(U_j → U)` and
`f_j ∈ F(U_j)` with `φ(f_j) = g|_{U_j}`" is `CategoryTheory.Presheaf.IsLocallySurjective`: the
sieve of those `V → U` over which `g` lifts is covering. No sheaf condition on `F` or `G` is
used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' v' u' v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The geometric point attached to a point `x` of an object `V` of the small étale site lies
over the image of `x` in `X`. -/
theorem geometricPointOfEtalePoint_liesOver (V : SmallEtale B X hX)
    (x : (SmallEtale.toScheme B X hX).obj V) :
    (geometricPointOfEtalePoint B X hX V x).LiesOver ((B.inclusion.map V.obj.hom) x) := by
  change ((GeometricPoint.ofPoint _ x).hom ≫ B.inclusion.map V.obj.hom) default = _
  rw [Scheme.Hom.comp_apply]
  exact congrArg _ (GeometricPoint.ofPoint_liesOver _ x)

/-- The underlying morphism of schemes of a morphism of the small étale site is étale. -/
private theorem etale_toScheme_map_aux {U V : SmallEtale B X hX} (f : U ⟶ V) :
    Etale ((SmallEtale.toScheme B X hX).map f) := by
  have hV : Etale (B.inclusion.map V.obj.hom) := V.property
  have : Etale ((SmallEtale.toScheme B X hX).map f ≫ B.inclusion.map V.obj.hom) := by
    rw [SmallEtale.toScheme_map_comp]
    exact U.property
  exact Etale.of_comp _ (B.inclusion.map V.obj.hom)

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]
  [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (forget A)]

variable {B X hX}

/-- At a point `x` of `V` whose geometric point has surjective stalk map, a section `b` of `G`
over `V` lifts on some morphism of the site whose image contains `x`. -/
theorem exists_imageSieve_mem_range_of_surjective_etaleStalkMap
    {F G : (SmallEtale B X hX)ᵒᵖ ⥤ A} (α : F ⟶ G) (V : SmallEtale B X hX)
    (b : ToType (G.obj (op V))) (x : (SmallEtale.toScheme B X hX).obj V)
    (h : Function.Surjective
      ((etaleStalkPresheafFunctor B X hX (geometricPointOfEtalePoint B X hX V x) A).map α)) :
    ∃ (Y : SmallEtale B X hX) (g : Y ⟶ V), Presheaf.imageSieve α b g ∧
      x ∈ Set.range ((SmallEtale.toScheme B X hX).map g) := by
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  obtain ⟨z, hz⟩ := h (Φ.toPresheafFiber V p G b)
  obtain ⟨W, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  replace hz : (Φ.presheafFiber.map α) (Φ.toPresheafFiber W y F c) =
      Φ.toPresheafFiber V p G b := hz
  rw [Φ.toPresheafFiber_naturality_apply α] at hz
  let ZW : Φ.fiber.Elements := ⟨W, y⟩
  let ZV : Φ.fiber.Elements := ⟨V, p⟩
  let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZV
  let l : Z ⟶ ZW := IsCofiltered.minToLeft ZW ZV
  let r : Z ⟶ ZV := IsCofiltered.minToRight ZW ZV
  have hl : Φ.toPresheafFiber Z.1 Z.2 G (G.map l.1.op (α.app (op W) c)) =
      Φ.toPresheafFiber W y G (α.app (op W) c) := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w l.1 Z.2 G) (α.app (op W) c)
    rw [l.2, ConcreteCategory.comp_apply] at this
    exact this
  have hr : Φ.toPresheafFiber Z.1 Z.2 G (G.map r.1.op b) = Φ.toPresheafFiber V p G b := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w r.1 Z.2 G) b
    rw [r.2, ConcreteCategory.comp_apply] at this
    exact this
  obtain ⟨Y, f, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' Z.1 Z.2 (G.map l.1.op (α.app (op W) c))
      (G.map r.1.op b)).1 (hl.trans (hz.trans hr.symm))
  refine ⟨Y, f ≫ r.1, ⟨F.map (f ≫ l.1).op c, ?_⟩, ?_⟩
  · rw [NatTrans.naturality_apply, op_comp, op_comp, G.map_comp, G.map_comp,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact heq
  · have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map f = Z.2.1 := congrArg Subtype.val hy'
    have h2 : Z.2.1 ≫ (SmallEtale.toScheme B X hX).map r.1 = p.1 := congrArg Subtype.val r.2
    refine ⟨y'.1 default, ?_⟩
    rw [← geometricPointOfEtalePointLift_base B X hX V x]
    change (y'.1 ≫ (SmallEtale.toScheme B X hX).map (f ≫ r.1)) default = p.1 default
    rw [Functor.map_comp, ← Category.assoc, h1, h2]

/-- **Local surjectivity from surjectivity on stalks at a detecting set of points.** Let `P` be
a detecting set of points of `X` and `α : F ⟶ G` a morphism of presheaves on the small étale
site of `X` which is surjective on the stalk at every geometric point of `X` lying over a point
of `P`. Then `α` is locally surjective: every section of `G` over an object `U` is, on the
members of an étale covering of `U`, the image of a section of `F`. -/
@[weil "lem_fk102_locally_surjective_of_stalks_surjective"]
theorem isLocallySurjective_of_surjective_etaleStalkMap_of_isDetecting {P : Set X}
    (hP : SmallEtale.IsDetecting B X hX P) {F G : (SmallEtale B X hX)ᵒᵖ ⥤ A} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom default ∈ P →
      Function.Surjective ((etaleStalkPresheafFunctor B X hX s A).map α)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X hX) α := by
  constructor
  intro V b
  let E : Set ((SmallEtale.toScheme B X hX).obj V) :=
    {x | ∃ (Y : SmallEtale B X hX) (g : Y ⟶ V), Presheaf.imageSieve α b g ∧
      x ∈ Set.range ((SmallEtale.toScheme B X hX).map g)}
  have hE : IsOpen E := by
    have : E = ⋃ (Y : SmallEtale B X hX) (g : Y ⟶ V) (_ : Presheaf.imageSieve α b g),
        Set.range ((SmallEtale.toScheme B X hX).map g) := by
      ext x; simp [E]
    rw [this]
    refine isOpen_iUnion fun Y ↦ isOpen_iUnion fun g ↦ isOpen_iUnion fun _ ↦ ?_
    have := etale_toScheme_map_aux B X hX g
    exact ((SmallEtale.toScheme B X hX).map g).isOpenMap.isOpen_range
  have hP' : ∀ x, (B.inclusion.map V.obj.hom) x ∈ P → x ∈ E := fun x hx ↦
    exists_imageSieve_mem_range_of_surjective_etaleStalkMap α V b x
      (h _ ((geometricPointOfEtalePoint_liesOver B X hX V x).symm ▸ hx))
  have huniv : E = Set.univ := by
    by_contra hne
    obtain ⟨v, hv, hvP⟩ := hP V Eᶜ hE.isClosed_compl
      (Set.nonempty_compl.2 hne)
    exact hv (hP' v hvP)
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  have hx : x ∈ E := huniv ▸ Set.mem_univ x
  exact hx

/-- **Local surjectivity from surjectivity on stalks at a detecting set of points, for sheaves
of sets.** Let `P` be a detecting set of points of `X` and `φ : F ⟶ G` a morphism of sheaves of
sets on the small étale site of `X` which is surjective on the stalk at every geometric point of
`X` lying over a point of `P`. Then for every object `U` and every `g ∈ G(U)` there is an étale
covering of `U` on whose members `g` is the image of a section of `F`. -/
@[weil "lem_fk102_locally_surjective_of_stalks_surjective"]
theorem isLocallySurjective_sheaf_of_surjective_etaleStalkMap_of_isDetecting {P : Set X}
    (hP : SmallEtale.IsDetecting B X hX P) {F G : Sheaf (SmallEtale.topology B X hX) (Type u)}
    (φ : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom default ∈ P →
      Function.Surjective ((etaleStalkPresheafFunctor B X hX s (Type u)).map φ.hom)) :
    Sheaf.IsLocallySurjective φ :=
  isLocallySurjective_of_surjective_etaleStalkMap_of_isDetecting hP φ.hom h

end AlgebraicGeometry

end

/-! ### Stalks over a detecting set of points detect isomorphisms of étale sheaves -/

/-!
# Stalks over a detecting set of points detect isomorphisms of étale sheaves

Let `B` be a big étale site containing a scheme `X` and `P ⊆ X` a detecting set of points
(`AlgebraicGeometry.SmallEtale.IsDetecting`). A morphism of étale sheaves on `X`, of sets or of
abelian groups, whose induced map on the stalk at every geometric point of `X` lying over a
point of `P` is bijective, is an isomorphism.

The proof shows the morphism is locally injective and locally surjective. The witnessing sieves
are produced as follows: a sieve on an object `V` of the small étale site whose members cover
every point of `V` mapping into `P` is covering, because the union of the (open) images of its
members is open, and its closed complement, if nonempty, would contain a point mapping into
`P`.

## Main results

* `AlgebraicGeometry.SmallEtale.IsDetecting.mem_topology` — a sieve whose members cover every
  point lying over a detecting set is a covering sieve.
* `AlgebraicGeometry.isIso_of_bijective_presheafFiber_of_isDetecting` — the criterion for
  sheaves with values in a concrete category whose forgetful functor preserves filtered
  colimits and reflects isomorphisms.
* `AlgebraicGeometry.isIso_of_bijective_presheafFiber_of_isDetecting_type` and
  `AlgebraicGeometry.isIso_of_isIso_etaleStalkMap_of_isDetecting` — the cases of sheaves of
  sets and of abelian groups.

## Implementation notes

Geometric points are spectra of algebraically closed fields, and the stalk at a geometric point
`s` is the fibre of the point `AlgebraicGeometry.geometricPointSitePoint` of the small étale
site, which is the colimit over the étale neighbourhoods of `s`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w'

namespace AlgebraicGeometry

namespace SmallEtale.IsDetecting

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {P : Set X}

/-- A sieve on an object `V` of the small étale site whose members cover every point of `V`
lying over a detecting set `P` is a covering sieve. -/
theorem mem_topology (hP : IsDetecting B X hX P) {V : SmallEtale B X hX} {R : Sieve V}
    (hR : ∀ x : (toScheme B X hX).obj V, (B.inclusion.map V.obj.hom).base x ∈ P →
      ∃ (Y : SmallEtale B X hX) (g : Y ⟶ V), R g ∧
        x ∈ Set.range ((toScheme B X hX).map g)) :
    R ∈ topology B X hX V := by
  apply mem_topology_of_jointlySurjective
  let W : Set ((toScheme B X hX).obj V) :=
    ⋃ (Y : SmallEtale B X hX) (g : Y ⟶ V) (_ : R g), Set.range ((toScheme B X hX).map g)
  have hW : IsOpen W := by
    refine isOpen_iUnion fun Y ↦ isOpen_iUnion fun g ↦ isOpen_iUnion fun _ ↦ ?_
    exact ((toScheme B X hX).map g).isOpenMap.isOpen_range
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨v, hvZ, hv⟩ := hP V Wᶜ hW.isClosed_compl ⟨x, by
    simp only [W, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun Y g hg hxg ↦ hx Y g hg hxg⟩
  obtain ⟨Y, g, hg, hvg⟩ := hR v hv
  exact hvZ (Set.mem_iUnion.2 ⟨Y, Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨hg, hvg⟩⟩⟩)

end SmallEtale.IsDetecting

section Criterion

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {P : Set X}

/-- The geometric point of `X` attached to a point `x` of an étale object `V` lies over the
image of `x` in `X`. -/
theorem geometricPointOfEtalePoint_hom_base_default (V : SmallEtale B X hX)
    (x : (SmallEtale.toScheme B X hX).obj V) :
    (geometricPointOfEtalePoint B X hX V x).hom.base default =
      (B.inclusion.map V.obj.hom).base x := by
  have h := geometricPointOfEtalePointLift_base B X hX V x
  have h2 := (geometricPointOfEtalePointLift B X hX V x).2
  rw [← h2, Scheme.Hom.comp_apply, h]

/-- A morphism `f : W ⟶ V` through which a lift of a geometric point factors exhibits the point
of `V` below that lift in the image of `f`. -/
private theorem mem_range_of_lift' {s : GeometricPoint X} {V W : SmallEtale B X hX}
    (f : W ⟶ V) (q : s.source ⟶ (SmallEtale.toScheme B X hX).obj W)
    (t : s.source ⟶ (SmallEtale.toScheme B X hX).obj V)
    (hq : q ≫ (SmallEtale.toScheme B X hX).map f = t)
    (x : (SmallEtale.toScheme B X hX).obj V) (hx : t default = x) :
    x ∈ Set.range ((SmallEtale.toScheme B X hX).map f) := by
  refine ⟨q default, ?_⟩
  rw [← hx, ← hq]
  simp

variable {A : Type*} [Category.{v} A] {FC : A → A → Type*} {CC : A → Type w'}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w'} A FC]
  [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (forget A)]

/-- Surjectivity on the stalks at all geometric points over a detecting set implies local
surjectivity. -/
theorem isLocallySurjective_of_surjective_presheafFiber_of_isDetecting
    (hP : SmallEtale.IsDetecting B X hX P) {F G : (SmallEtale B X hX)ᵒᵖ ⥤ A} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom.base default ∈ P →
      Function.Surjective ((geometricPointSitePoint B X hX s).presheafFiber.map α)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X hX) α := by
  constructor
  intro V b
  apply hP.mem_topology
  intro x hxP
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  obtain ⟨z, hz⟩ := h s (by rw [geometricPointOfEtalePoint_hom_base_default]; exact hxP)
    (Φ.toPresheafFiber V p G b)
  obtain ⟨W, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  rw [Φ.toPresheafFiber_naturality_apply α] at hz
  let ZW : Φ.fiber.Elements := ⟨W, y⟩
  let ZV : Φ.fiber.Elements := ⟨V, p⟩
  let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZV
  let l : Z ⟶ ZW := IsCofiltered.minToLeft ZW ZV
  let r : Z ⟶ ZV := IsCofiltered.minToRight ZW ZV
  have hl : Φ.toPresheafFiber Z.1 Z.2 G (G.map l.1.op (α.app (op W) c)) =
      Φ.toPresheafFiber W y G (α.app (op W) c) := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w l.1 Z.2 G) (α.app (op W) c)
    rw [l.2, ConcreteCategory.comp_apply] at this
    exact this
  have hr : Φ.toPresheafFiber Z.1 Z.2 G (G.map r.1.op b) = Φ.toPresheafFiber V p G b := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w r.1 Z.2 G) b
    rw [r.2, ConcreteCategory.comp_apply] at this
    exact this
  obtain ⟨Y, f, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' Z.1 Z.2 (G.map l.1.op (α.app (op W) c))
      (G.map r.1.op b)).1 (hl.trans (hz.trans hr.symm))
  refine ⟨Y, f ≫ r.1, ⟨F.map (f ≫ l.1).op c, ?_⟩, ?_⟩
  · rw [NatTrans.naturality_apply, op_comp, op_comp, G.map_comp, G.map_comp,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact heq
  · have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map f = Z.2.1 := congrArg Subtype.val hy'
    have h2 : Z.2.1 ≫ (SmallEtale.toScheme B X hX).map r.1 = p.1 := congrArg Subtype.val r.2
    refine mem_range_of_lift' (f ≫ r.1) y'.1 p.1 ?_ x
      (geometricPointOfEtalePointLift_base B X hX V x)
    rw [Functor.map_comp, ← Category.assoc, h1, h2]

/-- Injectivity on the stalks at all geometric points over a detecting set implies local
injectivity. -/
theorem isLocallyInjective_of_injective_presheafFiber_of_isDetecting
    (hP : SmallEtale.IsDetecting B X hX P) {F G : (SmallEtale B X hX)ᵒᵖ ⥤ A} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom.base default ∈ P →
      Function.Injective ((geometricPointSitePoint B X hX s).presheafFiber.map α)) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) α := by
  constructor
  intro V a₁ a₂ ha
  obtain ⟨V⟩ := V
  apply hP.mem_topology
  intro x hxP
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  have hgerm : Φ.toPresheafFiber V p F a₁ = Φ.toPresheafFiber V p F a₂ := by
    refine h s (by rw [geometricPointOfEtalePoint_hom_base_default]; exact hxP) ?_
    rw [Φ.toPresheafFiber_naturality_apply α, Φ.toPresheafFiber_naturality_apply α]
    exact congrArg (Φ.toPresheafFiber V p G) ha
  obtain ⟨Y, f, y', hy', heq⟩ := (Φ.toPresheafFiber_eq_iff' V p a₁ a₂).1 hgerm
  exact ⟨Y, f, heq, mem_range_of_lift' f y'.1 p.1 (congrArg Subtype.val hy') x
    (geometricPointOfEtalePointLift_base B X hX V x)⟩

/-- **Isomorphisms are detected on stalks over a detecting set.** Let `P ⊆ X` be detecting and
`α : F ⟶ G` a morphism of étale sheaves on `X` with values in a concrete category whose
forgetful functor preserves filtered colimits and reflects isomorphisms. If `α` induces a
bijection on the stalk at every geometric point of `X` lying over a point of `P`, then `α` is an
isomorphism. -/
@[weil "lem_fk102_iso_of_stalks_iso_on_detecting"]
theorem isIso_of_bijective_presheafFiber_of_isDetecting [(forget A).ReflectsIsomorphisms]
    [(SmallEtale.topology B X hX).HasSheafCompose (forget A)]
    (hP : SmallEtale.IsDetecting B X hX P) {F G : Sheaf (SmallEtale.topology B X hX) A}
    (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom.base default ∈ P →
      Function.Bijective ((geometricPointSitePoint B X hX s).presheafFiber.map α.hom)) :
    IsIso α :=
  (Sheaf.isLocallyBijective_iff_isIso α).1
    ⟨isLocallyInjective_of_injective_presheafFiber_of_isDetecting hP α.hom fun s hs ↦ (h s hs).1,
      isLocallySurjective_of_surjective_presheafFiber_of_isDetecting hP α.hom
        fun s hs ↦ (h s hs).2⟩

/-- **Isomorphisms of étale sheaves of sets are detected on stalks over a detecting set.** -/
@[weil "lem_fk102_iso_of_stalks_iso_on_detecting"]
theorem isIso_of_bijective_presheafFiber_of_isDetecting_type
    (hP : SmallEtale.IsDetecting B X hX P) {F G : Sheaf (SmallEtale.topology B X hX) (Type u)}
    (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom.base default ∈ P →
      Function.Bijective ((geometricPointSitePoint B X hX s).presheafFiber.map α.hom)) :
    IsIso α :=
  isIso_of_bijective_presheafFiber_of_isDetecting hP α h

end Criterion

section Abelian

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {P : Set X}

private instance [UnivLE.{u, v}] :
    PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{v}) :=
  preservesFilteredColimitsOfSize_of_univLE.{v, v, u, u} (forget AddCommGrpCat.{v})

/-- **Isomorphisms of abelian étale sheaves are detected on stalks over a detecting set.** A
morphism of abelian sheaves on the small étale site of `X` which is an isomorphism on the stalk
at every geometric point of `X` lying over a point of a detecting set `P` is an isomorphism. -/
@[weil "lem_fk102_iso_of_stalks_iso_on_detecting"]
theorem isIso_of_isIso_etaleStalkMap_of_isDetecting [UnivLE.{u, v}]
    (hP : SmallEtale.IsDetecting B X hX P)
    {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v}} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, s.hom.base default ∈ P →
      IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)) :
    IsIso α := by
  refine (Sheaf.isLocallyBijective_iff_isIso α).1
    ⟨isLocallyInjective_of_injective_presheafFiber_of_isDetecting hP α.hom fun s hs ↦ ?_,
      isLocallySurjective_of_surjective_presheafFiber_of_isDetecting hP α.hom fun s hs ↦ ?_⟩
  · have := h s hs
    exact (ConcreteCategory.bijective_of_isIso
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)).1
  · have := h s hs
    exact (ConcreteCategory.bijective_of_isIso
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)).2

end Abelian

end AlgebraicGeometry
