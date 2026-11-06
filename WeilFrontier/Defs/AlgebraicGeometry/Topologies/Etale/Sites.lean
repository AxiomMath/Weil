module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# The étale category of noetherian separated étale schemes

Let `B` be a big étale site containing a scheme `S`. The category `Et(S)` of Freitag–Kiehl has
as objects the étale morphisms `u : U ⟶ S` whose source `U` is a noetherian separated scheme,
and as morphisms `(U, u) ⟶ (V, v)` the morphisms of schemes `h : U ⟶ V` with `h ≫ v = u`; it
is a full subcategory of the category of `S`-schemes.

Here it is the full subcategory of the small étale category `AlgebraicGeometry.SmallEtale B S hS`
of [Stacks, Tag 021B] on the objects whose underlying scheme is noetherian and separated.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsNoetherianSeparated` — the property of a small étale object
  over `S` that its underlying scheme is noetherian and separated.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale` — the resulting full subcategory, with its
  inclusion into the small étale category, its functor `toScheme` to schemes, its structure
  morphisms `structureMorphism`, and the functor `toOver` to `S`-schemes.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.mk` — the object given by an étale morphism
  `u : U ⟶ S` from a noetherian separated scheme `U` lying in `B`.
* `AlgebraicGeometry.Scheme.noetherianSeparatedEtale` — the same category for a bare scheme,
  with the big étale site `AlgebraicGeometry.BigEtaleSite.containing`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.fullyFaithfulToOver` — the category is a full
  subcategory of the category of `S`-schemes.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.homEquiv` — its morphisms `(U, u) ⟶ (V, v)`
  are exactly the morphisms of schemes `h : U ⟶ V` with `h ≫ v = u`.

## Implementation notes

The objects live in a big étale site `B`, i.e. below a size cutoff, as in the small étale site
of [Stacks, Tag 021B]; this is how the category is made to have a set of morphisms between any
two objects while still containing every noetherian separated étale `S`-scheme up to
isomorphism. The Freitag–Kiehl category has no such cutoff; the two agree up to equivalence
because every noetherian étale `S`-scheme is isomorphic to one of size below the cutoff.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property of an object of the small étale category of `S` that its underlying scheme is
noetherian and separated. -/
abbrev SmallEtale.IsNoetherianSeparated : ObjectProperty (SmallEtale B S hS) :=
  fun U ↦ IsNoetherian ((SmallEtale.toScheme B S hS).obj U) ∧
    ((SmallEtale.toScheme B S hS).obj U).IsSeparated

/-- **The étale category `Et(S)`.** The full subcategory of the small étale category of `S` on
the objects whose underlying scheme is noetherian and separated: its objects are the étale
morphisms `u : U ⟶ S` with `U` noetherian and separated, and its morphisms are the morphisms of
`S`-schemes. -/
@[weil "def_fk102_etale_site_category"]
abbrev SmallNoetherianSeparatedEtale := (SmallEtale.IsNoetherianSeparated B S hS).FullSubcategory

namespace SmallNoetherianSeparatedEtale

/-- The canonical full embedding into the small étale category. -/
abbrev inclusion : SmallNoetherianSeparatedEtale B S hS ⥤ SmallEtale B S hS :=
  (SmallEtale.IsNoetherianSeparated B S hS).ι

/-- The functor sending an object `(U, u)` to the scheme `U`. -/
abbrev toScheme : SmallNoetherianSeparatedEtale B S hS ⥤ Scheme.{u} :=
  inclusion B S hS ⋙ SmallEtale.toScheme B S hS

variable {B S hS}

instance isNoetherian_toScheme_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    IsNoetherian ((toScheme B S hS).obj U) :=
  U.property.1

instance isSeparated_toScheme_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    ((toScheme B S hS).obj U).IsSeparated :=
  U.property.2

/-- The structure morphism `u : U ⟶ S` of an object `(U, u)`. -/
abbrev structureMorphism (U : SmallNoetherianSeparatedEtale B S hS) :
    (toScheme B S hS).obj U ⟶ S :=
  B.inclusion.map U.obj.obj.hom

instance etale_structureMorphism (U : SmallNoetherianSeparatedEtale B S hS) :
    Etale (structureMorphism U) :=
  U.obj.property

@[reassoc (attr := simp)]
lemma toScheme_map_comp_structureMorphism {U V : SmallNoetherianSeparatedEtale B S hS}
    (h : U ⟶ V) : (toScheme B S hS).map h ≫ structureMorphism V = structureMorphism U := by
  simp only [structureMorphism, Functor.comp_map, ← Functor.map_comp]
  congr 1
  exact Over.w h.hom.hom

lemma hom_ext {U V : SmallNoetherianSeparatedEtale B S hS} {g h : U ⟶ V}
    (e : (toScheme B S hS).map g = (toScheme B S hS).map h) : g = h :=
  (toScheme B S hS).map_injective e

/-- The object of `Et(S)` given by an étale morphism `u : U ⟶ S` from a noetherian separated
scheme `U` lying in `B`. -/
def mk (U : Scheme.{u}) (hU : B.Contains U) (u : U ⟶ S) [Etale u] [IsNoetherian U]
    [U.IsSeparated] : SmallNoetherianSeparatedEtale B S hS :=
  ⟨⟨Over.mk (Y := B.obj U hU) (ObjectProperty.homMk u), ‹Etale u›⟩,
    ⟨‹IsNoetherian U›, ‹U.IsSeparated›⟩⟩

@[simp]
lemma toScheme_obj_mk (U : Scheme.{u}) (hU : B.Contains U) (u : U ⟶ S) [Etale u]
    [IsNoetherian U] [U.IsSeparated] : (toScheme B S hS).obj (mk U hU u) = U :=
  rfl

@[simp]
lemma structureMorphism_mk (U : Scheme.{u}) (hU : B.Contains U) (u : U ⟶ S) [Etale u]
    [IsNoetherian U] [U.IsSeparated] : structureMorphism (mk (hS := hS) U hU u) = u :=
  rfl

variable (B S hS) in
/-- The final object `(S, id)` of `Et(S)`, for a noetherian separated scheme `S`. -/
def final [IsNoetherian S] [S.IsSeparated] : SmallNoetherianSeparatedEtale B S hS :=
  mk S hS (𝟙 S)

/-- **Morphisms of `Et(S)`.** A morphism `(U, u) ⟶ (V, v)` is the same as a morphism of schemes
`h : U ⟶ V` with `h ≫ v = u`. -/
@[weil "def_fk102_etale_site_category"]
def homEquiv (U V : SmallNoetherianSeparatedEtale B S hS) :
    (U ⟶ V) ≃ {h : (toScheme B S hS).obj U ⟶ (toScheme B S hS).obj V //
      h ≫ structureMorphism V = structureMorphism U} where
  toFun g := ⟨(toScheme B S hS).map g, toScheme_map_comp_structureMorphism g⟩
  invFun h := ObjectProperty.homMk (ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk h.1) (by ext1; exact h.2)))
  left_inv g := rfl
  right_inv h := rfl

@[simp]
lemma homEquiv_apply_coe {U V : SmallNoetherianSeparatedEtale B S hS} (g : U ⟶ V) :
    (homEquiv U V g : (toScheme B S hS).obj U ⟶ (toScheme B S hS).obj V) = (toScheme B S hS).map g :=
  rfl

variable (B S hS)

/-- The functor from `Et(S)` to the category of `S`-schemes, sending `(U, u)` to `u`. -/
def toOver : SmallNoetherianSeparatedEtale B S hS ⥤ Over S :=
  inclusion B S hS ⋙ SmallEtale.inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion

@[simp]
lemma toOver_obj_hom (U : SmallNoetherianSeparatedEtale B S hS) :
    ((toOver B S hS).obj U).hom = structureMorphism U :=
  rfl

@[simp]
lemma toOver_map_left {U V : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ V) :
    ((toOver B S hS).map h).left = (toScheme B S hS).map h :=
  rfl

/-- **`Et(S)` is a full subcategory of the category of `S`-schemes.** -/
@[weil "def_fk102_etale_site_category"]
def fullyFaithfulToOver : (toOver B S hS).FullyFaithful :=
  ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)).comp
    ((ObjectProperty.fullyFaithfulι _).over (B.obj S hS))

instance : (toOver B S hS).Full := (fullyFaithfulToOver B S hS).full

instance : (toOver B S hS).Faithful := (fullyFaithfulToOver B S hS).faithful

end SmallNoetherianSeparatedEtale

/-- The étale category `Et(X)` of a bare scheme `X`: `AlgebraicGeometry.SmallNoetherianSeparatedEtale`
for the big étale site `AlgebraicGeometry.BigEtaleSite.containing X`. -/
@[weil "def_fk102_etale_site_category"]
noncomputable abbrev Scheme.noetherianSeparatedEtale (X : Scheme.{u}) :=
  SmallNoetherianSeparatedEtale (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)

end AlgebraicGeometry

end

/-! ### Detecting sets of points -/

/-!
# Detecting sets of points

Let `S` be a scheme. A set of points `P ⊆ S` is *detecting* if for every object `V` of the small
étale site of `S`, every nonempty closed subset of `V` contains a point whose image in `S` lies
in `P`. Such sets suffice to test exactness and isomorphy of morphisms of étale sheaves on
stalks: one only needs the stalks at geometric points lying over points of `P`. The whole of `S`
is detecting, and so is the set of points closed in their fibre over a base scheme for a
morphism locally of finite type.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsDetecting` — a set `P ⊆ S` is detecting for the small étale
  site `SmallEtale B S hS`: every nonempty closed subset of an object `V` contains a point
  mapping into `P` under the structure morphism `V ⟶ S`.
* `AlgebraicGeometry.Scheme.IsDetecting` — the same condition quantified over all étale
  morphisms `V ⟶ S` of schemes, independent of the choice of a big étale site.

## Main results

* `AlgebraicGeometry.Scheme.IsDetecting.smallEtale` — a set detecting for all étale schemes
  over `S` is detecting for every small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.IsDetecting.univ`, `AlgebraicGeometry.Scheme.IsDetecting.univ`
  — the set of all points is detecting.
* `AlgebraicGeometry.SmallEtale.IsDetecting.mono`, `AlgebraicGeometry.Scheme.IsDetecting.mono`
  — a superset of a detecting set is detecting.
* `AlgebraicGeometry.SmallEtale.IsDetecting.exists_mem_of_nonempty` — a nonempty object of the
  small étale site has a point mapping into a detecting set.

## Implementation notes

Freitag and Kiehl test the condition on their category `Et(S)` of noetherian separated étale
`S`-schemes. Here it is tested on every object of the small étale site of [Stacks, Tag 021B],
which contains the noetherian separated ones; the condition is therefore at least as strong.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- A set of points `P ⊆ S` is *detecting* for the small étale site of `S` if for every object
`V` of the site, every nonempty closed subset of `V` contains a point whose image under the
structure morphism `V ⟶ S` lies in `P`. -/
@[weil "def_fk102_detecting_set_of_points"]
def IsDetecting (P : Set S) : Prop :=
  ∀ (V : SmallEtale B S hS) (Z : Set ((toScheme B S hS).obj V)), IsClosed Z → Z.Nonempty →
    ∃ v ∈ Z, (B.inclusion.map V.obj.hom).base v ∈ P

theorem isDetecting_iff (P : Set S) :
    IsDetecting B S hS P ↔
      ∀ (V : SmallEtale B S hS) (Z : Set ((toScheme B S hS).obj V)), IsClosed Z → Z.Nonempty →
        ∃ v ∈ Z, (B.inclusion.map V.obj.hom).base v ∈ P :=
  Iff.rfl

namespace IsDetecting

variable {P Q : Set S}

/-- The defining property of a detecting set. -/
theorem exists_mem (hP : IsDetecting B S hS P) (V : SmallEtale B S hS)
    {Z : Set ((toScheme B S hS).obj V)} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ v ∈ Z, (B.inclusion.map V.obj.hom).base v ∈ P :=
  hP V Z hZ hne

/-- A nonempty object of the small étale site has a point mapping into a detecting set. -/
theorem exists_mem_of_nonempty (hP : IsDetecting B S hS P) (V : SmallEtale B S hS)
    [Nonempty ((toScheme B S hS).obj V)] :
    ∃ v : (toScheme B S hS).obj V, (B.inclusion.map V.obj.hom).base v ∈ P := by
  obtain ⟨v, -, hv⟩ := hP V Set.univ isClosed_univ Set.univ_nonempty
  exact ⟨v, hv⟩

/-- A superset of a detecting set is detecting. -/
theorem mono (hP : IsDetecting B S hS P) (hPQ : P ⊆ Q) : IsDetecting B S hS Q := by
  intro V Z hZ hne
  obtain ⟨v, hvZ, hv⟩ := hP V Z hZ hne
  exact ⟨v, hvZ, hPQ hv⟩

variable (B S hS) in
/-- The set of all points is detecting. -/
theorem univ : IsDetecting B S hS (Set.univ : Set S) := by
  intro V Z _ hne
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv, Set.mem_univ _⟩

end IsDetecting

end SmallEtale

namespace Scheme

/-- A set of points `P ⊆ S` is *detecting* if for every étale morphism `f : V ⟶ S`, every
nonempty closed subset of `V` contains a point whose image under `f` lies in `P`. -/
def IsDetecting (S : Scheme.{u}) (P : Set S) : Prop :=
  ∀ ⦃V : Scheme.{u}⦄ (f : V ⟶ S) [Etale f] (Z : Set V), IsClosed Z → Z.Nonempty →
    ∃ v ∈ Z, f.base v ∈ P

namespace IsDetecting

variable {S : Scheme.{u}} {P Q : Set S}

/-- The defining property of a detecting set. -/
theorem exists_mem (hP : S.IsDetecting P) {V : Scheme.{u}} (f : V ⟶ S) [Etale f]
    {Z : Set V} (hZ : IsClosed Z) (hne : Z.Nonempty) : ∃ v ∈ Z, f.base v ∈ P :=
  hP f Z hZ hne

/-- A superset of a detecting set is detecting. -/
theorem mono (hP : S.IsDetecting P) (hPQ : P ⊆ Q) : S.IsDetecting Q := by
  intro V f _ Z hZ hne
  obtain ⟨v, hvZ, hv⟩ := hP f Z hZ hne
  exact ⟨v, hvZ, hPQ hv⟩

variable (S) in
/-- The set of all points is detecting. -/
theorem univ : S.IsDetecting Set.univ := by
  intro V f _ Z _ hne
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv, Set.mem_univ _⟩

/-- A set detecting for all étale schemes over `S` is detecting for every small étale site
of `S`. -/
theorem smallEtale (hP : S.IsDetecting P) (B : BigEtaleSite.{u}) (hS : B.Contains S) :
    SmallEtale.IsDetecting B S hS P := by
  intro V Z hZ hne
  exact hP (B.inclusion.map V.obj.hom) Z hZ hne

end IsDetecting

end Scheme

end AlgebraicGeometry
