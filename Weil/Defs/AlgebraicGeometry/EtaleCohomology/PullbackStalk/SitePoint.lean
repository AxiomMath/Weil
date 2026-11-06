module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Attr

/-!
# The coincidence set of two sections of a presheaf on the small étale site

Let `F` be a presheaf of sets on the small étale site of a scheme `X`, let `U` be an object of
that site and let `α β : F(U)`. A geometric point `ū : Spec Ω → U` of `U` makes `(U, ū)` an
étale neighbourhood of the geometric point `π ∘ ū` of `X`, where `π : U → X` is the structure
morphism, so every section `α` of `F` over `U` has a germ `α_ū` in the stalk `F_{π ∘ ū}`. The
coincidence set `C(α, β) ⊆ U` is the set of points `u ∈ U` such that `α_ū = β_ū` for every
geometric point `ū` of `U` lying over `u`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.germ`: the germ `α_ū` of a section `α ∈ F(U)` at a geometric
  point `ū` of `U`, an element of the stalk of `F` at the geometric point `π ∘ ū` of `X`.
* `AlgebraicGeometry.SmallEtale.germCoincidenceSet`: the coincidence set `C(α, β)`.

## Main results

* `AlgebraicGeometry.SmallEtale.mem_germCoincidenceSet_iff`: membership in `C(α, β)`.
* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_self`: `C(α, α) = U`.
* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_comm`: `C(α, β) = C(β, α)`.
* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_inter_subset`:
  `C(α, β) ∩ C(β, γ) ⊆ C(α, γ)`.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale B X hX` inside a big étale site `B`, and
geometric points are `AlgebraicGeometry.GeometricPoint`s, i.e. spectra of algebraically closed
fields. The stalk at a geometric point is the fiber of Mathlib's point of a site
`AlgebraicGeometry.geometricPointSitePoint`, which is definitionally the colimit over étale
neighbourhoods `AlgebraicGeometry.etaleStalk`; the germ is the colimit insertion
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber`, so Mathlib's API for germs at a
point of a site applies to it directly.

The presheaves take values in `Type v` for any universe `v` with `UnivLE.{u, v}`, so that
colimits indexed by étale neighbourhoods exist in `Type v`; this covers both sheaves of sets in
the universe of the schemes and the underlying sets of sheaves of modules in `Type (u + 1)`. The
hypothesis `UnivLE.{u, v}` is placed after the presheaf, or bound implicitly when the presheaf is
implicit, so that `v` is read off the presheaf before the instance is synthesized.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  I.3.15 (2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The geometric point `π ∘ ū` of `X` obtained from a geometric point `ū` of an object `U` of
the small étale site of `X` by composing with the structure morphism `π : U → X`. -/
abbrev toBaseGeometricPoint (U : SmallEtale B X hX)
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) : GeometricPoint X :=
  ū.map (B.inclusion.map U.obj.hom)

/-- A geometric point `ū` of `U` is a lift of the geometric point `π ∘ ū` of `X` to `U`, that
is, `(U, ū)` is an étale neighbourhood of `π ∘ ū`. -/
def geometricPointLift (U : SmallEtale B X hX)
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) :
    (geometricPointFiber B X hX (toBaseGeometricPoint U ū)).obj U :=
  ⟨ū.hom, rfl⟩

@[simp]
lemma geometricPointLift_coe (U : SmallEtale B X hX)
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) :
    (geometricPointLift U ū).1 = ū.hom :=
  rfl

/-- The germ `α_ū` of a section `α ∈ F(U)` at a geometric point `ū` of `U`: the image of `α`
in the stalk of `F` at the geometric point `π ∘ ū` of `X`, under the canonical map from the term
indexed by the étale neighbourhood `(U, ū)`. -/
@[weil "def_fk103_germ_of_section"]
def germ (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}] {U : SmallEtale B X hX}
    (α : F.obj (op U))
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) :
    (geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).presheafFiber.obj F :=
  (geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber U
    (geometricPointLift U ū) F α

/-- The coincidence set `C(α, β)` of two sections `α β ∈ F(U)` of a presheaf `F` on the small
étale site of `X`: the set of points `u ∈ U` such that `α_ū = β_ū` for every geometric point `ū`
of `U` lying over `u`. -/
@[weil "def_fk103_germ_coincidence_set"]
def germCoincidenceSet (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]
    {U : SmallEtale B X hX}
    (α β : F.obj (op U)) : Set ((SmallEtale.toScheme B X hX).obj U) :=
  {u | ∀ ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U), ū.LiesOver u →
    germ F α ū = germ F β ū}

variable (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}] {U : SmallEtale B X hX}

lemma mem_germCoincidenceSet_iff (α β : F.obj (op U)) (u : (SmallEtale.toScheme B X hX).obj U) :
    u ∈ germCoincidenceSet F α β ↔
      ∀ ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U), ū.LiesOver u →
        germ F α ū = germ F β ū :=
  Iff.rfl

/-- A geometric point lying over a point of the coincidence set sees equal germs. -/
lemma germ_eq_of_mem_germCoincidenceSet {α β : F.obj (op U)}
    {u : (SmallEtale.toScheme B X hX).obj U} (hu : u ∈ germCoincidenceSet F α β)
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) (hū : ū.LiesOver u) :
    germ F α ū = germ F β ū :=
  hu ū hū

@[simp]
lemma germCoincidenceSet_self (α : F.obj (op U)) : germCoincidenceSet F α α = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ ↦ rfl

lemma germCoincidenceSet_comm (α β : F.obj (op U)) :
    germCoincidenceSet F α β = germCoincidenceSet F β α := by
  ext u
  exact ⟨fun h ū hū ↦ (h ū hū).symm, fun h ū hū ↦ (h ū hū).symm⟩

lemma germCoincidenceSet_inter_subset (α β γ : F.obj (op U)) :
    germCoincidenceSet F α β ∩ germCoincidenceSet F β γ ⊆ germCoincidenceSet F α γ :=
  fun _ h ū hū ↦ (h.1 ū hū).trans (h.2 ū hū)

/-- Equal sections coincide everywhere. -/
lemma germCoincidenceSet_eq_univ_of_eq {α β : F.obj (op U)} (h : α = β) :
    germCoincidenceSet F α β = Set.univ := by
  subst h
  exact germCoincidenceSet_self F α

end AlgebraicGeometry.SmallEtale

end

/-! ### Étale sheaves of sets with finite stalks -/

/-!
# Étale sheaves of sets with finite stalks

An étale sheaf of sets `F` on a scheme `X` *has finite stalks* if its stalk `F_x̄` is a finite
set for every geometric point `x̄` of `X`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.HasFiniteStalks`: the sheaf `F` on the small étale site of `X`
  has finite stalks.

## Main results

* `AlgebraicGeometry.SmallEtale.HasFiniteStalks.finite`: the stalk at a geometric point of a
  sheaf with finite stalks is finite.
* `AlgebraicGeometry.SmallEtale.HasFiniteStalks.of_mono`: a subsheaf of a sheaf with finite
  stalks has finite stalks.
* `AlgebraicGeometry.SmallEtale.HasFiniteStalks.of_iso` and
  `AlgebraicGeometry.SmallEtale.hasFiniteStalks_iff_of_iso`: the property is invariant under
  isomorphism of sheaves.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale B X hX` inside a big étale site `B`, and
geometric points are `AlgebraicGeometry.GeometricPoint`s, spectra of algebraically closed
fields. The stalk at a geometric point `x̄` is the fiber functor of the point of the site
`AlgebraicGeometry.geometricPointSitePoint`, which is definitionally the colimit over the étale
neighbourhoods of `x̄` (`AlgebraicGeometry.etaleStalk_eq_presheafFiber`). The source allows
geometric points over separably closed fields; for a sheaf of sets the stalk does not change
when the field is enlarged to an algebraic closure, so the two conditions agree.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- An étale sheaf of sets `F` on `X` has finite stalks if its stalk at every geometric point of
`X` is a finite set. -/
@[weil "def_fk103_sheaf_finite_stalks"]
def HasFiniteStalks (F : Sheaf (SmallEtale.topology B X hX) (Type v)) [UnivLE.{u, v}] :
    Prop :=
  ∀ x : GeometricPoint X, Finite ((geometricPointSitePoint B X hX x).sheafFiber.obj F)

lemma hasFiniteStalks_iff (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    [UnivLE.{u, v}] :
    HasFiniteStalks F ↔
      ∀ x : GeometricPoint X, Finite ((geometricPointSitePoint B X hX x).sheafFiber.obj F) :=
  Iff.rfl

/-- In terms of the stalk of the underlying presheaf, `AlgebraicGeometry.etaleStalk`. -/
lemma hasFiniteStalks_iff_etaleStalk (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    [UnivLE.{u, v}] :
    HasFiniteStalks F ↔ ∀ x : GeometricPoint X, Finite (etaleStalk B X hX x F.obj) :=
  Iff.rfl

namespace HasFiniteStalks

variable {F G : Sheaf (SmallEtale.topology B X hX) (Type v)} {hv : UnivLE.{u, v}}

/-- The stalk of a sheaf with finite stalks at a geometric point is finite. -/
lemma finite (h : HasFiniteStalks F) (x : GeometricPoint X) :
    Finite ((geometricPointSitePoint B X hX x).sheafFiber.obj F) :=
  h x

/-- If a map of sheaves is injective on every stalk, finiteness of the stalks of the target
passes to the source. -/
lemma of_injective (φ : F ⟶ G) (hφ : ∀ x : GeometricPoint X,
    Function.Injective ((geometricPointSitePoint B X hX x).sheafFiber.map φ))
    (hG : HasFiniteStalks G) : HasFiniteStalks F := fun x ↦
  have := hG x
  Finite.of_injective _ (hφ x)

/-- If a map of sheaves is surjective on every stalk, finiteness of the stalks of the source
passes to the target. -/
lemma of_surjective (φ : F ⟶ G) (hφ : ∀ x : GeometricPoint X,
    Function.Surjective ((geometricPointSitePoint B X hX x).sheafFiber.map φ))
    (hF : HasFiniteStalks F) : HasFiniteStalks G := fun x ↦
  have := hF x
  Finite.of_surjective _ (hφ x)

/-- Having finite stalks is invariant under isomorphism of sheaves. -/
lemma of_iso (e : F ≅ G) (hF : HasFiniteStalks F) : HasFiniteStalks G := fun x ↦
  have := hF x
  Finite.of_equiv _ ((geometricPointSitePoint B X hX x).sheafFiber.mapIso e).toEquiv

end HasFiniteStalks

lemma hasFiniteStalks_iff_of_iso {F G : Sheaf (SmallEtale.topology B X hX) (Type v)}
    (e : F ≅ G) [UnivLE.{u, v}] : HasFiniteStalks F ↔ HasFiniteStalks G :=
  ⟨HasFiniteStalks.of_iso e, HasFiniteStalks.of_iso e.symm⟩

namespace HasFiniteStalks

/- The two lemmas below are stated for sheaves valued in the scheme universe: that the stalk
functor preserves monomorphisms and epimorphisms is deduced from `AB5` of `Type u` for colimits
of size `u`. -/

/-- A subsheaf of a sheaf with finite stalks has finite stalks. -/
lemma of_mono {F G : Sheaf (SmallEtale.topology B X hX) (Type u)} (φ : F ⟶ G) [Mono φ]
    (hG : HasFiniteStalks G) : HasFiniteStalks F :=
  of_injective φ (fun _ ↦ (mono_iff_injective _).1 inferInstance) hG

/-- A quotient of a sheaf with finite stalks has finite stalks. -/
lemma of_epi {F G : Sheaf (SmallEtale.topology B X hX) (Type u)} (φ : F ⟶ G) [Epi φ]
    (hF : HasFiniteStalks F) : HasFiniteStalks G :=
  of_surjective φ (fun _ ↦ (epi_iff_surjective _).1 inferInstance) hF

end HasFiniteStalks

end AlgebraicGeometry.SmallEtale

end
