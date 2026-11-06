module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Equiv

/-!
# Restriction of étale presheaves to an object of the étale category

Let `U = (U, u)` be an object of the étale category `Et(S)` of noetherian separated étale
`S`-schemes. The slice category `Et(S)/U` has as objects the pairs `(V, h)` with `V ∈ Et(S)` and
`h : V ⟶ U` a morphism of `Et(S)`. For a presheaf `L` on `Et(S)` the *restriction* `L|_U` is the
presheaf `(V, h) ↦ L(V)` on `Et(S)/U`, with the restriction maps of `L`.

An object `v : V ⟶ U` of `Et(U)` gives the object `(V, u ∘ v)` of `Et(S)` together with the
morphism `v` to `U`; this is a functor `Et(U) ⥤ Et(S)/U` (an isomorphism of categories, proved
separately), through which `L|_U` is regarded as a presheaf on `Et(U)`: it sends `v : V ⟶ U` to
`L(V, u ∘ v)`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.postcompose` — the functor `Et(U) ⥤ Et(S)`,
  `(V, v) ↦ (V, u ∘ v)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toOver'` — the functor `Et(U) ⥤ Et(S)/U`,
  `(V, v) ↦ ((V, u ∘ v), v)`.
* `AlgebraicGeometry.EtalePresheaf.restrictSlice` — the restriction `L|_U` as a presheaf on the
  slice `Et(S)/U`.
* `AlgebraicGeometry.EtalePresheaf.restrict` — the restriction `L|_U` as a presheaf on `Et(U)`.
* `AlgebraicGeometry.EtalePresheaf.restrictFunctor` — restriction as a functor between categories
  of presheaves.

## Main results

* `AlgebraicGeometry.EtalePresheaf.restrict_eq_comp_restrictSlice` — the presheaf on `Et(U)` is
  the presheaf on the slice read through `Et(U) ⥤ Et(S)/U`.
* `AlgebraicGeometry.EtalePresheaf.restrict_obj`, `AlgebraicGeometry.EtalePresheaf.restrict_map`
  — `L|_U (V) = L(V)`, with the restriction maps of `L`.

## Implementation notes

The functor `Et(U) ⥤ Et(S)` is the restriction to noetherian separated objects of
`AlgebraicGeometry.smallEtalePostcompose`, the composition functor between small étale sites
of [Stacks, Tag 03S3]; the underlying scheme is unchanged, so the noetherian and separated
conditions carry over. The category `Et(U)` is taken in the same big étale site `B` as `Et(S)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (U : SmallNoetherianSeparatedEtale B S hS)

/-- The étale category `Et(U)` of an object `U` of `Et(S)`, in the same big étale site. -/
abbrev Over' : Type _ :=
  SmallNoetherianSeparatedEtale B U.obj.obj.left.1 U.obj.obj.left.property

/-- The functor `Et(U) ⥤ Et(S)` composing the structure morphism of an object with that of
`U`: `(V, v) ↦ (V, u ∘ v)`. -/
noncomputable def postcompose : Over' U ⥤ SmallNoetherianSeparatedEtale B S hS :=
  (SmallEtale.IsNoetherianSeparated B S hS).lift
    (inclusion _ _ _ ⋙ smallEtalePostcompose B S hS U.obj) (fun V => V.property)

@[simp]
lemma toScheme_obj_postcompose (V : Over' U) :
    (toScheme B S hS).obj ((postcompose U).obj V) = (toScheme _ _ _).obj V :=
  rfl

@[simp]
lemma toScheme_map_postcompose {V W : Over' U} (f : V ⟶ W) :
    (toScheme B S hS).map ((postcompose U).map f) = (toScheme _ _ _).map f :=
  rfl

@[simp]
lemma structureMorphism_postcompose (V : Over' U) :
    structureMorphism ((postcompose U).obj V) = structureMorphism V ≫ structureMorphism U := by
  simp only [structureMorphism]
  exact Functor.map_comp _ _ _

instance : (postcompose U).Faithful where
  map_injective {_ _} _ _ h := hom_ext (congrArg (toScheme B S hS).map h :)

/-- The structure morphism `v : V ⟶ U` of an object `(V, v)` of `Et(U)`, as a morphism
`(V, u ∘ v) ⟶ U` of `Et(S)`. -/
noncomputable def postcomposeToBase (V : Over' U) : (postcompose U).obj V ⟶ U :=
  ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk V.obj.obj.hom rfl))

@[simp]
lemma toScheme_map_postcomposeToBase (V : Over' U) :
    (toScheme B S hS).map (postcomposeToBase U V) = structureMorphism V :=
  rfl

@[reassoc (attr := simp)]
lemma postcompose_map_comp_postcomposeToBase {V W : Over' U} (f : V ⟶ W) :
    (postcompose U).map f ≫ postcomposeToBase U W = postcomposeToBase U V :=
  hom_ext (by
    rw [Functor.map_comp, toScheme_map_postcompose, toScheme_map_postcomposeToBase,
      toScheme_map_postcomposeToBase]
    exact toScheme_map_comp_structureMorphism f)

/-- The functor `Et(U) ⥤ Et(S)/U`, `(V, v) ↦ ((V, u ∘ v), v)`, identity on morphisms. -/
noncomputable def toOver' : Over' U ⥤ Over U :=
  Over.lift (postcompose U)
    { app := postcomposeToBase U
      naturality := fun _ _ f => by simp }

@[simp]
lemma toOver'_comp_forget : toOver' U ⋙ Over.forget U = postcompose U :=
  rfl

@[simp]
lemma toOver'_obj_hom (V : Over' U) : ((toOver' U).obj V).hom = postcomposeToBase U V :=
  rfl

end SmallNoetherianSeparatedEtale

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {C : Type v} [Category.{w} C]

/-- **Restriction of a presheaf to a slice.** For a presheaf `L` on `Et(S)` and `U ∈ Et(S)`, the
presheaf `(V, h) ↦ L(V)` on the slice category `Et(S)/U`, with the restriction maps of `L`. -/
@[weil "def_fk102_sheaf_restriction_to_etale"]
abbrev restrictSlice (L : EtalePresheaf B S hS C) (U : SmallNoetherianSeparatedEtale B S hS) :
    (Over U)ᵒᵖ ⥤ C :=
  (Over.forget U).op ⋙ L

/-- **Restriction of a presheaf to an object of `Et(S)`.** For a presheaf `L` on `Et(S)` and
`U = (U, u) ∈ Et(S)`, the presheaf `L|_U` on `Et(U)`, sending `v : V ⟶ U` to `L(V, u ∘ v)`. -/
@[weil "def_fk102_sheaf_restriction_to_etale"]
noncomputable abbrev restrict (L : EtalePresheaf B S hS C)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    EtalePresheaf B U.obj.obj.left.1 U.obj.obj.left.property C :=
  (postcompose U).op ⋙ L

/-- The restriction to `Et(U)` is the restriction to the slice `Et(S)/U` read through the
functor `Et(U) ⥤ Et(S)/U`. -/
@[weil "def_fk102_sheaf_restriction_to_etale"]
lemma restrict_eq_comp_restrictSlice (L : EtalePresheaf B S hS C)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    restrict L U = (toOver' U).op ⋙ restrictSlice L U :=
  rfl

lemma restrict_obj (L : EtalePresheaf B S hS C) (U : SmallNoetherianSeparatedEtale B S hS)
    (V : (Over' U)ᵒᵖ) : (restrict L U).obj V = L.obj (op ((postcompose U).obj V.unop)) :=
  rfl

lemma restrict_map (L : EtalePresheaf B S hS C) (U : SmallNoetherianSeparatedEtale B S hS)
    {V W : (Over' U)ᵒᵖ} (f : V ⟶ W) :
    (restrict L U).map f = L.map ((postcompose U).map f.unop).op :=
  rfl

lemma restrictSlice_obj (L : EtalePresheaf B S hS C) (U : SmallNoetherianSeparatedEtale B S hS)
    (V : (Over U)ᵒᵖ) : (restrictSlice L U).obj V = L.obj (op V.unop.left) :=
  rfl

lemma restrictSlice_map (L : EtalePresheaf B S hS C) (U : SmallNoetherianSeparatedEtale B S hS)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    (restrictSlice L U).map f = L.map f.unop.left.op :=
  rfl

variable (C) in
/-- Restriction to `Et(U)` as a functor between categories of presheaves. -/
noncomputable def restrictFunctor (U : SmallNoetherianSeparatedEtale B S hS) :
    EtalePresheaf B S hS C ⥤ EtalePresheaf B U.obj.obj.left.1 U.obj.obj.left.property C :=
  (Functor.whiskeringLeft _ _ C).obj (postcompose U).op

@[simp]
lemma restrictFunctor_obj (U : SmallNoetherianSeparatedEtale B S hS)
    (L : EtalePresheaf B S hS C) : (restrictFunctor C U).obj L = restrict L U :=
  rfl

@[simp]
lemma restrictFunctor_map_app (U : SmallNoetherianSeparatedEtale B S hS)
    {L L' : EtalePresheaf B S hS C} (φ : L ⟶ L') (V : (Over' U)ᵒᵖ) :
    ((restrictFunctor C U).map φ).app V = φ.app (op ((postcompose U).obj V.unop)) :=
  rfl

end EtalePresheaf

end AlgebraicGeometry

end
