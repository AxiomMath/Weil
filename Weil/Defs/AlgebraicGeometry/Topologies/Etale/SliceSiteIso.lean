module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Defs.AlgebraicGeometry.Sites.Etale
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction

/-!
# The slice of the étale category over an object is the étale category of that object

Let `U = (U, u)` be an object of the étale category `Et(S)` of noetherian separated étale
`S`-schemes. An object of the slice category `Et(S)/U` is a pair `(V, h)` with `V ∈ Et(S)` and
`h : V ⟶ U` a morphism of `Et(S)`; since `h` is étale, `h : V ⟶ U` is an object of `Et(U)`.
This gives a functor `Φ : Et(S)/U ⥤ Et(U)`, the identity on underlying morphisms of schemes,
and it is an isomorphism of categories: its inverse is the functor `Et(U) ⥤ Et(S)/U`,
`(V, v) ↦ ((V, u ∘ v), v)`. Coverings correspond, because both are finite jointly surjective
families of étale morphisms of the same underlying schemes, and `Φ` preserves fibre products.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.fromOver` — the functor `Et(S)/U ⥤ Et(U)`,
  `(V, h) ↦ (V, h)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.overEquivalence` — the resulting equivalence
  `Et(S)/U ≌ Et(U)`, whose inverse is
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toOver'`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.fromOver_comp_toOver'` and
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toOver'_comp_fromOver` — `fromOver` and
  `toOver'` are mutually inverse functors, on the nose: `Et(S)/U` and `Et(U)` are isomorphic
  categories.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isEtaleCovering_fromOver_map_iff` — a family
  of morphisms of `Et(S)/U` is sent to an étale covering exactly when the underlying family of
  morphisms of `Et(S)` is an étale covering.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.preservesPullbacks_fromOver` — `fromOver`
  preserves fibre products.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (U : SmallNoetherianSeparatedEtale B S hS)

omit U in
/-- Two objects of `Et(S)` with the same underlying object of the big étale site and the same
structure morphism are equal. -/
lemma obj_ext {V W : SmallNoetherianSeparatedEtale B S hS} (h₁ : V.obj.obj.left = W.obj.obj.left)
    (h₂ : HEq V.obj.obj.hom W.obj.obj.hom) : V = W := by
  rcases V with ⟨⟨⟨L, ⟨⟩, v⟩, hv⟩, hV⟩
  rcases W with ⟨⟨⟨L', ⟨⟩, w⟩, hw⟩, hW⟩
  cases h₁
  cases h₂
  rfl

/-- The object `h : V ⟶ U` of `Et(U)` attached to an object `(V, h)` of the slice `Et(S)/U`. -/
def fromOverObj (V : Over U) : Over' U :=
  ⟨⟨Over.mk (X := B.obj U.obj.obj.left.1 U.obj.obj.left.property) V.hom.hom.hom.left,
    etale_toScheme_map V.hom⟩, V.left.property⟩

/-- **The functor `Φ : Et(S)/U ⥤ Et(U)`**, sending `(V, h)` to `h : V ⟶ U`, and a morphism of
the slice to the same morphism of schemes. -/
@[weil "lem_fk102_slice_site_iso"]
def fromOver : Over U ⥤ Over' U where
  obj := fromOverObj U
  map {_ _} f := ObjectProperty.homMk (ObjectProperty.homMk
    (Over.homMk f.left.hom.hom.left
      (congrArg (fun g => g.hom.hom.left) (Over.w f))))
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma toScheme_obj_fromOver (V : Over U) :
    (toScheme _ _ _).obj ((fromOver U).obj V) = (toScheme B S hS).obj V.left :=
  rfl

@[simp]
lemma toScheme_map_fromOver {V W : Over U} (f : V ⟶ W) :
    (toScheme _ _ _).map ((fromOver U).map f) = (toScheme B S hS).map f.left :=
  rfl

@[simp]
lemma structureMorphism_fromOver (V : Over U) :
    structureMorphism ((fromOver U).obj V) = (toScheme B S hS).map V.hom :=
  rfl

/-- Composing `Et(U) ⥤ Et(S)/U` with `Φ` is the identity of `Et(U)`. -/
@[weil "lem_fk102_slice_site_iso"]
theorem toOver'_comp_fromOver : toOver' U ⋙ fromOver U = 𝟭 _ :=
  rfl

/-- Composing `Φ` with `Et(U) ⥤ Et(S)/U` is the identity of `Et(S)/U`. -/
@[weil "lem_fk102_slice_site_iso"]
theorem fromOver_comp_toOver' : fromOver U ⋙ toOver' U = 𝟭 _ := by
  have hobj : ∀ V : Over U, (postcompose U).obj ((fromOver U).obj V) = V.left := by
    rintro ⟨⟨⟨⟨L, ⟨⟩, v⟩, hv⟩, hV⟩, ⟨⟩, h⟩
    have e : h.hom.hom.left ≫ U.obj.obj.hom = v := Over.w h.hom.hom
    exact obj_ext rfl (heq_of_eq e)
  have key : ∀ (A A' : SmallNoetherianSeparatedEtale B S hS) (e : A = A') (f : A ⟶ U)
      (f' : A' ⟶ U), f = eqToHom e ≫ f' → Over.mk f = Over.mk f' := by
    rintro _ _ rfl _ _ rfl
    simp
  have hobj' : ∀ V : Over U, (toOver' U).obj ((fromOver U).obj V) = V := by
    rintro ⟨Vl, ⟨⟩, h⟩
    refine key _ _ (hobj _) _ _ (hom_ext ?_)
    rw [Functor.map_comp, eqToHom_map]
    exact (Category.id_comp _).symm
  refine CategoryTheory.Functor.ext hobj' (fun V W f => ?_)
  ext1
  apply hom_ext
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
    Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **`Et(S)/U` and `Et(U)` are isomorphic categories**: `Φ` is bijective on objects. Together
with `AlgebraicGeometry.SmallNoetherianSeparatedEtale.fullyFaithfulFromOver` this says that `Φ` is
an isomorphism of categories. -/
theorem bijective_fromOver_obj : Function.Bijective (fromOver U).obj := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(toOver' U).obj, fun V => ?_, fun V => ?_⟩
  · exact congrArg (fun F : Over U ⥤ Over U => F.obj V) (fromOver_comp_toOver' U)
  · exact congrArg (fun F : Over' U ⥤ Over' U => F.obj V) (toOver'_comp_fromOver U)

/-- The isomorphism of categories `Φ : Et(S)/U ≌ Et(U)`, as an equivalence whose unit and counit
are identities. Its inverse is `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toOver'`. -/
noncomputable def overEquivalence : Over U ≌ Over' U :=
  CategoryTheory.Equivalence.mk (fromOver U) (toOver' U) (eqToIso (fromOver_comp_toOver' U).symm)
    (eqToIso (toOver'_comp_fromOver U))

@[simp]
lemma overEquivalence_functor : (overEquivalence U).functor = fromOver U :=
  rfl

@[simp]
lemma overEquivalence_inverse : (overEquivalence U).inverse = toOver' U :=
  rfl

instance : (fromOver U).IsEquivalence :=
  (overEquivalence U).isEquivalence_functor

instance : (toOver' U).IsEquivalence :=
  (overEquivalence U).isEquivalence_inverse

/-- `Φ` is fully faithful. -/
noncomputable def fullyFaithfulFromOver : (fromOver U).FullyFaithful :=
  (overEquivalence U).fullyFaithfulFunctor

/-- **Coverings correspond.** A family `fᵢ : (Vᵢ, hᵢ) ⟶ (V, h)` of morphisms of `Et(S)/U` is sent
by `Φ` to an étale covering of `Φ (V, h)` if and only if the underlying family `Vᵢ ⟶ V` is an
étale covering of `V`. -/
@[weil "lem_fk102_slice_site_iso"]
theorem isEtaleCovering_fromOver_map_iff {V : Over U} {ι : Type*} {W : ι → Over U}
    (f : ∀ i, W i ⟶ V) :
    Scheme.IsEtaleCovering (fun i => (toScheme _ _ _).map ((fromOver U).map (f i))) ↔
      Scheme.IsEtaleCovering (fun i => (toScheme B S hS).map (f i).left) :=
  Iff.rfl

/-- **`Φ` preserves fibre products.** -/
@[weil "lem_fk102_slice_site_iso"]
instance preservesPullbacks_fromOver : PreservesLimitsOfShape WalkingCospan (fromOver U) :=
  inferInstance

/-- The inverse functor `Et(U) ⥤ Et(S)/U` preserves fibre products. -/
instance preservesPullbacks_toOver' : PreservesLimitsOfShape WalkingCospan (toOver' U) :=
  inferInstance

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
