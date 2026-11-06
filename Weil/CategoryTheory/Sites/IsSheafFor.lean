module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# The sheaf condition on covering sieves of the small étale site

For a presheaf `P` on a category `C` and a sieve `S` on an object `U`, the sections of `P` over
`S` are the sieve-compatible families of elements `(s_g)_{g ∈ S}`, and restriction gives a map
`P(U) → P(S)`, `t ↦ (g^* t)_g`. A presheaf of sets or of abelian groups on a site is a sheaf if
and only if this map is bijective for every covering sieve `S`. We prove this for an arbitrary
Grothendieck topology, and record it for the small étale site of a scheme [FK, I.2].

## Main definitions

* `CategoryTheory.Sieve.toSieveCompatible`: the map `P(U) → P(S)` to sieve-compatible families
  of elements.

## Main results

* `CategoryTheory.Presieve.isSheafFor_iff_bijective_toSieveCompatible`: `P` satisfies the sheaf
  condition for the sieve `S` if and only if `P(U) → P(S)` is bijective.
* `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget_addCommGrpCat`: a presheaf of abelian
  groups is a sheaf if and only if its underlying presheaf of sets is, with no condition relating
  the universes of the site and of the groups.
* `AlgebraicGeometry.Scheme.isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible`: a
  presheaf of sets on the small étale site of `X` is a sheaf if and only if
  `F(U) → F(S)` is bijective for every covering sieve `S` on every `U`.
* `Scheme.isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible_addCommGrpCat`: the same
  for presheaves of abelian groups.

## Implementation notes

The étale site is Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology` on `X.Etale`, whose
objects are all étale `X`-schemes, rather than the noetherian separated ones of [FK]. The criterion
holds for every Grothendieck topology, so nothing about the étale topology is used. For a presheaf
of abelian groups the group structure of `F(S)` plays no role in bijectivity, so the map is taken
on the underlying presheaf of sets.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Sieve

/-- The map `P(U) → P(S)` sending a section `t` to the sieve-compatible family `(g^* t)_{g ∈ S}`
of its restrictions. -/
def toSieveCompatible (P : Cᵒᵖ ⥤ Type w) {U : C} (S : Sieve U) :
    P.obj (op U) → {x : Presieve.FamilyOfElements P S.arrows // x.SieveCompatible} :=
  fun t ↦ ⟨fun _ f _ ↦ P.map f.op t, fun _ _ f g _ ↦ by simp⟩

@[simp]
lemma toSieveCompatible_coe_apply (P : Cᵒᵖ ⥤ Type w) {U : C} (S : Sieve U) (t : P.obj (op U))
    {V : C} (f : V ⟶ U) (hf : S f) :
    (toSieveCompatible P S t).1 f hf = P.map f.op t :=
  rfl

end Sieve

namespace Presieve

/-- A presheaf of sets satisfies the sheaf condition for a sieve `S` on `U` if and only if the map
`P(U) → P(S)` to sieve-compatible families is bijective. -/
theorem isSheafFor_iff_bijective_toSieveCompatible (P : Cᵒᵖ ⥤ Type w) {U : C} (S : Sieve U) :
    IsSheafFor P S.arrows ↔ Function.Bijective (Sieve.toSieveCompatible P S) := by
  constructor
  · intro h
    refine ⟨fun t₁ t₂ ht ↦ ?_, fun x ↦ ?_⟩
    · refine h.isSeparatedFor.ext fun V f hf ↦ ?_
      exact congrArg (fun y : {x : FamilyOfElements P S.arrows // x.SieveCompatible} ↦
        y.1 f hf) ht
    · obtain ⟨t, ht, -⟩ := h x.1 ((compatible_iff_sieveCompatible x.1).2 x.2)
      exact ⟨t, Subtype.ext <| funext fun V ↦ funext fun f ↦ funext fun hf ↦ ht f hf⟩
  · rintro ⟨hinj, hsurj⟩ x hx
    obtain ⟨t, ht⟩ := hsurj ⟨x, (compatible_iff_sieveCompatible x).1 hx⟩
    refine ⟨t, fun V f hf ↦ ?_, fun t' ht' ↦ hinj ?_⟩
    · exact (congrArg (fun y : {x : FamilyOfElements P S.arrows // x.SieveCompatible} ↦
        y.1 f hf) ht)
    · rw [ht]
      exact Subtype.ext <| funext fun V ↦ funext fun f ↦ funext fun hf ↦ ht' f hf

/-- A presheaf of sets is a sheaf for a Grothendieck topology `J` if and only if, for every
covering sieve `S` on every object `U`, the map `P(U) → P(S)` is bijective. -/
theorem isSheaf_iff_bijective_toSieveCompatible (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) :
    IsSheaf J P ↔ ∀ (U : C) (S : Sieve U), S ∈ J U →
      Function.Bijective (Sieve.toSieveCompatible P S) :=
  forall_congr' fun _ ↦ forall_congr' fun S ↦ imp_congr_right fun _ ↦
    isSheafFor_iff_bijective_toSieveCompatible P S

end Presieve

namespace Presheaf

/-- A presheaf of abelian groups is a sheaf if and only if its underlying presheaf of sets is a
sheaf. Unlike `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, no relation between the
universe of the groups and those of the site is required. -/
theorem isSheaf_iff_isSheaf_forget_addCommGrpCat (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    IsSheaf J P ↔ Presieve.IsSheaf J (P ⋙ forget AddCommGrpCat) := by
  refine ⟨fun h ↦ ?_, Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget J P⟩
  exact Presieve.isSheaf_iso J
    (Functor.isoWhiskerLeft P AddCommGrpCat.coyonedaObjIsoForget.{w})
    (h (AddCommGrpCat.of (ULift.{w} ℤ)))

end Presheaf

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **Sheaves via covering sieves** [FK, I.2]. A presheaf of sets `F` on the small étale site of
`X` is a sheaf if and only if, for every object `U` and every covering sieve `S` on `U`, the map
`F(U) → F(S)` to the sieve-compatible families on `S` is bijective. -/
@[weil "lem_fk102_sheaf_iff_sieve_condition"]
theorem isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible
    (F : X.Etaleᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf X.smallEtaleTopology F ↔ ∀ (U : X.Etale) (S : Sieve U),
      S ∈ X.smallEtaleTopology U → Function.Bijective (Sieve.toSieveCompatible F S) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_iff_bijective_toSieveCompatible _ F

/-- **Sheaves via covering sieves**, abelian groups [FK, I.2]. A presheaf of abelian groups `F`
on the small étale site of `X` is a sheaf if and only if, for every object `U` and every covering
sieve `S` on `U`, the map `F(U) → F(S)` to the sieve-compatible families on `S` is bijective. -/
@[weil "lem_fk102_sheaf_iff_sieve_condition"]
theorem isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible_addCommGrpCat
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Presheaf.IsSheaf X.smallEtaleTopology F ↔ ∀ (U : X.Etale) (S : Sieve U),
      S ∈ X.smallEtaleTopology U →
        Function.Bijective
          (Sieve.toSieveCompatible (F ⋙ CategoryTheory.forget AddCommGrpCat) S) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget_addCommGrpCat]
  exact Presieve.isSheaf_iff_bijective_toSieveCompatible _ _

end AlgebraicGeometry.Scheme

end
