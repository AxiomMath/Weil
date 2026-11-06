module

public import Weil.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheafCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Weil.Attr

/-!
# Torsion sheaves have enough injectives

Let `S` be a scheme. The abelian category `𝒯(S)` of torsion sheaves on the small étale site of
`S` is a Grothendieck abelian category, so it has enough injectives: every torsion sheaf is a
subsheaf of an injective object of `𝒯(S)`.

The proof has two parts, both of which hold more generally.

* A Serre class `P` of a Grothendieck abelian category `A` which is closed under filtered
  colimits is itself a Grothendieck abelian category. Filtered colimits in `P` are computed in
  `A`, so they are exact. If `G` is a separator of `A`, the quotients of `G` which satisfy `P`
  form a set of objects separating `P`: a morphism `g : G ⟶ X` to an object of `P` factors
  through its coimage, a quotient of `G` which is a subobject of `X`, hence lies in `P`.
* On any site, a filtered colimit of torsion abelian sheaves is a torsion abelian sheaf: it is the
  sheafification of the colimit of the underlying presheaves, and a section of that colimit comes
  from a section of one member of the diagram, which is locally annihilated by positive integers.

Abelian sheaves on the small étale site form a Grothendieck abelian category, and torsion sheaves
form a Serre class in it, so `𝒯(S)` is Grothendieck abelian, and has enough injectives by
Grothendieck's theorem `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`.

## Main results

* `CategoryTheory.ObjectProperty.isGrothendieckAbelian_fullSubcategory`: a Serre class closed
  under filtered colimits in a Grothendieck abelian category is Grothendieck abelian.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.isGrothendieckAbelian`: `𝒯(S)` is a
  Grothendieck abelian category.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.enoughInjectives`: `𝒯(S)` has enough
  injectives.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.exists_injective_mono_ι_map`: every torsion
  sheaf embeds, by a monomorphism of abelian sheaves, into an injective object of `𝒯(S)`.

## Implementation notes

Freitag and Kiehl deduce enough injectives from Grothendieck's theorem using a set of noetherian
(constructible) generators of `𝒯(S)`. Here the generating set is instead the set of torsion
quotients of a separator of the abelian sheaves, which needs no hypothesis on `S` and no theory of
constructible sheaves; only closure under filtered colimits is used, not under all colimits.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [A. Grothendieck, *Sur quelques points d'algèbre homologique*, Thm. 1.10.1][Grothendieck1957]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u v₁ u₁

namespace CategoryTheory.ObjectProperty

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] (P : ObjectProperty A)

/-- In a Grothendieck abelian category, the quotients of the separator which satisfy a property
`P` closed under subobjects separate the objects satisfying `P`. -/
theorem isSeparating_fullSubcategory_cokernel [IsGrothendieckAbelian.{w} A]
    [P.IsClosedUnderSubobjects] :
    ObjectProperty.IsSeparating (P := ObjectProperty.ofObj
      (fun K : {K : Subobject (separator A) // P (cokernel K.arrow)} ↦
        (⟨cokernel K.1.arrow, K.2⟩ : P.FullSubcategory))) := by
  intro X Y u v huv
  apply P.ι.map_injective
  refine (isSeparator_separator A).def _ _ fun g ↦ ?_
  let K : Subobject (separator A) := Subobject.mk (kernel.ι g)
  have hK : K.arrow ≫ g = 0 := by
    simp [K]
  let S : ShortComplex A := ShortComplex.mk K.arrow g hK
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have : kernel.lift S.g S.f S.zero = (Subobject.underlyingIso (kernel.ι g)).hom := by
      ext; simp [S, K]
    rw [this]; infer_instance
  have hmono : Mono (cokernel.desc K.arrow g hK) := hS.mono_cokernelDesc
  have hP : P (cokernel K.arrow) := P.prop_of_mono (cokernel.desc K.arrow g hK) X.property
  have := huv _ ⟨⟨K, hP⟩⟩ (ObjectProperty.homMk (cokernel.desc K.arrow g hK))
  have := congrArg (fun φ ↦ cokernel.π K.arrow ≫ φ.hom) this
  simpa using this

/-- **A Serre class closed under filtered colimits in a Grothendieck abelian category is a
Grothendieck abelian category.** -/
theorem isGrothendieckAbelian_fullSubcategory [IsGrothendieckAbelian.{w} A] [P.IsSerreClass]
    [hP : ∀ (J : Type w) [SmallCategory J] [IsFiltered J], P.IsClosedUnderColimitsOfShape J] :
    IsGrothendieckAbelian.{w} P.FullSubcategory := by
  have := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have : HasFilteredColimitsOfSize.{w, w} P.FullSubcategory :=
    ⟨fun J _ _ ↦ inferInstance⟩
  have : AB5OfSize.{w, w} P.FullSubcategory :=
    ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J P.ι⟩
  have : HasCoproducts.{w} P.FullSubcategory := hasCoproducts_of_finite_and_filtered
  let I := {K : Subobject (separator A) // P (cokernel K.arrow)}
  let f : I → P.FullSubcategory := fun K ↦ ⟨cokernel K.1.arrow, K.2⟩
  let e := equivShrink.{w} I
  have hsep : ObjectProperty.IsSeparating (ObjectProperty.ofObj (f ∘ e.symm)) := by
    refine ObjectProperty.IsSeparating.of_le (P.isSeparating_fullSubcategory_cokernel) ?_
    intro X hX
    obtain ⟨K⟩ := hX
    exact (ObjectProperty.ofObj_iff _ _).2
      ⟨e K, by rw [Function.comp_apply, Equiv.symm_apply_apply]⟩
  exact { hasSeparator := ⟨_, hsep.isSeparator_coproduct⟩ }

end CategoryTheory.ObjectProperty

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **A filtered colimit of locally torsion presheaves is locally torsion.** A section of the
colimit over `U` comes from a section over `U` of one member of the diagram, and the covering
sieve on which that section is annihilated works for its image. -/
private theorem isLocallyTorsion_colimit {K : Type w} [SmallCategory K] [IsFiltered K]
    (D : K ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w}) (hD : ∀ k, IsLocallyTorsion J (D.obj k)) :
    IsLocallyTorsion J (colimit D) := by
  intro U x
  have hc := isColimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U))
    (colimit.isColimit D)
  obtain ⟨k, y, rfl⟩ := Concrete.isColimit_exists_rep _ hc x
  obtain ⟨R, hR, hkill⟩ := hD k U y
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, hn, h⟩ := hkill V f hf
  refine ⟨n, hn, ?_⟩
  dsimp
  rw [← NatTrans.naturality_apply (colimit.ι D k) f.op y, ← _root_.map_nsmul, h, map_zero]

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A filtered colimit of torsion abelian sheaves is a torsion abelian sheaf.** The colimit is
the sheafification of the colimit of the underlying presheaves, which is locally torsion. -/
private instance isClosedUnderColimitsOfShape_torsionSheafProperty (K : Type w) [SmallCategory K]
    [IsFiltered K] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (torsionSheafProperty J : ObjectProperty (Sheaf J AddCommGrpCat.{w})) K where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    have hP := torsionSheafProperty_sheafify J (colimit (h.diag ⋙ sheafToPresheaf J _))
      (isLocallyTorsion_colimit J _ fun k ↦ h.prop_diag_obj k)
    exact torsionSheafProperty_of_iso J
      (IsColimit.coconePointUniqueUpToIso
        (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)) h.isColimit) hP

end Stacks.Torsion

namespace AlgebraicGeometry.SmallEtale.TorsionSheafCategory

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The category `𝒯(S)` of torsion sheaves is a Grothendieck abelian category.** -/
instance isGrothendieckAbelian : IsGrothendieckAbelian.{u} (TorsionSheafCategory B S hS) :=
  have (K : Type u) [SmallCategory K] [IsFiltered K] :
      (IsTorsionSheaf.{u} B S hS).IsClosedUnderColimitsOfShape K :=
    Stacks.Torsion.isClosedUnderColimitsOfShape_torsionSheafProperty _ K
  (IsTorsionSheaf.{u} B S hS).isGrothendieckAbelian_fullSubcategory (hP := this)

/-- **The category `𝒯(S)` of torsion sheaves has enough injectives.** -/
@[weil "lem_fk104_torsion_sheaves_enough_injectives"]
instance enoughInjectives : EnoughInjectives (TorsionSheafCategory B S hS) :=
  IsGrothendieckAbelian.enoughInjectives

/-- **Every torsion sheaf is a subsheaf of an injective object of `𝒯(S)`**: there is a morphism
to an injective object of `𝒯(S)` which is a monomorphism of abelian sheaves. -/
@[weil "lem_fk104_torsion_sheaves_enough_injectives"]
theorem exists_injective_mono_ι_map (F : TorsionSheafCategory B S hS) :
    ∃ (I : TorsionSheafCategory B S hS) (f : F ⟶ I), Injective I ∧ Mono ((ι B S hS).map f) :=
  ⟨Injective.under F, Injective.ι F, inferInstance, inferInstance⟩

end AlgebraicGeometry.SmallEtale.TorsionSheafCategory
