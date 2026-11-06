module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant

/-!
# Finite locally constant abelian sheaves and specialization maps

Let `S` be a scheme and `F` an abelian sheaf on the small étale site of `S`. For a geometric
point `s` of `S` and a geometric specialization `σ` of `s` (a geometric point of the strict
henselization of `S` at `s`, with image `t` in `S`), the specialization map
`sp_σ : F_s ⟶ F_t` sends the germ of a section over an étale neighbourhood of `s` to its germ at
the induced étale neighbourhood of `t`. When every quasi-compact open of `S` has finitely many
irreducible components (for instance when `S` is locally noetherian), `F` is finite locally
constant if and only if every specialization map is an isomorphism and every stalk is finite.

The result is deduced from the case of sheaves of sets (Stacks, Tag 0GJ7): finite local
constancy of an abelian sheaf is a property of its underlying sheaf of sets, the underlying set
of a stalk is the stalk of the underlying sheaf of sets (stalks are filtered colimits, which the
forgetful functor preserves), and under these identifications the specialization maps agree.

## Main results

* `AlgebraicGeometry.isFiniteLocallyConstant_iff_isIso_specializationMapOnStalks_and_finite`:
  the criterion for a scheme whose quasi-compact opens have finitely many irreducible
  components.
* `isFiniteLocallyConstant_iff_isIso_specializationMapOnStalks_and_finite_of_isLocallyNoetherian`
  (in `AlgebraicGeometry`): the criterion for a locally noetherian scheme.

## Implementation notes

Abelian sheaves take values in `AddCommGrpCat.{u + 1}`, the universe of the sets-valued sheaves
of the small étale site `AlgebraicGeometry.SmallEtale B S hS` (whose objects live in
`Type (u + 1)`), so that the forgetful functor lands in the sheaves of sets of Tag 0GJ7.
Geometric points are over algebraically closed fields, and the specializations are
`AlgebraicGeometry.GeometricSpecialization`.

The source assumes `S` noetherian; the hypothesis used is only that quasi-compact opens have
finitely many irreducible components, which holds for locally noetherian schemes.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0GJ7](https://stacks.math.columbia.edu/tag/0GJ7)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace AlgebraicGeometry
variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

private instance preservesColimitsOfShape_forget_addCommGrpCat_elementsOp (s : GeometricPoint S) :
    PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget AddCommGrpCat.{u + 1}) := by
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1, u + 1, u + 1, u + 2, u + 2}
      (forget AddCommGrpCat.{u + 1})
  infer_instance

/-- The underlying set of the stalk of an abelian presheaf is the stalk of its underlying
presheaf of sets. -/
private noncomputable def forgetEtaleStalkIso (s : GeometricPoint S)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (forget AddCommGrpCat.{u + 1}).obj (etaleStalk B S hS s P) ≅
      etaleStalk B S hS s (P ⋙ forget AddCommGrpCat.{u + 1}) :=
  preservesColimitIso (forget AddCommGrpCat.{u + 1})
    ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P)

private theorem forgetEtaleStalkIso_inv_comp_map_specializationMapOnStalks {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (forgetEtaleStalkIso s P).inv ≫
        (forget AddCommGrpCat.{u + 1}).map (specializationMapOnStalks σ P) =
      specializationMapOnStalks σ (P ⋙ forget AddCommGrpCat.{u + 1}) ≫
        (forgetEtaleStalkIso σ.target P).inv := by
  apply colimit.hom_ext
  intro e
  have h1 := ι_comp_specializationMapOnStalks σ (P ⋙ forget AddCommGrpCat.{u + 1}) e.unop
  have h2 := ι_comp_specializationMapOnStalks σ P e.unop
  have h3 : colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P ⋙
      forget AddCommGrpCat.{u + 1}) e ≫ (forgetEtaleStalkIso s P).inv =
      (forget AddCommGrpCat.{u + 1}).map
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P) e) :=
    ι_preservesColimitIso_inv (forget AddCommGrpCat.{u + 1})
      ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P) e
  have h4 : colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ P ⋙
      forget AddCommGrpCat.{u + 1})
        (op ((CategoryOfElements.map (specializationFiberHom σ)).obj e.unop)) ≫
        (forgetEtaleStalkIso σ.target P).inv =
      (forget AddCommGrpCat.{u + 1}).map
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ P)
          (op ((CategoryOfElements.map (specializationFiberHom σ)).obj e.unop))) :=
    ι_preservesColimitIso_inv (forget AddCommGrpCat.{u + 1})
      ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ P) _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((congrArg (· ≫ (forget AddCommGrpCat.{u + 1}).map (specializationMapOnStalks σ P))
    h3).trans ?_)
  refine ((Functor.map_comp _ _ _).symm.trans ?_)
  refine ((congrArg (forget AddCommGrpCat.{u + 1}).map h2).trans ?_)
  refine h4.symm.trans ?_
  refine ((congrArg (· ≫ (forgetEtaleStalkIso σ.target P).inv) h1.symm).trans ?_)
  exact Category.assoc _ _ _

private theorem finite_etaleStalk_comp_forget_iff (s : GeometricPoint S)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Finite (etaleStalk B S hS s (P ⋙ forget AddCommGrpCat.{u + 1})) ↔
      Finite (ToType (etaleStalk B S hS s P)) :=
  ⟨fun _ => Finite.of_equiv _ (forgetEtaleStalkIso s P).toEquiv.symm,
    fun h => @Finite.of_equiv _ _ h (forgetEtaleStalkIso s P).toEquiv⟩

private theorem bijective_specializationMapOnStalks_comp_forget_iff {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Function.Bijective (specializationMapOnStalks σ (P ⋙ forget AddCommGrpCat.{u + 1})) ↔
      IsIso (specializationMapOnStalks σ P) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have h := forgetEtaleStalkIso_inv_comp_map_specializationMapOnStalks σ P
  have e₁ := (forgetEtaleStalkIso s P).toEquiv.symm.bijective
  have e₂ := (forgetEtaleStalkIso σ.target P).toEquiv.symm.bijective
  have hfun : (⇑(ConcreteCategory.hom (specializationMapOnStalks σ P))) ∘
      (forgetEtaleStalkIso s P).toEquiv.symm =
      (forgetEtaleStalkIso σ.target P).toEquiv.symm ∘
        specializationMapOnStalks σ (P ⋙ forget AddCommGrpCat.{u + 1}) := by
    funext x
    exact ConcreteCategory.congr_hom h x
  constructor
  · intro hb
    have : Function.Bijective ((forgetEtaleStalkIso σ.target P).toEquiv.symm ∘
        specializationMapOnStalks σ (P ⋙ forget AddCommGrpCat.{u + 1})) := e₂.comp hb
    rw [← hfun] at this
    exact (Function.Bijective.of_comp_iff _ e₁).mp this
  · intro hb
    have : Function.Bijective ((⇑(ConcreteCategory.hom (specializationMapOnStalks σ P))) ∘
        (forgetEtaleStalkIso s P).toEquiv.symm) := hb.comp e₁
    rw [hfun] at this
    exact (Function.Bijective.of_comp_iff' e₂ _).mp this

variable (B S hS) in
/-- **Finite local constancy of an abelian sheaf through its stalks.** Let `S` be a scheme every
quasi-compact open of which has finitely many irreducible components, and let `F` be an abelian
sheaf on the small étale site of `S`. Then `F` is finite locally constant if and only if every
specialization map `F_s ⟶ F_t` of its stalks is an isomorphism and every stalk `F_s` is
finite. -/
@[weil "lem_fk108_locally_constant_iff_specialization_iso"]
theorem isFiniteLocallyConstant_iff_isIso_specializationMapOnStalks_and_finite
    (hScomp : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    SmallEtale.IsFiniteLocallyConstant B S hS F ↔
      (∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
          IsIso (specializationMapOnStalks σ F.obj)) ∧
        ∀ s : GeometricPoint S, Finite (ToType (etaleStalk B S hS s F.obj)) := by
  rw [SmallEtale.IsFiniteLocallyConstant, Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_forget,
    isFiniteLocallyConstant_iff_finite_etaleStalk_and_bijective_specializationMap B S hS hScomp]
  change ((∀ s, Finite (etaleStalk B S hS s (F.obj ⋙ forget AddCommGrpCat.{u + 1}))) ∧
      ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s), Function.Bijective
        (specializationMapOnStalks σ (F.obj ⋙ forget AddCommGrpCat.{u + 1}))) ↔ _
  simp only [finite_etaleStalk_comp_forget_iff, bijective_specializationMapOnStalks_comp_forget_iff]
  exact and_comm

variable (B S hS) in
/-- **Finite local constancy of an abelian sheaf on a locally noetherian scheme through its
stalks.** An abelian sheaf `F` on the small étale site of a locally noetherian scheme `S` is
finite locally constant if and only if every specialization map `F_s ⟶ F_t` of its stalks is
an isomorphism and every stalk `F_s` is finite. -/
@[weil "lem_fk108_locally_constant_iff_specialization_iso"]
theorem
    isFiniteLocallyConstant_iff_isIso_specializationMapOnStalks_and_finite_of_isLocallyNoetherian
    [IsLocallyNoetherian S] (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    SmallEtale.IsFiniteLocallyConstant B S hS F ↔
      (∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
          IsIso (specializationMapOnStalks σ F.obj)) ∧
        ∀ s : GeometricPoint S, Finite (ToType (etaleStalk B S hS s F.obj)) := by
  refine isFiniteLocallyConstant_iff_isIso_specializationMapOnStalks_and_finite B S hS
    (fun V hV => ?_) F
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : IsNoetherian V.toScheme := (isNoetherian_iff _).mpr ⟨inferInstance, ‹_›⟩
  exact finite_irreducibleComponents_of_isNoetherian (X := V.toScheme)

end AlgebraicGeometry

end
