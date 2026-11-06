module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import Weil.Attr

/-!
# The specialization homomorphism is well defined and natural

Let `s` be a geometric point of a scheme `S` and `σ` a geometric specialization of `s`, with
specialized point `a = σ.target`. For a presheaf `G` on the small étale site of `S`, the
specialization homomorphism `sp : G_s ⟶ G_a` is characterised by its composites with the
canonical maps `G(U) ⟶ G_s`: at a pointed étale neighbourhood `(U, u)` of `s` the composite is
the canonical map `G(U) ⟶ G_a` at the induced étale neighbourhood of `a`. Such a morphism
exists and is unique, because the stalk `G_s` is the colimit of `G(U)` over the étale
neighbourhoods of `s`; and it is natural in `G`.

## Main results

* `AlgebraicGeometry.GeometricSpecialization.existsUnique_specializationMapOnStalks`: there is
  exactly one morphism `G_s ⟶ G_a` with the prescribed composites, namely
  `specializationMapOnStalks σ G`.
* `AlgebraicGeometry.GeometricSpecialization.specializationMapOnStalks_naturality`: for a
  morphism `u : G ⟶ G'` of presheaves, `sp ≫ u_a = u_s ≫ sp`.
* `AlgebraicGeometry.GeometricSpecialization.specializationMapOnStalks_comp_etaleStalkMap`: the
  same identity for a morphism of abelian sheaves, with the stalk maps `etaleStalkMap`.

## Implementation notes

The statements are made for presheaves with values in any category with small colimits; the
source's case is that of abelian sheaves, recovered in
`specializationMapOnStalks_comp_etaleStalkMap`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.8
* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

namespace GeometricSpecialization

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : GeometricPoint S}

/-- The specialization homomorphism exists and is unique: there is exactly one morphism
`G_s ⟶ G_a` whose composite with the canonical map `G(U) ⟶ G_s` at every pointed étale
neighbourhood `(U, u)` of `s` is the canonical map `G(U) ⟶ G_a` at the induced étale
neighbourhood of `a`, and it is `specializationMapOnStalks σ G`. -/
@[weil "lem_fk108_specialization_homomorphism_well_defined"]
theorem existsUnique_specializationMapOnStalks (σ : GeometricSpecialization B S hS s)
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (G : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    ∃! f : etaleStalk B S hS s G ⟶ etaleStalk B S hS σ.target G,
      ∀ e : (geometricPointFiber B S hS s).Elements,
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ G) (op e) ≫ f =
          colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ G)
            (op (σ.inducedEtaleNeighborhood e)) := by
  refine ⟨specializationMapOnStalks σ G,
    fun e => ι_comp_specializationMapOnStalks_eq_ι_inducedEtaleNeighborhood σ G e, ?_⟩
  intro f hf
  refine colimit.hom_ext fun e => ?_
  rw [hf e.unop, ι_comp_specializationMapOnStalks_eq_ι_inducedEtaleNeighborhood]

/-- A morphism `G_s ⟶ G_a` with the composites of the specialization homomorphism is the
specialization homomorphism. -/
theorem eq_specializationMapOnStalks (σ : GeometricSpecialization B S hS s)
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (G : (SmallEtale B S hS)ᵒᵖ ⥤ A)
    (f : etaleStalk B S hS s G ⟶ etaleStalk B S hS σ.target G)
    (hf : ∀ e : (geometricPointFiber B S hS s).Elements,
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ G) (op e) ≫ f =
          colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ G)
            (op (σ.inducedEtaleNeighborhood e))) :
    f = specializationMapOnStalks σ G :=
  (existsUnique_specializationMapOnStalks σ G).unique hf
    (fun e => ι_comp_specializationMapOnStalks_eq_ι_inducedEtaleNeighborhood σ G e)

/-- The specialization homomorphism is natural: for a morphism `u : G ⟶ G'` of presheaves on
the small étale site, `sp ≫ u_a = u_s ≫ sp`, where `u_s` and `u_a` are the induced maps of
stalks. -/
@[weil "lem_fk108_specialization_homomorphism_well_defined"]
theorem specializationMapOnStalks_naturality (σ : GeometricSpecialization B S hS s)
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    {G G' : (SmallEtale B S hS)ᵒᵖ ⥤ A} (α : G ⟶ G') :
    specializationMapOnStalks σ G ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op α) =
      colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B S hS s)).op α) ≫
        specializationMapOnStalks σ G' := by
  refine colimit.hom_ext fun e => ?_
  have h₁ := ι_comp_specializationMapOnStalks_eq_ι_inducedEtaleNeighborhood σ G e.unop
  have h₂ := ι_comp_specializationMapOnStalks_eq_ι_inducedEtaleNeighborhood σ G' e.unop
  erw [← Category.assoc, h₁, ι_colimMap, ← Category.assoc, ι_colimMap, Category.assoc, h₂]
  rfl

/-- Naturality of the specialization homomorphism for a morphism of abelian sheaves:
`sp ≫ u_a = u_s ≫ sp`, with the stalk maps `etaleStalkMap`. -/
theorem specializationMapOnStalks_comp_etaleStalkMap (σ : GeometricSpecialization B S hS s)
    {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}} (α : F ⟶ G) :
    specializationMapOnStalks σ F.obj ≫ etaleStalkMap B S hS σ.target α =
      etaleStalkMap B S hS s α ≫ specializationMapOnStalks σ G.obj :=
  specializationMapOnStalks_naturality σ α.hom

end GeometricSpecialization

end AlgebraicGeometry
