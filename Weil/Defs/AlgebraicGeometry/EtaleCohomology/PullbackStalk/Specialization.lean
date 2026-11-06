module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import Weil.Attr

/-!
# The étale neighbourhood induced by a specialization of geometric points

Let `S` be a scheme, `s` a geometric point of `S`, and `σ` a geometric specialization of `s`:
a geometric point `a = σ.target` of `S` together with a lift `φ = σ.lift` of `a` to the strict
henselization `S_(s)` of `S` at `s`, over `S`. For a pointed étale neighbourhood `(U, u)` of `s`
let `π_U : S_(s) ⟶ U` be the canonical morphism over `S` carrying the canonical geometric point
of `S_(s)` to `u`. Then `(U, φ ≫ π_U)` is a pointed étale neighbourhood of `a`, the *étale
neighbourhood of `a` induced by `(U, u)` and `σ`*. This construction is functorial in `(U, u)`,
and it is the functor of neighbourhoods along which the specialization map on stalks
`F_s ⟶ F_a` is the induced map of colimits.

## Main definitions

* `AlgebraicGeometry.GeometricSpecialization.inducedEtaleNeighborhood`: the étale
  neighbourhood `(U, φ ≫ π_U)` of the specialized point induced by `(U, u)`.
* `AlgebraicGeometry.GeometricSpecialization.inducedEtaleNeighborhoodFunctor`: the same
  construction as a functor of categories of pointed étale neighbourhoods.

## Main results

* `AlgebraicGeometry.GeometricSpecialization.inducedEtaleNeighborhood_fst`: the induced
  neighbourhood has the same underlying étale `S`-scheme.
* `AlgebraicGeometry.GeometricSpecialization.inducedEtaleNeighborhood_snd_coe`: its point is
  `φ ≫ π_U`.
* `AlgebraicGeometry.GeometricSpecialization.inducedEtaleNeighborhood_snd_coe_eq`: its point is
  `φ ≫ f` for every morphism `f : S_(s) ⟶ U` over `S` carrying the canonical geometric point
  to `u`, so `π_U` is characterised as in the source.

## Implementation notes

Following the conventions of the étale site used throughout, étale neighbourhoods of a
geometric point `s` are the elements of the geometric-point fiber functor
`geometricPointFiber B S hS s` on the small étale site `SmallEtale B S hS`, geometric points are
over algebraically closed fields, and the strict local scheme `S_(s)` is `strictHenselization`,
the spectrum of the étale local ring at `s`. The canonical morphism `π_U` is
`strictHenselizationEtaleFactor`, the factorisation provided by the initiality of the strict
henselization among pointed pro-étale neighbourhoods; the source instead obtains it from the
maps `Γ(U', 𝒪_{U'}) ⟶ 𝒪̃_{X,s}` for affine opens `U' ⊆ U`, and the uniqueness statement
`inducedEtaleNeighborhood_snd_coe_eq` shows that the two descriptions agree. An `S`-morphism
`φ` from a geometric point to `S_(s)` lying over `a` is exactly a `GeometricSpecialization`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.8
* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace GeometricSpecialization

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : GeometricPoint S}

/-- The étale neighbourhood of the specialized geometric point `σ.target` induced by a pointed
étale neighbourhood `(U, u)` of `s`: the same étale `S`-scheme `U`, pointed by the lift of
`σ.target` to the strict henselization followed by the canonical morphism from the strict
henselization to `U`. -/
@[weil "def_fk108_specialization_map_neighborhood"]
def inducedEtaleNeighborhood (σ : GeometricSpecialization B S hS s)
    (e : (geometricPointFiber B S hS s).Elements) :
    (geometricPointFiber B S hS σ.target).Elements :=
  (CategoryOfElements.map (specializationFiberHom σ)).obj e

/-- The induced étale neighbourhoods, as a functor of categories of pointed étale
neighbourhoods. -/
abbrev inducedEtaleNeighborhoodFunctor (σ : GeometricSpecialization B S hS s) :
    (geometricPointFiber B S hS s).Elements ⥤ (geometricPointFiber B S hS σ.target).Elements :=
  CategoryOfElements.map (specializationFiberHom σ)

@[simp]
theorem inducedEtaleNeighborhoodFunctor_obj (σ : GeometricSpecialization B S hS s)
    (e : (geometricPointFiber B S hS s).Elements) :
    σ.inducedEtaleNeighborhoodFunctor.obj e = σ.inducedEtaleNeighborhood e :=
  rfl

/-- The induced étale neighbourhood has the same underlying étale `S`-scheme. -/
@[simp]
theorem inducedEtaleNeighborhood_fst (σ : GeometricSpecialization B S hS s)
    (e : (geometricPointFiber B S hS s).Elements) :
    (σ.inducedEtaleNeighborhood e).1 = e.1 :=
  rfl

/-- The point of the induced étale neighbourhood is the lift of the specialized point to the
strict henselization, followed by the canonical morphism `π_U`. -/
@[simp]
theorem inducedEtaleNeighborhood_snd_coe (σ : GeometricSpecialization B S hS s)
    (e : (geometricPointFiber B S hS s).Elements) :
    (σ.inducedEtaleNeighborhood e).2.1 =
      σ.lift ≫ strictHenselizationEtaleFactor B S hS s e.1 e.2 :=
  rfl

/-- The point of the induced étale neighbourhood is `σ.lift ≫ f` for any morphism `f` from the
strict henselization to `U` over `S` carrying the canonical geometric point to `u`. -/
theorem inducedEtaleNeighborhood_snd_coe_eq (σ : GeometricSpecialization B S hS s)
    (e : (geometricPointFiber B S hS s).Elements)
    (f : strictHenselization B S hS s ⟶ (SmallEtale.toScheme B S hS).obj e.1)
    (hf : f ≫ B.inclusion.map e.1.obj.hom = strictHenselizationToBase B S hS s)
    (hu : geometricPointToStrictHenselization B S hS s ≫ f = e.2.1) :
    (σ.inducedEtaleNeighborhood e).2.1 = σ.lift ≫ f := by
  rw [inducedEtaleNeighborhood_snd_coe,
    strictHenselizationEtaleFactor_unique B S hS s e.1 e.2 f hf hu]

/-- The specialization map on stalks sends the germ at an étale neighbourhood of `s` to the germ
at the induced étale neighbourhood of the specialized point. -/
theorem ι_comp_specializationMapOnStalks_eq_ι_inducedEtaleNeighborhood
    (σ : GeometricSpecialization B S hS s) {A : Type*} [Category A]
    [Limits.HasColimitsOfSize.{u, u} A] (F : (SmallEtale B S hS)ᵒᵖ ⥤ A)
    (e : (geometricPointFiber B S hS s).Elements) :
    Limits.colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F)
        (Opposite.op e) ≫ specializationMapOnStalks σ F =
      Limits.colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ F)
        (Opposite.op (σ.inducedEtaleNeighborhood e)) :=
  ι_comp_specializationMapOnStalks σ F e

end GeometricSpecialization

end AlgebraicGeometry
