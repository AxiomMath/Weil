module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Weil.Attr

/-!
# The graph of an étale morphism into a separated scheme is open and closed

Let `j : X ⟶ Z` be an open immersion and `g : Z ⟶ Y` a separated morphism such that `j ≫ g` is
étale. For an étale `φ : U ⟶ X`, the graph `γ_φ = (𝟙 U, φ ≫ j) : U ⟶ U ×_Y Z` is a closed
immersion (graph of a morphism into a scheme separated over `Y`) and étale (a `Z`-morphism between
étale `Z`-schemes). A flat monomorphism locally of finite presentation is an open immersion, so
`γ_φ` is both an open and a closed immersion.

## Main results

* `AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_pullbackLift_id`: `γ_φ` is an open
  and a closed immersion.

## Implementation notes

The source assumes `Z` separated; only the separatedness of `g` is used.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 85.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory Limits

/-- The graph `(𝟙 U, φ ≫ j) : U ⟶ U ×_Y Z`, for any presentation `f` of the composite
`U ⟶ Y`, is an open and closed immersion. -/
theorem isOpenImmersion_and_isClosedImmersion_pullbackLift_id_of_eq {X Y Z U : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) [IsOpenImmersion j] [IsSeparated g] [Etale (j ≫ g)]
    (φ : U ⟶ X) [Etale φ] (f : U ⟶ Y) (hf : f = (φ ≫ j) ≫ g) (w : 𝟙 U ≫ f = (φ ≫ j) ≫ g) :
    IsOpenImmersion (pullback.lift (𝟙 U) (φ ≫ j) w : U ⟶ pullback f g) ∧
      IsClosedImmersion (pullback.lift (𝟙 U) (φ ≫ j) w : U ⟶ pullback f g) := by
  subst hf
  have : Etale ((φ ≫ j) ≫ g) := by rw [Category.assoc]; infer_instance
  have : Etale (pullback.lift (𝟙 U) (φ ≫ j) w ≫ pullback.snd ((φ ≫ j) ≫ g) g) := by
    rw [pullback.lift_snd]; infer_instance
  have : Etale (pullback.lift (𝟙 U) (φ ≫ j) w) :=
    Etale.of_comp _ (pullback.snd ((φ ≫ j) ≫ g) g)
  have : Mono (pullback.lift (𝟙 U) (φ ≫ j) w) :=
    mono_of_mono_fac (pullback.lift_fst (𝟙 U) (φ ≫ j) w)
  exact ⟨IsOpenImmersion.of_flat_of_mono _, inferInstance⟩

/-- For an open immersion `j : X ⟶ Z`, a separated `g : Z ⟶ Y` with `j ≫ g` étale, and an étale
`φ : U ⟶ X`, the graph `(𝟙 U, φ ≫ j) : U ⟶ U ×_Y Z` is an open and closed immersion. -/
@[weil "lem_fk108_graph_open_closed_embedding"]
theorem isOpenImmersion_and_isClosedImmersion_pullbackLift_id {X Y Z U : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) [IsOpenImmersion j] [IsSeparated g] [Etale (j ≫ g)]
    (φ : U ⟶ X) [Etale φ] :
    IsOpenImmersion (pullback.lift (𝟙 U) (φ ≫ j) (by simp) : U ⟶ pullback (φ ≫ j ≫ g) g) ∧
      IsClosedImmersion
        (pullback.lift (𝟙 U) (φ ≫ j) (by simp) : U ⟶ pullback (φ ≫ j ≫ g) g) :=
  isOpenImmersion_and_isClosedImmersion_pullbackLift_id_of_eq j g φ _
    (Category.assoc _ _ _).symm _

end AlgebraicGeometry
