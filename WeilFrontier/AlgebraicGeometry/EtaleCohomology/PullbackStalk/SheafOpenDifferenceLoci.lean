module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Weil.Attr

/-!
# Subsheaves of sheaves with open difference loci

Let `G` be an étale sheaf of sets on a scheme `X` with open difference loci and let `H ⊆ G` be a
subsheaf. Then `H` has open difference loci. Indeed, for sections `α β ∈ H(U)` and a geometric
point `ū` of `U`, the map of stalks `H_{π ∘ ū} → G_{π ∘ ū}` is injective (a filtered colimit of
injections) and carries the germs of `α` and `β` in `H` to their germs in `G`. Hence the
coincidence sets `C(α, β)` formed in `H` and in `G` agree, and the difference locus is open by
the hypothesis on `G`.

## Main results

* `AlgebraicGeometry.SmallEtale.germ_map`: a morphism of presheaves carries germs to germs.
* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_map`: a locally injective morphism of
  presheaves preserves coincidence sets.
* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.of_isLocallyInjective`: the source of a
  locally injective morphism into a presheaf with open difference loci has open difference loci.
* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.of_mono`: a subsheaf of a sheaf with open
  difference loci has open difference loci.

## Implementation notes

A subsheaf `H ⊆ G` is a monomorphism `H ⟶ G` of sheaves. The result is proved more generally
for a locally injective morphism of presheaves `F ⟶ G`, which covers every injective morphism of
presheaves and every monomorphism of sheaves; the injectivity of the induced maps of stalks is
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_injective`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A morphism of presheaves `φ : F ⟶ G` carries the germ of `α` at `ū` to the germ of
`φ(α)` at `ū`. -/
lemma germ_map {F G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} (φ : F ⟶ G) {U : SmallEtale B X hX}
    (α : F.obj (op U)) (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) :
    (geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).presheafFiber.map φ
        (germ F α ū) = germ G (φ.app (op U) α) ū :=
  ConcreteCategory.congr_hom
    ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_naturality
      φ U (geometricPointLift U ū)) α

/-- A locally injective morphism of presheaves preserves coincidence sets. -/
lemma germCoincidenceSet_map {F G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) φ] {U : SmallEtale B X hX}
    (α β : F.obj (op U)) :
    germCoincidenceSet G (φ.app (op U) α) (φ.app (op U) β) = germCoincidenceSet F α β := by
  ext u
  refine forall_congr' fun ū ↦ imp_congr_right fun _ ↦ ?_
  rw [← germ_map, ← germ_map]
  exact ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_map_injective
    φ).eq_iff

/-- If `φ : F ⟶ G` is a locally injective morphism of presheaves (for instance an injective
one) and `G` has open difference loci, then so does `F`. -/
lemma HasOpenDifferenceLoci.of_isLocallyInjective {F G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (φ : F ⟶ G) [Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) φ]
    (hG : HasOpenDifferenceLoci G) : HasOpenDifferenceLoci F := fun U α β ↦ by
  rw [← germCoincidenceSet_map φ]
  exact hG U _ _

/-- A subpresheaf of a presheaf with open difference loci has open difference loci. -/
lemma HasOpenDifferenceLoci.of_injective {F G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} (φ : F ⟶ G)
    (hφ : ∀ U, Function.Injective (φ.app U)) (hG : HasOpenDifferenceLoci G) :
    HasOpenDifferenceLoci F :=
  have := Presheaf.isLocallyInjective_of_injective (SmallEtale.topology B X hX) φ hφ
  of_isLocallyInjective φ hG

/-- **Freitag–Kiehl I.3**: a subsheaf `H ⊆ G` (a monomorphism of étale sheaves of sets) of a
sheaf `G` with open difference loci has open difference loci. -/
@[weil "lem_fk103_open_difference_loci_subsheaf"]
lemma HasOpenDifferenceLoci.of_mono {H G : Sheaf (SmallEtale.topology B X hX) (Type u)}
    (φ : H ⟶ G) [Mono φ] (hG : HasOpenDifferenceLoci G.obj) : HasOpenDifferenceLoci H.obj :=
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  of_injective φ.hom (fun _ ↦ (mono_iff_injective _).1 inferInstance) hG

end AlgebraicGeometry.SmallEtale

end
