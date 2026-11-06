module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import Weil.AlgebraicGeometry.Morphisms.EtaleMorphismQuasiFinite
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk

/-!
# Representable étale sheaves have finite stalks

Let `X` be a scheme and `Y ⟶ X` an étale morphism with `Y` quasi-compact over `X`. The stalk of
the sheaf `Ỹ = Hom_X(-, Y)` represented by `Y` at a geometric point `s : Spec Ω ⟶ X` is the set
of lifts `Spec Ω ⟶ Y` of `s`. A lift is a section of the geometric fibre `Y ×_X Spec Ω ⟶ Spec Ω`,
and such a section is determined by the point it hits, `Ω` being algebraically closed. The
geometric fibre is étale and quasi-compact over `Spec Ω`, so it has finitely many points. Hence
the stalk is finite. In particular every representable étale sheaf, represented by a noetherian
separated étale `X`-scheme, has finite stalks.

## Main results

* `AlgebraicGeometry.GeometricPoint.finite_lifts_of_etale`: the lifts of a geometric point along
  an étale quasi-compact morphism form a finite set.
* `AlgebraicGeometry.SmallEtale.finite_geometricPointFiber_obj`: the same for an object of the
  small étale site that is quasi-compact over the base.
* `AlgebraicGeometry.SmallEtale.hasFiniteStalks_representedSheaf`: the sheaf represented by an
  object quasi-compact over the base has finite stalks.
* `AlgebraicGeometry.SmallEtale.hasFiniteStalks_of_isRepresentableInEt`: every representable
  étale sheaf has finite stalks.

## Implementation notes

The stalk of a represented sheaf is identified with the set of lifts of the geometric point by
`AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso`; this replaces the source's
argument through étale neighbourhoods and connected components. The finiteness of the set of
lifts is proved through the geometric fibre rather than through residue field extensions: only
quasi-compactness of the representing object over the base is used, which holds for a noetherian
representing object.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

/-- The lifts `Spec Ω ⟶ Y` of a geometric point `s : Spec Ω ⟶ S` along an étale quasi-compact
morphism `f : Y ⟶ S` form a finite set. -/
theorem finite_lifts_of_etale {Y S : Scheme.{u}} (f : Y ⟶ S) [Etale f] [QuasiCompact f]
    (s : GeometricPoint S) : Finite {p : s.source ⟶ Y // p ≫ f = s.hom} := by
  have : LocallyQuasiFinite f := (locallyQuasiFinite_of_etale f).2
  let sec : {p : s.source ⟶ Y // p ≫ f = s.hom} → (s.source ⟶ pullback f s.hom) :=
    fun p ↦ pullback.lift p.1 (𝟙 s.source) (by simpa using p.2)
  have hsnd (p) : sec p ≫ pullback.snd f s.hom = 𝟙 _ := pullback.lift_snd _ _ _
  have hfst (p) : sec p ≫ pullback.fst f s.hom = p.1 := pullback.lift_fst _ _ _
  have hinj : Function.Injective
      (fun p ↦ sec p (IsLocalRing.closedPoint s.residueField)) := by
    intro a b hab
    have h : sec a = sec b :=
      ext_of_apply_closedPoint_eq (pullback.snd f s.hom) (hsnd a) (hsnd b) hab
    exact Subtype.ext (by rw [← hfst a, ← hfst b, h])
  have hfin : Finite ↥(pullback f s.hom) := by
    have h := (pullback.snd f s.hom).finite_preimage_singleton
      (IsLocalRing.closedPoint s.residueField)
    exact Set.finite_univ_iff.mp (h.subset fun x _ ↦ Subsingleton.elim _ _)
  exact Finite.of_injective _ hinj

end GeometricPoint

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The lifts of a geometric point of `X` to an object of the small étale site of `X` that is
quasi-compact over `X` form a finite set. -/
theorem finite_geometricPointFiber_obj (Y : SmallEtale B X hX)
    [QuasiCompact (B.inclusion.map Y.obj.hom)] (s : GeometricPoint X) :
    Finite ((geometricPointFiber B X hX s).obj Y) :=
  GeometricPoint.finite_lifts_of_etale (B.inclusion.map Y.obj.hom) s

/-- The sheaf `Ỹ` represented by an object `Y` of the small étale site of `X` that is
quasi-compact over `X` has finite stalks. -/
theorem hasFiniteStalks_representedSheaf (Y : SmallEtale B X hX)
    [QuasiCompact (B.inclusion.map Y.obj.hom)] : HasFiniteStalks (representedSheaf Y) :=
  fun s ↦
    haveI := finite_geometricPointFiber_obj Y s
    Finite.of_equiv _ ((smallEtaleYonedaCompEtaleStalkFunctorIso B X hX s).app Y).toEquiv.symm

/-- **Representable étale sheaves have finite stalks.** Every representable étale sheaf of sets
on `X` has finite stalks. -/
@[weil "lem_fk103_representable_sheaf_finite_stalks"]
theorem hasFiniteStalks_of_isRepresentableInEt (F : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hF : IsRepresentableInEt F.obj) : HasFiniteStalks F := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := hF
  have : IsNoetherian (B.inclusion.obj Y.obj.left) := hY.1
  have : QuasiCompact (B.inclusion.map Y.obj.hom) :=
    (Etale.locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact
      (B.inclusion.map Y.obj.hom)).2.2
  exact (hasFiniteStalks_representedSheaf Y).of_iso
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso (X := representedSheaf Y) (Y := F) e)

end SmallEtale

end AlgebraicGeometry

end

/-! ### The stalk of a represented sheaf is the geometric fibre -/

/-!
# The stalk of a represented sheaf is the geometric fibre

Let `S` be a scheme, `s` a geometric point of `S` and `Y` an object of the small étale site of
`S`. The map `ε_Y : Ỹ_s → Y(s)` from the stalk of the represented sheaf `Ỹ` to the set of lifts
of `s` to `Y`, sending the germ at `(U, u)` of `f : U ⟶ Y` to `u ≫ f`, is bijective. Its
inverse sends a lift `y` to the germ of the identity of `Y` at the étale neighbourhood
`(Y, y)`. Equivalently, every element of `Ỹ_s` is the germ of `𝟙 Y` at some `(Y, y)`, and two
germs of morphisms `f, f' : U ⟶ Y` at one neighbourhood `(U, u)` coincide exactly when
`u ≫ f = u ≫ f'`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.stalkToFiberEquiv`: the bijection `ε_Y : Ỹ_s ≃ Y(s)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.stalkToFiberEquiv_symm_apply`: the inverse of `ε_Y` sends
  `y` to the germ of `𝟙 Y` at `(Y, y)`.
* `AlgebraicGeometry.GeometricPoint.etaleStalkGerm_representedSheaf_eq_iff`: two germs of
  morphisms `f, f' : U ⟶ Y` at `(U, u)` coincide if and only if `u ≫ f = u ≫ f'`.

## Implementation notes

The bijectivity of `ε_Y` is that of a component of the natural isomorphism
`AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso`, which is the codensity theorem for
the fibre functor; the elementwise statements are deduced from it rather than from the
connected-component argument of the source. Geometric points take values in algebraically
closed fields and the étale site is `AlgebraicGeometry.SmallEtale`, following the Stacks
project.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GeometricPoint

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : GeometricPoint S)

/-- **The stalk of a represented sheaf is the geometric fibre.** The map
`ε_Y : Ỹ_s → Y(s)`, `f_{(U, u)} ↦ u ≫ f`, as a bijection. -/
@[weil "lem_fka1_fiber_equals_stalk"]
def stalkToFiberEquiv (Y : SmallEtale B S hS) :
    (etaleStalkFunctor.{u, u} B S hS s).obj (SmallEtale.representedSheaf Y) ≃
      (geometricPointFiber B S hS s).obj Y :=
  Equiv.ofBijective _ (bijective_stalkToFiberMap s Y)

@[simp]
theorem stalkToFiberEquiv_apply (Y : SmallEtale B S hS)
    (z : (etaleStalkFunctor.{u, u} B S hS s).obj (SmallEtale.representedSheaf Y)) :
    stalkToFiberEquiv s Y z = stalkToFiberMap s Y z :=
  rfl

/-- `ε_Y` sends the germ of `𝟙 Y` at the étale neighbourhood `(Y, y)` to `y`. -/
@[simp]
theorem stalkToFiberMap_etaleStalkGerm_id (Y : SmallEtale B S hS)
    (y : (geometricPointFiber B S hS s).obj Y) :
    stalkToFiberMap s Y
        (etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y)
          ((geometricPointFiber B S hS s).elementsMk Y y) (𝟙 Y)) = y := by
  rw [stalkToFiberMap_etaleStalkGerm]
  simp

/-- The inverse of `ε_Y` sends a lift `y` of `s` to `Y` to the germ of `𝟙 Y` at the étale
neighbourhood `(Y, y)`. -/
@[weil "lem_fka1_fiber_equals_stalk", simp]
theorem stalkToFiberEquiv_symm_apply (Y : SmallEtale B S hS)
    (y : (geometricPointFiber B S hS s).obj Y) :
    (stalkToFiberEquiv s Y).symm y =
      etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y)
        ((geometricPointFiber B S hS s).elementsMk Y y) (𝟙 Y) := by
  rw [Equiv.symm_apply_eq, stalkToFiberEquiv_apply, stalkToFiberMap_etaleStalkGerm_id]

/-- Two germs at an étale neighbourhood `(U, u)` of morphisms `f, f' : U ⟶ Y` coincide in the
stalk `Ỹ_s` if and only if `u ≫ f = u ≫ f'`. -/
@[weil "lem_fka1_fiber_equals_stalk"]
theorem etaleStalkGerm_representedSheaf_eq_iff (Y : SmallEtale B S hS)
    (U : (geometricPointFiber B S hS s).Elements) (f f' : U.1 ⟶ Y) :
    etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y) U f =
        etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y) U f' ↔
      (geometricPointFiber B S hS s).map f U.2 = (geometricPointFiber B S hS s).map f' U.2 := by
  rw [← stalkToFiberMap_etaleStalkGerm, ← stalkToFiberMap_etaleStalkGerm]
  exact (bijective_stalkToFiberMap s Y).injective.eq_iff.symm

end AlgebraicGeometry.GeometricPoint

end
