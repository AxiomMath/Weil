module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Weil.Attr

/-!
# The coincidence set of two sections is open

Let `F` be a presheaf of sets on the small étale site of a scheme `X`, let `U` be an object of
that site and let `α β ∈ F(U)`. The coincidence set `C(α, β) ⊆ U`, the set of points `u` such
that the germs of `α` and `β` agree at every geometric point of `U` over `u`, is open.

If the germs agree at one geometric point `ū` of `U`, then `α` and `β` have the same
restriction to some étale neighbourhood `g : V ⟶ U` of `ū`. The image `W` of `g` is open, as
`g` is étale, and contains the image of `ū`. Every geometric point of `U` lying over a point of
`W` lifts along `g`, since `g` is étale and the residue field of a geometric point is
algebraically closed, so the germs of `α` and `β` agree there too: `W ⊆ C(α, β)`. Since every
point of `U` has a geometric point over it, `C(α, β)` is a neighbourhood of each of its points.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isOpen_subset_germCoincidenceSet`: equal germs at one
  geometric point give an open neighbourhood of its image inside `C(α, β)`.
* `AlgebraicGeometry.SmallEtale.isOpen_germCoincidenceSet`: `C(α, β)` is open.

## Implementation notes

The sheaf condition is not used: the statement holds for every presheaf of sets on the small
étale site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry

/-- Every point of a scheme has a geometric point lying over it. -/
lemma GeometricPoint.exists_liesOver {S : Scheme.{u}} (x : S) :
    ∃ s : GeometricPoint S, s.LiesOver x :=
  ⟨{ residueField := AlgebraicClosure (S.residueField x)
     hom := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x)
        (AlgebraicClosure (S.residueField x)))) ≫ S.fromSpecResidueField x },
    Scheme.fromSpecResidueField_apply x _⟩

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}
  (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}] {U : SmallEtale B X hX}

/-- If the germs of two sections `α β ∈ F(U)` agree at one geometric point `ū` of `U`, then
the image of `ū` has an open neighbourhood in `U` contained in the coincidence set
`C(α, β)`. -/
theorem exists_isOpen_subset_germCoincidenceSet {α β : F.obj (op U)}
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U))
    (h : germ F α ū = germ F β ū) :
    ∃ W : Set ((SmallEtale.toScheme B X hX).obj U), IsOpen W ∧ ū.hom default ∈ W ∧
      W ⊆ germCoincidenceSet F α β := by
  obtain ⟨V, f, y, hy, hf⟩ :=
    ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_eq_iff'
      (P := F) U (geometricPointLift U ū) α β).1 h
  set g := (SmallEtale.toScheme B X hX).map f with hg_def
  have hgU : g ≫ B.inclusion.map U.obj.hom = B.inclusion.map V.obj.hom := by
    rw [hg_def, SmallEtale.toScheme_map_comp]
  have : Etale g := by
    have : Etale (g ≫ B.inclusion.map U.obj.hom) := by
      rw [hgU]
      exact V.property
    exact Etale.of_comp _ (B.inclusion.map U.obj.hom)
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  have hy' : y.1 ≫ g = ū.hom := congrArg Subtype.val hy
  refine ⟨Set.range g, g.isOpenMap.isOpen_range, ⟨y.1 default, ?_⟩, ?_⟩
  · rw [← hy']
    rfl
  · rintro _ ⟨v, rfl⟩ ū' hū'
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g ū'.hom v hū'.symm
    let y' : (geometricPointFiber B X hX (toBaseGeometricPoint U ū')).obj V :=
      ⟨l, by
        change l ≫ B.inclusion.map V.obj.hom = ū'.hom ≫ B.inclusion.map U.obj.hom
        rw [← hgU, ← Category.assoc, hl]⟩
    let Φ := geometricPointSitePoint B X hX (toBaseGeometricPoint U ū')
    have hlift : Φ.fiber.map f y' = geometricPointLift U ū' := Subtype.ext hl
    have key := Φ.toPresheafFiber_w_apply f y' F
    change Φ.toPresheafFiber U (geometricPointLift U ū') F α =
      Φ.toPresheafFiber U (geometricPointLift U ū') F β
    rw [← hlift, ← key, ← key, hf]

/-- **The coincidence set is open.** For a presheaf of sets `F` on the small étale site of `X`,
an object `U` and sections `α β ∈ F(U)`, the coincidence set `C(α, β)` is open in `U`. -/
@[weil "lem_fk103_sheaf_coincidence_locus_open"]
theorem isOpen_germCoincidenceSet (α β : F.obj (op U)) :
    IsOpen (germCoincidenceSet F α β) := by
  refine isOpen_iff_forall_mem_open.2 fun u hu ↦ ?_
  obtain ⟨ū, hū⟩ := GeometricPoint.exists_liesOver u
  obtain ⟨W, hWo, hW, hWC⟩ :=
    exists_isOpen_subset_germCoincidenceSet F ū (hu ū hū)
  exact ⟨W, hWC, hWo, hū ▸ hW⟩

end SmallEtale

end AlgebraicGeometry

end
