module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Weil.Attr

/-!
# Coincidence sets of a presheaf with open difference loci are clopen

Let `F` be a presheaf of sets on the small étale site of a scheme `X`, let `U` be an object of
that site and let `α β ∈ F(U)`. The coincidence set `C(α, β) ⊆ U` is always open: if the germs
of `α` and `β` agree at a geometric point `ū` of `U`, then `α` and `β` agree on an étale
neighbourhood `V → U` of `ū`, whose image is an open neighbourhood of the image of `ū`, and
every geometric point of `U` over a point of that image lifts to `V`. If `F` has open difference
loci, the complement of `C(α, β)` is open as well, so `C(α, β)` is open and closed in `U`.

## Main results

* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.isClopen_germCoincidenceSet`: for a
  presheaf with open difference loci, every coincidence set `C(α, β)` is clopen.

## Implementation notes

The statement is made for presheaves of sets, which contains the case of an étale sheaf `F`
through its underlying presheaf; the sheaf condition is not used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.15
-/

/- the two private lemmas below duplicate
`AlgebraicGeometry.GeometricPoint.exists_liesOver` and
`AlgebraicGeometry.SmallEtale.isOpen_germCoincidenceSet` (FK's openness of the coincidence locus
of two sections), both in
`WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafCoincidenceLocusOpen`, which is
not imported here; they are kept private to avoid a name clash. -/

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- Every point of a scheme has a geometric point lying over it. -/
private lemma exists_geometricPoint_liesOver {S : Scheme.{u}} (x : S) :
    ∃ s : GeometricPoint S, s.LiesOver x :=
  ⟨{ residueField := AlgebraicClosure (S.residueField x)
     hom := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x)
        (AlgebraicClosure (S.residueField x)))) ≫ S.fromSpecResidueField x },
    Scheme.fromSpecResidueField_apply x _⟩

/-- The coincidence set of two sections of a presheaf on the small étale site is open. -/
private theorem isOpen_germCoincidenceSet' (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    {U : SmallEtale B X hX} (α β : F.obj (op U)) :
    IsOpen (germCoincidenceSet F α β) := by
  refine isOpen_iff_forall_mem_open.2 fun u hu ↦ ?_
  obtain ⟨ū, hū⟩ := exists_geometricPoint_liesOver u
  obtain ⟨V, f, y, hy, hf⟩ :=
    ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_eq_iff'
      (P := F) U (geometricPointLift U ū) α β).1 (hu ū hū)
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
  refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, ⟨y.1 default, ?_⟩⟩
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
  · rw [← hū, ← hy']
    rfl

public section

/-- **Coincidence sets are clopen.** If a presheaf of sets `F` on the small étale site of `X`
has open difference loci, then for every object `U` and all sections `α β ∈ F(U)` the
coincidence set `C(α, β)` is open and closed in `U`. -/
@[weil "lem_fk103_open_difference_loci_clopen"]
theorem HasOpenDifferenceLoci.isClopen_germCoincidenceSet
    {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} (hF : HasOpenDifferenceLoci F)
    {U : SmallEtale B X hX} (α β : F.obj (op U)) :
    IsClopen (germCoincidenceSet F α β) :=
  ⟨hF.isClosed α β, isOpen_germCoincidenceSet' F α β⟩

end

end AlgebraicGeometry.SmallEtale
