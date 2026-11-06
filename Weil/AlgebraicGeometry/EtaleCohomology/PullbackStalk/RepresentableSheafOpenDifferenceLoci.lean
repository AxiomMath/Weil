module

public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Weil.Attr

/-!
# Representable étale sheaves have open difference loci

Let `Y` be an object of the small étale site of a scheme `X` whose structure morphism
`π : Y ⟶ X` is separated, and let `α β : U ⟶ Y` be two sections over `U` of the sheaf `Ỹ`
represented by `Y`. The diagonal `Δ : Y ⟶ Y ×_X Y` of the étale morphism `π` is an open
immersion, since `π` is unramified, and a closed immersion, since `π` is separated. The
coincidence set `C(α, β) ⊆ U` is the preimage of the image of `Δ` under `(α, β) : U ⟶ Y ×_X Y`:
if the germs of `α` and `β` agree at a geometric point `ū` then `α ∘ ū = β ∘ ū`, so `(α, β)`
sends the point under `ū` into the diagonal; conversely `α` and `β` agree on the open preimage
`W` of the diagonal, and every geometric point over a point of `W` factors through `W`.
Hence `C(α, β)` is closed (and open), that is, `Ỹ` has open difference loci. A presheaf
isomorphic to `Ỹ` for an object `Y` of `Et(X)` (noetherian and separated) inherits the property.

## Main results

* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_representedSheaf_eq_preimage`: the
  coincidence set of two sections of `Ỹ` is the preimage of the diagonal of `Y` over `X`.
* `AlgebraicGeometry.SmallEtale.hasOpenDifferenceLoci_representedSheaf`: for `Y` separated over
  `X`, the represented sheaf `Ỹ` has open difference loci.
* `AlgebraicGeometry.SmallEtale.IsRepresentableInEt.hasOpenDifferenceLoci`: every representable
  étale sheaf has open difference loci.

## Implementation notes

The source shows that `C(α, β)` is a union of connected components of `U` and uses that the
noetherian scheme `U` has finitely many of them. The objects `U` of the small étale site are
arbitrary étale `X`-schemes, whose connected components need not be open, so the diagonal
argument is used instead; it needs no finiteness hypothesis on `U`, and of the hypotheses on
`Y` only the separatedness of `Y ⟶ X`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The morphism `(α, β) : U ⟶ Y ×_X Y` of schemes defined by two morphisms `α β : U ⟶ Y` of
the small étale site of `X`. -/
noncomputable abbrev pairToPullback {U Y : SmallEtale B X hX} (α β : U ⟶ Y) :
    (SmallEtale.toScheme B X hX).obj U ⟶
      pullback (B.inclusion.map Y.obj.hom) (B.inclusion.map Y.obj.hom) :=
  pullback.lift ((SmallEtale.toScheme B X hX).map α) ((SmallEtale.toScheme B X hX).map β)
    ((SmallEtale.toScheme_map_comp B X hX α).trans (SmallEtale.toScheme_map_comp B X hX β).symm)

/-- **The coincidence set of two sections of a represented sheaf is the preimage of the
diagonal.** For `Y` étale and separated over `X` and `α β ∈ Ỹ(U) = Hom_X(U, Y)`, the coincidence
set `C(α, β)` is the preimage of the diagonal of `Y ×_X Y` under `(α, β)`. -/
theorem germCoincidenceSet_representedSheaf_eq_preimage {Y U : SmallEtale B X hX}
    [IsSeparated (B.inclusion.map Y.obj.hom)] (α β : (representedSheaf Y).obj.obj (op U)) :
    germCoincidenceSet (representedSheaf Y).obj α β =
      pairToPullback (show U ⟶ Y from α) (show U ⟶ Y from β) ⁻¹'
        Set.range (pullback.diagonal (B.inclusion.map Y.obj.hom)) := by
  set π := B.inclusion.map Y.obj.hom
  have : Etale π := Y.property
  set a : U ⟶ Y := α
  set b : U ⟶ Y := β
  set f := (SmallEtale.toScheme B X hX).map a
  set g := (SmallEtale.toScheme B X hX).map b
  set p := pairToPullback a b
  have hpf : p ≫ pullback.fst π π = f := pullback.lift_fst _ _ _
  have hpg : p ≫ pullback.snd π π = g := pullback.lift_snd _ _ _
  ext u
  constructor
  · intro hu
    obtain ⟨ū, hū⟩ := GeometricPoint.exists_liesOver u
    obtain ⟨V, h, y, hy, hh⟩ :=
      ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_eq_iff'
        (P := (representedSheaf Y).obj) U (geometricPointLift U ū) α β).1 (hu ū hū)
    have hy' : y.1 ≫ (SmallEtale.toScheme B X hX).map h = ū.hom := congrArg Subtype.val hy
    have hh' : h ≫ a = h ≫ b := hh
    have hfg : ū.hom ≫ f = ū.hom ≫ g := by
      rw [← hy', Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hh']
    have hdiag : ū.hom ≫ p = (ū.hom ≫ f) ≫ pullback.diagonal π := by
      apply pullback.hom_ext
      · rw [Category.assoc, hpf, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, hpg, Category.assoc, pullback.diagonal_snd, Category.comp_id, hfg]
    refine ⟨(ū.hom ≫ f) (default : ū.source), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hdiag, Scheme.Hom.comp_apply]
    exact congrArg p hū
  · intro hu ū hū
    let W : ((SmallEtale.toScheme B X hX).obj U).Opens := p ⁻¹ᵁ (pullback.diagonal π).opensRange
    have huW : u ∈ W := hu
    have hWr : Set.range (W.ι ≫ p) ⊆ Set.range (pullback.diagonal π) := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    have hWfg : W.ι ≫ f = W.ι ≫ g := by
      have hl := IsOpenImmersion.lift_fac (pullback.diagonal π) (W.ι ≫ p) hWr
      have h1 := congrArg (· ≫ pullback.fst π π) hl
      have h2 := congrArg (· ≫ pullback.snd π π) hl
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, hpf, hpg,
        Category.comp_id] at h1 h2
      exact h1.symm.trans h2
    have hsub : Set.range ū.hom ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      obtain rfl : z = (default : ū.source) := Subsingleton.elim _ _
      rw [Scheme.Opens.range_ι]
      change ū.hom default ∈ W
      rw [hū]
      exact huW
    let l : ū.source ⟶ (W : Scheme) := IsOpenImmersion.lift W.ι ū.hom hsub
    have hl : l ≫ W.ι = ū.hom := IsOpenImmersion.lift_fac _ _ _
    let i := openObjectι B X hX U W
    have hi : (SmallEtale.toScheme B X hX).map i = W.ι := openObjectι_map B X hX U W
    let y : (geometricPointFiber B X hX (toBaseGeometricPoint U ū)).obj
        (openObject B X hX U W) :=
      ⟨l, by
        change l ≫ B.inclusion.map (openObject B X hX U W).obj.hom =
          ū.hom ≫ B.inclusion.map U.obj.hom
        rw [← SmallEtale.toScheme_map_comp B X hX i, hi, ← Category.assoc, hl]⟩
    refine ((geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber_eq_iff'
        (P := (representedSheaf Y).obj) U (geometricPointLift U ū) α β).2
      ⟨openObject B X hX U W, i, y, Subtype.ext ?_, ?_⟩
    · change l ≫ (SmallEtale.toScheme B X hX).map i = ū.hom
      rw [hi, hl]
    · change i ≫ a = i ≫ b
      apply (SmallEtale.toScheme B X hX).map_injective
      rw [Functor.map_comp, Functor.map_comp, hi]
      exact hWfg

/-- **The sheaf represented by a separated étale scheme has open difference loci.** -/
theorem hasOpenDifferenceLoci_representedSheaf (Y : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map Y.obj.hom)] :
    HasOpenDifferenceLoci (representedSheaf Y).obj := by
  refine HasOpenDifferenceLoci.of_isClosed fun U α β ↦ ?_
  rw [germCoincidenceSet_representedSheaf_eq_preimage]
  exact (pullback.diagonal (B.inclusion.map Y.obj.hom)).isClosedEmbedding.isClosed_range.preimage
    (pairToPullback _ _).continuous

/-- **Freitag–Kiehl I.3**: every representable étale sheaf has open difference loci. -/
@[weil "lem_fk103_representable_sheaf_open_difference_loci"]
theorem IsRepresentableInEt.hasOpenDifferenceLoci {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (hF : IsRepresentableInEt F) : HasOpenDifferenceLoci F := by
  obtain ⟨Y, ⟨-, hY⟩, ⟨e⟩⟩ := hF
  have : (B.inclusion.obj Y.obj.left).IsSeparated := hY
  exact HasOpenDifferenceLoci.of_injective e.inv
    (fun V ↦ (isIso_iff_bijective (e.inv.app V)).1 inferInstance |>.1)
    (hasOpenDifferenceLoci_representedSheaf Y)

end AlgebraicGeometry.SmallEtale

end
