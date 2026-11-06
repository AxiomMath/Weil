module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Attr

/-!
# Sections of a represented sheaf agreeing at a geometric point

Let `Y` be a separated étale scheme over `S` and `α β : U ⟶ Y` two morphisms over `S`, that is,
two sections over `U` of the sheaf `Ỹ` represented by `Y` on the small étale site of `S`. If `α`
and `β` agree at a geometric point `ū` of `U`, then they agree on every connected scheme mapping
to `U` through the image point of `ū`; in particular they agree on the connected component `U₀`
of `U` containing that point, whenever it is open (for instance when `U` is locally noetherian).

The proof is the rigidity of morphisms into a separated unramified scheme (Stacks, Tag 024V):
two morphisms from a connected scheme to a separated unramified `S`-scheme which agree on the
spectrum of the residue field at one point coincide. A geometric point `Spec k ⟶ U` factors
through `Spec κ(u₀) ⟶ U`, and `Spec k ⟶ Spec κ(u₀)` is an epimorphism onto that factor since
the residue field embedding `κ(u₀) ⟶ k` is injective.

## Main results

* `AlgebraicGeometry.GeometricPoint.fromSpecResidueField_comp_eq_of_hom_comp_eq`: two morphisms
  agreeing at a geometric point agree on the spectrum of the residue field of its image point.
* `AlgebraicGeometry.Unramified.comp_eq_of_geometricPoint_comp_eq`: two morphisms into a
  separated unramified `S`-scheme agreeing at a geometric point agree on every connected scheme
  mapping through its image point.
* `AlgebraicGeometry.SmallEtale.representedSheaf_sections_eq_on_connectedComponent`: two
  sections of the sheaf represented by a separated étale `Y` agreeing at a geometric point of `U`
  agree on the connected component of `U` through it, when that component is open.
* `AlgebraicGeometry.SmallEtale.representedSheaf_sections_eq_on_connectedComponentOpens`:
  the same for `U` locally noetherian, where the component is the open subscheme
  `AlgebraicGeometry.Scheme.connectedComponentOpens`.

## Implementation notes

The objects of the étale site in the source are separated and noetherian étale schemes, while
`AlgebraicGeometry.SmallEtale` allows arbitrary étale schemes. The statement fails for
non-separated `Y` (the two sections of the affine line with doubled origin over the affine line
agree at every geometric point away from the origin), so separatedness of `Y` over `S` is a
hypothesis; of the noetherian condition only the openness of the connected component `U₀` is
used. The restriction `α|_{U₀}` is the composite of `α` with the open immersion `U₀ ⟶ U` of
schemes.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks Project, Tag 024V](https://stacks.math.columbia.edu/tag/024V)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {U Y : Scheme.{u}}

/-- Two morphisms agreeing at a geometric point `x` agree on `Spec κ(x₀)`, where `x₀` is the
image point of `x`. -/
theorem fromSpecResidueField_comp_eq_of_hom_comp_eq (x : GeometricPoint U) {f g : U ⟶ Y}
    (h : x.hom ≫ f = x.hom ≫ g) :
    U.fromSpecResidueField x.point ≫ f = U.fromSpecResidueField x.point ≫ g := by
  set φ := x.pointResidueFieldHom
  have key : ∀ k : U ⟶ Y, x.hom ≫ k = (Scheme.SpecToEquivOfField x.residueField Y).symm
      ⟨k x.point, k.residueFieldMap x.point ≫ φ⟩ := by
    intro k
    rw [← x.map_pointResidueFieldHom_comp_fromSpecResidueField]
    change _ = Spec.map (k.residueFieldMap x.point ≫ φ) ≫ Y.fromSpecResidueField (k x.point)
    simp only [Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rfl
  rw [key f, key g] at h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    ((Scheme.SpecToEquivOfField x.residueField Y).symm.injective h)
  have hinj : Function.Injective φ.hom := x.pointResidueFieldHom_injective
  have hκ : f.residueFieldMap x.point =
      (Y.residueFieldCongr e).hom ≫ g.residueFieldMap x.point := by
    ext a
    apply hinj
    have := congrArg (fun m => m.hom a) he
    simpa [Category.assoc] using this
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField,
    ← g.SpecMap_residueFieldMap_fromSpecResidueField, hκ, Spec.map_comp, Category.assoc,
    Y.residueFieldCongr_fromSpecResidueField e]

end GeometricPoint

namespace Unramified

/-- Two morphisms from a connected scheme into a separated unramified `S`-scheme, over `S`, which
agree on the spectrum of the residue field at one point, are equal. -/
theorem eq_of_fromSpecResidueField_comp_eq {S X W : Scheme.{u}} (π : X ⟶ S)
    [Unramified π] [IsSeparated π] [ConnectedSpace W] (f g : W ⟶ X) (hover : f ≫ π = g ≫ π)
    (w : W) (h : W.fromSpecResidueField w ≫ f = W.fromSpecResidueField w ≫ g) : f = g := by
  let P := Limits.pullback π (f ≫ π)
  let p : P ⟶ W := Limits.pullback.snd π (f ≫ π)
  have : Unramified p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π (f ≫ π)) inferInstance
  have : IsSeparated p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π (f ≫ π)) inferInstance
  let sf : W ⟶ P := Limits.pullback.lift f (𝟙 W) (by simp)
  let sg : W ⟶ P := Limits.pullback.lift g (𝟙 W) (by simp [hover])
  have hsf : sf ≫ p = 𝟙 W := by rw [Limits.pullback.lift_snd]
  have hsg : sg ≫ p = 𝟙 W := by rw [Limits.pullback.lift_snd]
  have hpoint : sf w = sg w := by
    have hu : W.fromSpecResidueField w ≫ sf = W.fromSpecResidueField w ≫ sg := by
      apply Limits.pullback.hom_ext
      · simpa only [Category.assoc, sf, sg, Limits.pullback.lift_fst] using h
      · simp only [Category.assoc, sf, sg, Limits.pullback.lift_snd]
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
      congrArg (fun k : Spec (W.residueField w) ⟶ P => k (default : Spec (W.residueField w))) hu
  have hs : sf = sg :=
    section_eq_of_common_point p sf sg hsf hsg (sf w) w w rfl (by simp [hpoint])
  simpa only [sf, sg, Limits.pullback.lift_fst] using
    congrArg (fun k : W ⟶ P => k ≫ Limits.pullback.fst π (f ≫ π)) hs

/-- Two morphisms `f g : U ⟶ X` over `S` into a separated unramified `S`-scheme which agree at a
geometric point `x` of `U` agree on every connected scheme `W` mapping to `U` through the image
point of `x`. -/
theorem comp_eq_of_geometricPoint_comp_eq {S X U W : Scheme.{u}} (π : X ⟶ S)
    [Unramified π] [IsSeparated π] [ConnectedSpace W] {f g : U ⟶ X} (hover : f ≫ π = g ≫ π)
    (x : GeometricPoint U) (h : x.hom ≫ f = x.hom ≫ g) (j : W ⟶ U) (w : W)
    (hw : j w = x.point) : j ≫ f = j ≫ g := by
  have h₀ := x.fromSpecResidueField_comp_eq_of_hom_comp_eq h
  generalize x.point = u₀ at hw h₀
  subst hw
  refine eq_of_fromSpecResidueField_comp_eq π (j ≫ f) (j ≫ g) (by simp [hover]) w ?_
  rw [← Category.assoc, ← j.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc, h₀,
    ← Category.assoc, j.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]

end Unramified

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the small étale site commutes with the structure morphisms to `S`. -/
theorem toScheme_map_comp_inclusion_map_hom {U V : SmallEtale B S hS} (a : U ⟶ V) :
    (SmallEtale.toScheme B S hS).map a ≫ B.inclusion.map V.obj.hom =
      B.inclusion.map U.obj.hom :=
  ((B.inclusion.map_comp _ _).symm).trans
    (congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B S hS).map a)))

/-- **Sections of a represented sheaf agreeing at a geometric point agree on its connected
component.** Let `Y` be separated étale over `S`, `α β ∈ Ỹ(U) = Hom_S(U, Y)`, and `ū` a geometric
point of `U` with `α ∘ ū = β ∘ ū`. If the connected component `U₀` of `U` containing the image
point of `ū` is open, then `α|_{U₀} = β|_{U₀}`. -/
@[weil "lem_fk103_represented_sections_agree_on_component"]
theorem representedSheaf_sections_eq_on_connectedComponent {Y U : SmallEtale B S hS}
    [IsSeparated (B.inclusion.map Y.obj.hom)] (α β : (representedSheaf Y).obj.obj (op U))
    (u : GeometricPoint ((SmallEtale.toScheme B S hS).obj U))
    (h : u.hom ≫ (SmallEtale.toScheme B S hS).map (show U ⟶ Y from α) =
      u.hom ≫ (SmallEtale.toScheme B S hS).map (show U ⟶ Y from β))
    (U₀ : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hU₀ : (U₀ : Set ((SmallEtale.toScheme B S hS).obj U)) = connectedComponent u.point) :
    U₀.ι ≫ (SmallEtale.toScheme B S hS).map (show U ⟶ Y from α) =
      U₀.ι ≫ (SmallEtale.toScheme B S hS).map (show U ⟶ Y from β) := by
  have : Etale (B.inclusion.map Y.obj.hom) := Y.property
  have : ConnectedSpace U₀ :=
    isConnected_iff_connectedSpace.mp (hU₀ ▸ isConnected_connectedComponent)
  exact Unramified.comp_eq_of_geometricPoint_comp_eq (B.inclusion.map Y.obj.hom)
    ((toScheme_map_comp_inclusion_map_hom _).trans (toScheme_map_comp_inclusion_map_hom _).symm)
    u h U₀.ι ⟨u.point, show u.point ∈ (U₀ : Set _) from hU₀ ▸ mem_connectedComponent⟩ rfl

/-- **Sections of a represented sheaf agreeing at a geometric point agree on its connected
component**, for `U` locally noetherian: if `Y` is separated étale over `S`, `α β ∈ Ỹ(U)` and
`α ∘ ū = β ∘ ū` for a geometric point `ū` of `U`, then `α` and `β` agree on the open connected
component `U₀` of `U` containing the image point of `ū`. -/
@[weil "lem_fk103_represented_sections_agree_on_component"]
theorem representedSheaf_sections_eq_on_connectedComponentOpens
    {Y U : SmallEtale B S hS} [IsSeparated (B.inclusion.map Y.obj.hom)]
    [IsLocallyNoetherian ((SmallEtale.toScheme B S hS).obj U)]
    (α β : (representedSheaf Y).obj.obj (op U))
    (u : GeometricPoint ((SmallEtale.toScheme B S hS).obj U))
    (h : u.hom ≫ (SmallEtale.toScheme B S hS).map (show U ⟶ Y from α) =
      u.hom ≫ (SmallEtale.toScheme B S hS).map (show U ⟶ Y from β)) :
    (((SmallEtale.toScheme B S hS).obj U).connectedComponentOpens
        (ConnectedComponents.mk u.point)).ι ≫
        (SmallEtale.toScheme B S hS).map (show U ⟶ Y from α) =
      (((SmallEtale.toScheme B S hS).obj U).connectedComponentOpens
        (ConnectedComponents.mk u.point)).ι ≫
        (SmallEtale.toScheme B S hS).map (show U ⟶ Y from β) :=
  representedSheaf_sections_eq_on_connectedComponent α β u h _
    (connectedComponents_preimage_singleton)

end SmallEtale

end AlgebraicGeometry

end
