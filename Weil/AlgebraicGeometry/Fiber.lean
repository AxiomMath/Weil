module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.OpenImmersionFiber
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Points closed in their fibre form a detecting set

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. A point `x : X` is *closed in
its fibre* if `{x}` is closed in the subspace `f ⁻¹' {f x}`, equivalently if the corresponding
point of the scheme-theoretic fibre `f.fiber (f x)` is closed. The set of these points is
detecting: every nonempty closed subset of a scheme `V` étale over `X` contains a point mapping
to a point closed in its fibre.

The proof: given `h : V ⟶ X` étale, `Z ⊆ V` closed and nonempty, `z ∈ Z` and `s` the image of
`z` in `S`, the fibre of `V` over `s` is locally of finite type over the field `κ(s)`, hence a
Jacobson space, so the nonempty closed subset of it lying over `Z` contains a closed point `v`.
The induced morphism of fibres `V_s ⟶ X_s` is locally of finite type and `X_s` is Jacobson, so
it maps the closed point `v` to a closed point of `X_s`; this is the image of `v` in `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.closedInFiberPoints` — the set of points of `X` closed in their
  fibre under `f`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mem_closedInFiberPoints_iff_isClosed_asFiber` — a point is closed
  in its fibre iff it is a closed point of the scheme-theoretic fibre.
* `AlgebraicGeometry.Scheme.Hom.mem_closedInFiberPoints_of_isClosed` — the image under a
  morphism locally of finite type of a point closed in its fibre is closed in its fibre.
* `AlgebraicGeometry.Scheme.Hom.isDetecting_closedInFiberPoints` — for `f` locally of finite
  type, the points closed in their fibre form a detecting set, for all étale `X`-schemes.
* `AlgebraicGeometry.Scheme.Hom.smallEtale_isDetecting_closedInFiberPoints` — the same for the
  small étale site of `X`.

## Implementation notes

A morphism is finitely generated in the sense of Freitag–Kiehl exactly when it is locally of
finite type (`AlgebraicGeometry.LocallyOfFiniteType`). No quasi-compactness of the fibres is
needed: a scheme locally of finite type over a field is a Jacobson space, and a nonempty closed
subset of a Jacobson space contains a closed point.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The set of points of `X` that are closed in their fibre `f ⁻¹' {f x}` (with the subspace
topology). -/
def closedInFiberPoints : Set X :=
  {x | IsClosed ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))}

variable {f}

lemma mem_closedInFiberPoints_iff {x : X} :
    x ∈ f.closedInFiberPoints ↔ IsClosed ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) :=
  Iff.rfl

/-- A point lying over `s` is closed in its fibre iff it is closed in `f ⁻¹' {s}`. -/
lemma mem_closedInFiberPoints_iff_of_eq {x : X} {s : S} (hx : f x = s) :
    x ∈ f.closedInFiberPoints ↔ IsClosed ({⟨x, hx⟩} : Set (f ⁻¹' {s})) := by
  subst hx
  rfl

/-- A point is closed in its fibre iff it is a closed point of the scheme-theoretic fibre. -/
lemma mem_closedInFiberPoints_iff_isClosed_asFiber {x : X} :
    x ∈ f.closedInFiberPoints ↔ IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  rw [mem_closedInFiberPoints_iff, ← (f.fiberHomeo (f x)).isClosed_image, Set.image_singleton]
  have : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ :=
    Subtype.ext (f.fiberι_asFiber x)
  rw [this]

/-- A closed point of the scheme-theoretic fibre over `s` maps to a point closed in its
fibre. -/
lemma mem_closedInFiberPoints_of_isClosed_fiber {s : S} {w : f.fiber s}
    (hw : IsClosed ({w} : Set (f.fiber s))) : f.fiberι s w ∈ f.closedInFiberPoints := by
  have hws : f (f.fiberι s w) = s := ((f.fiberHomeo s) w).2
  rw [mem_closedInFiberPoints_iff_of_eq hws, ← (f.fiberHomeo s).symm.isClosed_image,
    Set.image_singleton]
  have : (f.fiberHomeo s).symm ⟨f.fiberι s w, hws⟩ = w :=
    (f.fiberHomeo s).symm_apply_eq.mpr (Subtype.ext rfl)
  rwa [this]

instance locallyOfFiniteType_fiberMapOfComp {V : Scheme.{u}} (h : V ⟶ X) (s : S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType h] :
    LocallyOfFiniteType (fiberMapOfComp h f s) := by
  have : LocallyOfFiniteType (fiberMapOfComp h f s ≫ f.fiberToSpecResidueField s) := by
    rw [fiberMapOfComp_fiberToSpecResidueField]
    change LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  exact locallyOfFiniteType_of_comp _ (f.fiberToSpecResidueField s)

/-- Let `f : X ⟶ S` and `h : V ⟶ X` be locally of finite type, and let `v : V` be closed in the
fibre of `V` over `s : S`. Then `h v` is closed in the fibre of `X` over `s`. -/
lemma mem_closedInFiberPoints_of_isClosed [LocallyOfFiniteType f] {V : Scheme.{u}}
    (h : V ⟶ X) [LocallyOfFiniteType h] {s : S} {w : (h ≫ f).fiber s}
    (hw : IsClosed ({w} : Set ((h ≫ f).fiber s))) :
    h ((h ≫ f).fiberι s w) ∈ f.closedInFiberPoints := by
  have hw' := (fiberMapOfComp h f s).closePoints_subset_preimage_closedPoints hw
  have := mem_closedInFiberPoints_of_isClosed_fiber hw'
  rwa [← Scheme.Hom.comp_apply, fiberMapOfComp_fiberι, Scheme.Hom.comp_apply] at this

/-- **Points closed in their fibre are detecting.** For `f : X ⟶ S` locally of finite type, every
nonempty closed subset of a scheme étale over `X` contains a point whose image in `X` is closed
in its fibre under `f`. -/
theorem isDetecting_closedInFiberPoints [LocallyOfFiniteType f] :
    X.IsDetecting f.closedInFiberPoints := by
  intro V h _ Z hZ hne
  obtain ⟨z, hz⟩ := hne
  set g := h ≫ f
  let s := g z
  have hne' : ((g.fiberι s) ⁻¹' Z).Nonempty :=
    ⟨g.asFiber z, by simpa [s] using (g.fiberι_asFiber z).symm ▸ hz⟩
  obtain ⟨w, hwZ, hw⟩ := nonempty_inter_closedPoints hne'
    (hZ.preimage (g.fiberι s).continuous).isLocallyClosed
  exact ⟨g.fiberι s w, hwZ, mem_closedInFiberPoints_of_isClosed h hw⟩

/-- **Points closed in their fibre are detecting** for the small étale site of `X`: for
`f : X ⟶ S` locally of finite type, the set of points of `X` closed in their fibre under `f` is
detecting. -/
@[weil "lem_fk102_closed_in_fibre_points_detecting"]
theorem smallEtale_isDetecting_closedInFiberPoints [LocallyOfFiniteType f]
    (B : BigEtaleSite.{u}) (hX : B.Contains X) :
    SmallEtale.IsDetecting B X hX f.closedInFiberPoints :=
  isDetecting_closedInFiberPoints.smallEtale B hX

end Scheme.Hom

end AlgebraicGeometry
