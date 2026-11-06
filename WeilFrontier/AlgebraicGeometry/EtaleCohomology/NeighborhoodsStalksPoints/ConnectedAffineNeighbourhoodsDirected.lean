module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleNeighborhoodsFiltered
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# Connected affine étale neighbourhoods

Let `s` be a geometric point of a locally noetherian scheme `S`, and let `N(s)` be the category
of étale neighbourhoods of `s` (`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood`). The
étale neighbourhoods `(U, u)` with `U` connected and affine form a full subcategory `N₀(s)`
with the following properties:

* every étale neighbourhood of `s` receives a morphism from an object of `N₀(s)`;
* between two objects of `N₀(s)` there is at most one morphism;
* any two étale neighbourhoods of `s` (in particular any two objects of `N₀(s)`) receive
  morphisms from a common object of `N₀(s)`.

In particular `N₀(s)` is cofiltered, in fact a codirected preorder.

For the first point, let `y ∈ U` be the image of `u`, choose an affine open `U' ∋ y` and let
`U''` be the connected component of `U'` containing `y`. Since `U'` is locally noetherian, its
connected components are open, and a clopen subscheme of an affine scheme is affine; so `U''`
is a connected affine open subscheme of `U`, étale over `S`, through which `u` factors. The
second point holds because an affine scheme is separated, so its structure map to `S` is
separated, and a morphism of étale neighbourhoods out of a connected one into a separated one
is unique. The third point follows from the first, since `N(s)` is cofiltered.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.IsConnectedAffine`: the property of an
  étale neighbourhood of having a connected affine underlying scheme.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.exists_isConnectedAffine_hom`:
  cofinality of connected affine étale neighbourhoods.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.subsingleton_hom_of_isConnectedAffine`:
  at most one morphism between connected affine étale neighbourhoods.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.exists_isConnectedAffine_hom_hom`:
  any two étale neighbourhoods are dominated by a connected affine one.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.isCofiltered_isConnectedAffine`: the full
  subcategory of connected affine étale neighbourhoods is cofiltered.

## Implementation notes

The source assumes `S` noetherian and separated. Only local noetherianity of `S` is used (for
the open connected components); separatedness is not needed, since the structure map of an
affine scheme to any scheme is separated.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

/- FK's hypotheses "noetherian separated"
are generalised to `[IsLocallyNoetherian S]`; the directedness clause is stated for any two
étale neighbourhoods (FK: any two objects of `N_x`). -/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- An open subscheme of an affine scheme with clopen underlying set is affine: it is the basic
open set of an idempotent. -/
private lemma isAffine_toScheme_of_isClopen {Y : Scheme.{u}} [IsAffine Y] (U : Y.Opens)
    (hU : IsClopen (U : Set Y)) : IsAffine U.toScheme := by
  let e := Y.isoSpec
  let V := e.inv ⁻¹ᵁ U
  have hV : IsClopen (V.1 : Set (PrimeSpectrum Γ(Y, ⊤))) := hU.preimage e.inv.continuous
  obtain ⟨r, -, heq⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hV
  have hVeq : V = PrimeSpectrum.basicOpen r := TopologicalSpace.Opens.ext heq
  have hVaff : IsAffine V.toScheme := by
    rw [hVeq]
    exact IsAffineOpen.Spec_basicOpen r
  exact IsAffine.of_isIso (e.inv.preimageIso U).inv

namespace GeometricPoint

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {s : GeometricPoint S}

/-- An étale neighbourhood `(U, u)` is *connected affine* if the scheme `U` is connected and
affine. -/
def IsConnectedAffine : ObjectProperty (EtaleNeighborhood s) :=
  fun U => ConnectedSpace U.scheme ∧ IsAffine U.scheme

/-- **Cofinality.** Over a locally noetherian scheme, every étale neighbourhood of a geometric
point receives a morphism from a connected affine étale neighbourhood. -/
@[weil "lem_fk104_connected_affine_neighbourhoods_directed"]
theorem exists_isConnectedAffine_hom [IsLocallyNoetherian S] (U : EtaleNeighborhood s) :
    ∃ V : EtaleNeighborhood s, IsConnectedAffine V ∧ Nonempty (V ⟶ U) := by
  -- an affine open `U'` of `U` containing the image of the point
  obtain ⟨U', hU', hyU', -⟩ := exists_isAffineOpen_mem_and_subset
    (x := U.point.base default) (U := ⊤) trivial
  have : IsAffine U'.toScheme := hU'
  have : IsLocallyNoetherian U'.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U'.ι ≫ U.toBase)
  have : LocallyConnectedSpace U'.toScheme :=
    (isLocallyNoetherianSpace_of_isLocallyNoetherian U'.toScheme).locallyConnectedSpace _
  have hp : Set.range U.point.base ⊆ Set.range U'.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim t default]
    exact hyU'
  let p : s.source ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι U.point hp
  -- the connected component `C` of `U'` containing the image of the point
  let C : U'.toScheme.Opens := ⟨connectedComponent (p.base default), isOpen_connectedComponent⟩
  have : IsAffine C.toScheme := isAffine_toScheme_of_isClopen C isClopen_connectedComponent
  have : ConnectedSpace C.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hq : Set.range p.base ⊆ Set.range C.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim t default]
    exact mem_connectedComponent
  let q : s.source ⟶ C.toScheme := IsOpenImmersion.lift C.ι p hq
  have hqp : q ≫ C.ι ≫ U'.ι = U.point := by
    rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac]
  let V : EtaleNeighborhood s :=
    { scheme := C.toScheme
      toBase := C.ι ≫ U'.ι ≫ U.toBase
      point := q
      point_comp := by rw [← U.point_comp, ← hqp]; simp only [Category.assoc] }
  exact ⟨V, ⟨inferInstanceAs (ConnectedSpace C.toScheme), inferInstanceAs (IsAffine C.toScheme)⟩,
    ⟨homMk (U := V) (C.ι ≫ U'.ι) (Category.assoc _ _ _) hqp⟩⟩

/-- **Uniqueness.** Between two connected affine étale neighbourhoods of a geometric point
there is at most one morphism. -/
@[weil "lem_fk104_connected_affine_neighbourhoods_directed"]
theorem subsingleton_hom_of_isConnectedAffine {U V : EtaleNeighborhood s}
    (hU : IsConnectedAffine U) (hV : IsConnectedAffine V) : Subsingleton (U ⟶ V) := by
  have := hU.1
  have := hV.2
  infer_instance

/-- **Directedness.** Over a locally noetherian scheme, any two étale neighbourhoods of a
geometric point (in particular any two connected affine ones) receive morphisms from a common
connected affine étale neighbourhood. -/
@[weil "lem_fk104_connected_affine_neighbourhoods_directed"]
theorem exists_isConnectedAffine_hom_hom [IsLocallyNoetherian S] (U V : EtaleNeighborhood s) :
    ∃ W : EtaleNeighborhood s, IsConnectedAffine W ∧ Nonempty (W ⟶ U) ∧ Nonempty (W ⟶ V) := by
  obtain ⟨W, hW, ⟨f⟩⟩ := exists_isConnectedAffine_hom (IsCofiltered.min U V)
  exact ⟨W, hW, ⟨f ≫ IsCofiltered.minToLeft U V⟩, ⟨f ≫ IsCofiltered.minToRight U V⟩⟩

/-- Over a locally noetherian scheme, the full subcategory of connected affine étale
neighbourhoods of a geometric point is cofiltered. -/
instance isCofiltered_isConnectedAffine [IsLocallyNoetherian S] :
    IsCofiltered (IsConnectedAffine (s := s)).FullSubcategory where
  cone_objs U V := by
    obtain ⟨W, hW, ⟨f⟩, ⟨g⟩⟩ := exists_isConnectedAffine_hom_hom U.obj V.obj
    exact ⟨⟨W, hW⟩, ObjectProperty.homMk f, ObjectProperty.homMk g, trivial⟩
  cone_maps {U V} f g := by
    have := subsingleton_hom_of_isConnectedAffine U.property V.property
    exact ⟨U, 𝟙 U, ObjectProperty.hom_ext_iff.mpr (Subsingleton.elim _ _)⟩
  nonempty := by
    obtain ⟨U⟩ := (IsCofiltered.nonempty : Nonempty (EtaleNeighborhood s))
    obtain ⟨W, hW, -⟩ := exists_isConnectedAffine_hom U
    exact ⟨⟨W, hW⟩⟩

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry

end
