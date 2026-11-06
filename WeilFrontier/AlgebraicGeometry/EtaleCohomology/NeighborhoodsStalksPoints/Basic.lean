module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Geometric points: underlying point and residue field embedding

A geometric point of a scheme `S` is a morphism `x : Spec k ⟶ S` from the spectrum of an
algebraically closed field `k` (`AlgebraicGeometry.GeometricPoint`). Its underlying point
`x₀ ∈ S` is the image of the unique point of `Spec k`, and `x` induces a field embedding
`κ(x₀) ⟶ k` of the residue field. Conversely a point of `S` together with an embedding of its
residue field into an algebraically closed field determines a geometric point, and the two
constructions are mutually inverse.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.point`: the underlying point of a geometric point.
* `AlgebraicGeometry.GeometricPoint.pointResidueFieldHom`: the embedding `κ(x₀) ⟶ k` induced by a
  geometric point.
* `AlgebraicGeometry.GeometricPoint.ofResidueFieldHom`: the geometric point given by a point
  and an embedding of its residue field into an algebraically closed field.
* `AlgebraicGeometry.GeometricPoint.equivSigma`: geometric points of `S` correspond to triples
  of an algebraically closed field `k`, a point `x₀ ∈ S` and an embedding `κ(x₀) ⟶ k`.

## Main results

* `AlgebraicGeometry.GeometricPoint.pointResidueFieldHom_injective`: the induced map of residue
  fields is injective.
* `AlgebraicGeometry.GeometricPoint.map_pointResidueFieldHom_comp_fromSpecResidueField`: a geometric
  point factors as `Spec k ⟶ Spec κ(x₀) ⟶ S`.

## Implementation notes

Geometric points take values in algebraically closed fields, following the convention of the
Stacks project (Tag 03PO); the source allows separably closed fields. For an arbitrary field
`K`, the description of morphisms `Spec K ⟶ S` as pairs (point, embedding) is
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, from which everything here is derived.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
-/

/- FK allows separably closed fields in the definition of a geometric point; the Stacks project
convention (algebraically closed fields) is used, and the (point, embedding) description for any
field is Mathlib's `Scheme.SpecToEquivOfField`. -/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {S : Scheme.{u}}

/-- The underlying point of a geometric point: the image of the unique point of its source. -/
@[weil "def_fk102_geometric_point"]
def point (s : GeometricPoint S) : S :=
  (Scheme.SpecToEquivOfField s.residueField S s.hom).1

lemma point_eq_hom_closedPoint (s : GeometricPoint S) :
    s.point = s.hom (closedPoint s.residueField) :=
  rfl

lemma point_eq_hom_apply (s : GeometricPoint S) (t : s.source) : s.point = s.hom t := by
  rw [point_eq_hom_closedPoint]
  congr 1
  exact Subsingleton.elim _ _

lemma liesOver_point (s : GeometricPoint S) : s.LiesOver s.point :=
  (s.point_eq_hom_apply default).symm

lemma liesOver_iff (s : GeometricPoint S) (x : S) : s.LiesOver x ↔ s.point = x := by
  rw [GeometricPoint.LiesOver, ← s.point_eq_hom_apply]

/-- The embedding of the residue field of the underlying point into the field of values,
induced by a geometric point. -/
@[weil "def_fk102_geometric_point"]
def pointResidueFieldHom (s : GeometricPoint S) :
    S.residueField s.point ⟶ CommRingCat.of s.residueField :=
  (Scheme.SpecToEquivOfField s.residueField S s.hom).2

lemma pointResidueFieldHom_injective (s : GeometricPoint S) :
    Function.Injective s.pointResidueFieldHom.hom :=
  s.pointResidueFieldHom.hom.injective

lemma map_pointResidueFieldHom_comp_fromSpecResidueField (s : GeometricPoint S) :
    Spec.map s.pointResidueFieldHom ≫ S.fromSpecResidueField s.point = s.hom :=
  (Scheme.SpecToEquivOfField s.residueField S).left_inv s.hom

/-- The geometric point given by a point of `S` and an embedding of its residue field into an
algebraically closed field. -/
def ofResidueFieldHom (k : Type u) [Field k] [IsAlgClosed k] (x : S)
    (φ : S.residueField x ⟶ CommRingCat.of k) : GeometricPoint S where
  residueField := k
  hom := (Scheme.SpecToEquivOfField k S).symm ⟨x, φ⟩

@[simp]
lemma ofResidueFieldHom_residueField (k : Type u) [Field k] [IsAlgClosed k] (x : S)
    (φ : S.residueField x ⟶ CommRingCat.of k) : (ofResidueFieldHom k x φ).residueField = k :=
  rfl

@[simp]
lemma ofResidueFieldHom_hom (k : Type u) [Field k] [IsAlgClosed k] (x : S)
    (φ : S.residueField x ⟶ CommRingCat.of k) :
    (ofResidueFieldHom k x φ).hom = Spec.map φ ≫ S.fromSpecResidueField x :=
  rfl

lemma sigma_ofResidueFieldHom (k : Type u) [Field k] [IsAlgClosed k] (x : S)
    (φ : S.residueField x ⟶ CommRingCat.of k) :
    (⟨(ofResidueFieldHom k x φ).point, (ofResidueFieldHom k x φ).pointResidueFieldHom⟩ :
      Σ y : S, S.residueField y ⟶ CommRingCat.of k) = ⟨x, φ⟩ :=
  (Scheme.SpecToEquivOfField k S).right_inv ⟨x, φ⟩

@[simp]
lemma point_ofResidueFieldHom (k : Type u) [Field k] [IsAlgClosed k] (x : S)
    (φ : S.residueField x ⟶ CommRingCat.of k) : (ofResidueFieldHom k x φ).point = x :=
  congrArg Sigma.fst (sigma_ofResidueFieldHom k x φ)

lemma ofResidueFieldHom_point_pointResidueFieldHom (s : GeometricPoint S) :
    ofResidueFieldHom s.residueField s.point s.pointResidueFieldHom = s := by
  obtain ⟨k, hom⟩ := s
  change GeometricPoint.mk k ((Scheme.SpecToEquivOfField k S).symm
    ((Scheme.SpecToEquivOfField k S) hom)) = GeometricPoint.mk k hom
  rw [Equiv.symm_apply_apply]

/-- **Geometric points as (field, point, embedding).** A geometric point `Spec k ⟶ S` is the
same as an algebraically closed field `k`, a point `x₀ ∈ S` and an embedding `κ(x₀) ⟶ k`. -/
@[weil "def_fk102_geometric_point"]
def equivSigma :
    GeometricPoint S ≃ Σ (k : Type u) (_ : Field k), Σ' (_ : IsAlgClosed k),
      Σ x : S, S.residueField x ⟶ CommRingCat.of k where
  toFun s := ⟨s.residueField, s.field_residueField, s.isAlgClosed_residueField, s.point,
    s.pointResidueFieldHom⟩
  invFun p := @ofResidueFieldHom S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  left_inv s := ofResidueFieldHom_point_pointResidueFieldHom s
  right_inv := by
    rintro ⟨k, hk, hk', x, φ⟩
    exact congrArg (fun q => (⟨k, hk, hk', q⟩ : Σ (k : Type u) (_ : Field k),
      Σ' (_ : IsAlgClosed k), Σ x : S, S.residueField x ⟶ CommRingCat.of k))
      (sigma_ofResidueFieldHom k x φ)

@[simp]
lemma equivSigma_apply_fst (s : GeometricPoint S) : (equivSigma s).1 = s.residueField :=
  rfl

end GeometricPoint

end AlgebraicGeometry

end

/-! ### Morphisms out of connected étale neighbourhoods -/

/-!
# Morphisms out of connected étale neighbourhoods

Let `s` be a geometric point of a scheme `S`, and let `(U, u)`, `(V, v)` be étale
neighbourhoods of `s` with `U` connected and `V` separated over `S`. Then there is at most one
morphism of étale neighbourhoods `(U, u) ⟶ (V, v)`.

Indeed, for two such morphisms `f, g`, the diagonal `Δ : V ⟶ V ×_S V` is an open immersion
(`V ⟶ S` is unramified) and a closed immersion (`V ⟶ S` is separated), so the preimage of its
image under `(f, g) : U ⟶ V ×_S V` is open and closed in `U`. It contains the image of the
point of `U`, since `(f, g) ∘ u = Δ ∘ v`, hence is all of `U`; so `(f, g)` factors through `Δ`
and `f = g`.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.hom_ext_of_connectedSpace`: two morphisms
  of étale neighbourhoods `(U, u) ⟶ (V, v)` with `U` connected and `V` separated over the base
  are equal.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.subsingleton_hom_of_connectedSpace`: the
  same statement as a `Subsingleton` instance.

## Implementation notes

Freitag–Kiehl work with separated schemes throughout; here the separatedness of `V` over the
base is an explicit hypothesis. It cannot be dropped: the affine line with a doubled origin is
étale over the affine line, and its two open embeddings of the affine line are distinct
morphisms of étale neighbourhoods of any geometric point away from the origin.
The base is not assumed noetherian: the diagonal of an étale morphism is an open immersion
in general.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2, p. 26.
-/

/- FK's standing separatedness assumption
is the hypothesis `[IsSeparated V.toBase]`; the open-diagonal step uses Mathlib's instance for
formally unramified morphisms locally of finite type instead of
`etale_iff_isOpenImmersion_diagonal_of_flat`, so no noetherian hypothesis is needed. -/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {s : GeometricPoint S}

/-- Two morphisms of étale neighbourhoods `(U, u) ⟶ (V, v)` of a geometric point, with `U`
connected and `V` separated over the base, are equal. -/
@[weil "lem_fk102_connected_neighborhoods_at_most_one_morphism"]
theorem hom_ext_of_connectedSpace {U V : EtaleNeighborhood s} [ConnectedSpace U.scheme]
    [IsSeparated V.toBase] (f g : U ⟶ V) : f = g := by
  set Δ := pullback.diagonal V.toBase
  set φ : U.scheme ⟶ pullback V.toBase V.toBase := pullback.lift f.hom g.hom (by
    rw [f.over, g.over])
  have hφ : U.point ≫ φ = V.point ≫ Δ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id, f.point_comp]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id, g.point_comp]
  have hclopen : IsClopen (φ.base ⁻¹' Set.range Δ.base) :=
    ⟨Δ.isClosedEmbedding.isClosed_range.preimage φ.continuous,
      Δ.isOpenEmbedding.isOpen_range.preimage φ.continuous⟩
  have hmem : U.point.base default ∈ φ.base ⁻¹' Set.range Δ.base := by
    refine ⟨V.point.base default, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ, Scheme.Hom.comp_apply]
  have huniv : φ.base ⁻¹' Set.range Δ.base = Set.univ :=
    hclopen.eq_univ ⟨_, hmem⟩
  have hrange : Set.range φ.base ⊆ Set.range Δ.base := by
    rintro _ ⟨x, rfl⟩
    have : x ∈ φ.base ⁻¹' Set.range Δ.base := huniv ▸ Set.mem_univ x
    exact this
  have hfac := IsOpenImmersion.lift_fac Δ φ hrange
  apply Hom.ext
  have h1 : f.hom = IsOpenImmersion.lift Δ φ hrange := by
    have := congrArg (· ≫ pullback.fst V.toBase V.toBase) hfac
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at this
    exact this.symm
  have h2 : g.hom = IsOpenImmersion.lift Δ φ hrange := by
    have := congrArg (· ≫ pullback.snd V.toBase V.toBase) hfac
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at this
    exact this.symm
  rw [h1, h2]

/-- There is at most one morphism of étale neighbourhoods `(U, u) ⟶ (V, v)` of a geometric
point when `U` is connected and `V` is separated over the base. -/
@[weil "lem_fk102_connected_neighborhoods_at_most_one_morphism"]
instance subsingleton_hom_of_connectedSpace {U V : EtaleNeighborhood s}
    [ConnectedSpace U.scheme] [IsSeparated V.toBase] : Subsingleton (U ⟶ V) :=
  ⟨hom_ext_of_connectedSpace⟩

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry

end
