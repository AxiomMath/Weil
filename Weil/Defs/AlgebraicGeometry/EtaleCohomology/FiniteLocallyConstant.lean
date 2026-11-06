module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import Weil.Defs.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Finite locally constant sheaves on the small étale site

Let `S` be a scheme and let `𝒞` be the category of sets or of abelian groups. A sheaf `F` on the
small étale site of `S` with values in `𝒞` is *finite locally constant* if there are an étale
covering `(Uᵢ ⟶ S)_{i ∈ I}` and finite objects `Mᵢ` of `𝒞` (finite sets, resp. finite abelian
groups) such that `F|_{Uᵢ}` is isomorphic to the constant sheaf `(Mᵢ)_{Uᵢ}` for every `i`.

This is Stacks' notion of a finite locally constant sheaf (Tag 093Q (3)),
`Stacks.ConstantSheaf.IsFiniteLocallyConstant`, on the small étale site
`AlgebraicGeometry.SmallEtale B S hS`, which asks for such a trivializing covering of *every*
object of the site. Since the site has the final object `S`, and a trivialization over `U`
restricts to a trivialization over any `V ⟶ U` with the same value, one covering of `S`
suffices; this is the form of the definition above.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsFiniteLocallyConstant`: a sheaf on the small étale site of `S`,
  with values in a concrete category, is finite locally constant.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_iff_exists_cover`: a sheaf is finite
  locally constant if and only if there are objects `Uᵢ` of the small étale site whose
  structure morphisms `Uᵢ ⟶ S` are jointly surjective, together with isomorphisms of each
  restriction `F|_{Uᵢ}` with a constant sheaf on a finite value.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_iff_exists_isEtaleCovering`: for a
  quasi-compact `S`, the same with a finite étale covering
  (`AlgebraicGeometry.Scheme.IsEtaleCovering`), which is the form of the definition for the
  noetherian schemes of [FK].

## Implementation notes

The coefficient category is an arbitrary concrete category; `Type u` (sheaves of sets) and
`AddCommGrpCat` (sheaves of abelian groups) are the two cases of the source, and a finite object
is one whose underlying type is finite.

The restriction `F|_U` of a sheaf to an object `U` of the site is Mathlib's restriction to the
localized site, `CategoryTheory.GrothendieckTopology.overPullback`, and the constant sheaf on the
localized site is `CategoryTheory.constantSheaf`. The objects `Uᵢ` of the small étale site are
schemes étale over `S` below the size cutoff of the big étale site `B`; every scheme étale over
`S` is covered by such objects, so the restriction is harmless.

In the source the coverings are finite families. Over a quasi-compact scheme every étale covering
has a finite subcovering, so the two definitions agree there; for a general scheme the definition
with arbitrary coverings is the standard one, and it is the one used here.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03RU](https://stacks.math.columbia.edu/tag/03RU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' u' u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  [∀ U : SmallEtale B S hS, HasWeakSheafify ((topology B S hS).over U) D]

variable (B S hS) in
/-- **Finite locally constant sheaves.** A sheaf `F` on the small étale site of `S`, with values
in a concrete category (sets or abelian groups in the source), is *finite locally constant* if it
is isomorphic, étale locally on `S`, to constant sheaves with finite values. The form with one
covering of `S` is `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_iff_exists_cover`. -/
@[weil "def_fk104_finite_locally_constant_sheaf"]
abbrev IsFiniteLocallyConstant (F : Sheaf (topology B S hS) D) : Prop :=
  Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD) (topology B S hS) F

/-- **Finite local constancy on one étale covering of `S`.** A sheaf on the small étale site of
`S` is finite locally constant if and only if there are objects `Uᵢ` of the site, whose structure
morphisms `Uᵢ ⟶ S` are jointly surjective, and finite objects `Mᵢ` with isomorphisms
`(Mᵢ)_{Uᵢ} ≅ F|_{Uᵢ}`. -/
@[weil "def_fk104_finite_locally_constant_sheaf"]
theorem isFiniteLocallyConstant_iff_exists_cover (F : Sheaf (topology B S hS) D) :
    IsFiniteLocallyConstant B S hS (FD := FD) (CD := CD) F ↔
      ∃ (I : Type (u + 1)) (U : I → SmallEtale B S hS),
        (∀ x : S, ∃ i, x ∈ Set.range (B.inclusion.map (U i).obj.hom)) ∧
        ∀ i, ∃ M : D, Finite (CD M) ∧ Nonempty
          ((constantSheaf ((topology B S hS).over (U i)) D).obj M ≅
            ((topology B S hS).overPullback D (U i)).obj F) := by
  constructor
  · intro h
    obtain ⟨I, X, f, hf, hc⟩ := h.exists_finite_cover (final B S hS)
    refine ⟨I, X, fun x => ?_, hc⟩
    obtain ⟨E, hE, hle⟩ := exists_isCovering_sieve₀_le B S hS hf
    obtain ⟨i, y, hy⟩ := jointlySurjective_of_isCovering B S hS hE x
    obtain ⟨j, a, ha⟩ := (Sieve.mem_ofArrows_iff X f (E.f i)).mp
      (hle _ (Sieve.ofArrows_mk _ _ i))
    have hx : x ∈ Set.range ((toScheme B S hS).map (f j)) := by
      refine ⟨(toScheme B S hS).map a y, ?_⟩
      rw [← hy]
      change _ = ((toScheme B S hS).map (E.f i)) y
      rw [ha, Functor.map_comp]
      rfl
    refine ⟨j, ?_⟩
    rwa [(finalIsTerminal B S hS).hom_ext (f j) ((finalIsTerminal B S hS).from (X j)),
      toScheme_map_from_final] at hx
  · rintro ⟨I, U, hU, hc⟩
    refine Stacks.ConstantSheaf.Localization.isFiniteLocallyConstant_of_finite_cover
      (topology B S hS) D (finalIsTerminal B S hS) F
      (f := fun i => (finalIsTerminal B S hS).from (U i)) ?_ hc
    refine mem_topology_of_jointlySurjective fun x => ?_
    obtain ⟨i, hi⟩ := hU x
    exact ⟨U i, _, Sieve.ofArrows_mk _ _ i, by rwa [toScheme_map_from_final]⟩

/-- **Finite local constancy on one finite étale covering of `S`.** For a quasi-compact `S`, a
sheaf on the small étale site of `S` is finite locally constant if and only if there are a finite
étale covering `(Uᵢ ⟶ S)_{i ∈ I}` by objects of the site and finite objects `Mᵢ` with isomorphisms
`(Mᵢ)_{Uᵢ} ≅ F|_{Uᵢ}`. -/
@[weil "def_fk104_finite_locally_constant_sheaf"]
theorem isFiniteLocallyConstant_iff_exists_isEtaleCovering [CompactSpace S]
    (F : Sheaf (topology B S hS) D) :
    IsFiniteLocallyConstant B S hS (FD := FD) (CD := CD) F ↔
      ∃ (I : Type (u + 1)) (U : I → SmallEtale B S hS),
        Scheme.IsEtaleCovering (U := S) (fun i => B.inclusion.map (U i).obj.hom) ∧
        ∀ i, ∃ M : D, Finite (CD M) ∧ Nonempty
          ((constantSheaf ((topology B S hS).over (U i)) D).obj M ≅
            ((topology B S hS).overPullback D (U i)).obj F) := by
  rw [isFiniteLocallyConstant_iff_exists_cover]
  constructor
  · rintro ⟨I, U, hU, hc⟩
    obtain ⟨s, hs⟩ := Scheme.exists_finite_isEtaleCovering (U := S)
      (φ := fun i => B.inclusion.map (U i).obj.hom)
      (Scheme.iUnion_range_eq_univ_iff.mpr hU)
    exact ⟨s, fun i => U i, hs, fun i => hc i⟩
  · rintro ⟨I, U, hU, hc⟩
    exact ⟨I, U, hU.exists_mem_range, hc⟩

end AlgebraicGeometry.SmallEtale
