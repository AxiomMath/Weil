module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant

/-!
# Locally constant sheaves on the small étale site

Let `S` be a scheme and let `𝒞` be the category of sets or of abelian groups. A sheaf `F` on the
small étale site of `S` with values in `𝒞` is *locally constant* if there are an étale covering
`(Uᵢ ⟶ S)_{i ∈ I}` and objects `Mᵢ` of `𝒞` such that `F|_{Uᵢ}` is isomorphic to the constant sheaf
`(Mᵢ)_{Uᵢ}` for every `i`.

This is Stacks' notion of a locally constant sheaf (Tag 093Q (2)),
`Stacks.ConstantSheaf.IsLocallyConstant`, on the small étale site
`AlgebraicGeometry.SmallEtale B S hS`, which asks for such a trivializing covering of *every*
object of the site. Since the site has the final object `S`, and a trivialization over `U`
restricts to a trivialization over any `V ⟶ U`, one covering of `S` suffices; this is the form of
the definition above.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsLocallyConstant`: a sheaf on the small étale site of `S` is
  locally constant.

## Main results

* `AlgebraicGeometry.SmallEtale.isLocallyConstant_iff_exists_cover`: a sheaf is locally constant
  if and only if there are objects `Uᵢ` of the small étale site whose structure morphisms
  `Uᵢ ⟶ S` are jointly surjective, together with isomorphisms of each restriction `F|_{Uᵢ}` with a
  constant sheaf.
* `AlgebraicGeometry.SmallEtale.IsFiniteLocallyConstant.isLocallyConstant`: a finite locally
  constant sheaf is locally constant.

## Implementation notes

The coefficient category is arbitrary; `Type` (sheaves of sets) and `AddCommGrpCat` (sheaves of
abelian groups) are the two cases of the source.

The restriction `F|_U` of a sheaf to an object `U` of the site is Mathlib's restriction to the
localized site, `CategoryTheory.GrothendieckTopology.overPullback`, and the constant sheaf on the
localized site is `CategoryTheory.constantSheaf`. The objects `Uᵢ` of the small étale site are
schemes étale over `S` below the size cutoff of the big étale site `B`; every scheme étale over
`S` is covered by such objects, so the restriction is harmless.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03RU](https://stacks.math.columbia.edu/tag/03RU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' u' u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {D : Type u'} [Category.{v'} D]
  [∀ U : SmallEtale B S hS, HasWeakSheafify ((topology B S hS).over U) D]

variable (B S hS) in
/-- **Locally constant sheaves.** A sheaf `F` on the small étale site of `S`, with values in a
category `D` (sets or abelian groups in the source), is *locally constant* if it is isomorphic,
étale locally on `S`, to constant sheaves. The form with one covering of `S` is
`AlgebraicGeometry.SmallEtale.isLocallyConstant_iff_exists_cover`. -/
@[weil "def_fka1_locally_constant_sheaf"]
abbrev IsLocallyConstant (F : Sheaf (topology B S hS) D) : Prop :=
  Stacks.ConstantSheaf.IsLocallyConstant (topology B S hS) F

/-- **Local constancy on one étale covering of `S`.** A sheaf on the small étale site of `S` is
locally constant if and only if there are objects `Uᵢ` of the site, whose structure morphisms
`Uᵢ ⟶ S` are jointly surjective, and objects `Mᵢ` with isomorphisms `(Mᵢ)_{Uᵢ} ≅ F|_{Uᵢ}`. -/
@[weil "def_fka1_locally_constant_sheaf"]
theorem isLocallyConstant_iff_exists_cover (F : Sheaf (topology B S hS) D) :
    IsLocallyConstant B S hS F ↔
      ∃ (I : Type (u + 1)) (U : I → SmallEtale B S hS),
        (∀ x : S, ∃ i, x ∈ Set.range (B.inclusion.map (U i).obj.hom)) ∧
        ∀ i, ∃ M : D, Nonempty
          ((constantSheaf ((topology B S hS).over (U i)) D).obj M ≅
            ((topology B S hS).overPullback D (U i)).obj F) := by
  constructor
  · intro h
    obtain ⟨I, X, f, hf, hc⟩ := h.exists_cover (final B S hS)
    refine ⟨I, X, fun x => ?_, fun i => ?_⟩
    · obtain ⟨E, hE, hle⟩ := exists_isCovering_sieve₀_le B S hS hf
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
    · obtain ⟨M, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant ((topology B S hS).over (X i))
        (((topology B S hS).overPullback D (X i)).obj F)
      exact ⟨M, ⟨e⟩⟩
  · rintro ⟨I, U, hU, hc⟩
    refine Stacks.ConstantSheaf.Localization.isLocallyConstant_of_isConstant_cover
      (topology B S hS) D (finalIsTerminal B S hS) F
      (f := fun i => (finalIsTerminal B S hS).from (U i)) ?_ fun i => ?_
    · refine mem_topology_of_jointlySurjective fun x => ?_
      obtain ⟨i, hi⟩ := hU x
      exact ⟨U i, _, Sieve.ofArrows_mk _ _ i, by rwa [toScheme_map_from_final]⟩
    · obtain ⟨M, ⟨e⟩⟩ := hc i
      exact Sheaf.isConstant_of_iso ((topology B S hS).over (U i)) e.symm

/-- A finite locally constant sheaf on the small étale site is locally constant. -/
theorem IsFiniteLocallyConstant.isLocallyConstant {FD : D → D → Type*} {CD : D → Type w}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
    {F : Sheaf (topology B S hS) D}
    (hF : IsFiniteLocallyConstant B S hS (FD := FD) (CD := CD) F) :
    IsLocallyConstant B S hS F :=
  have := hF
  inferInstance

end AlgebraicGeometry.SmallEtale
