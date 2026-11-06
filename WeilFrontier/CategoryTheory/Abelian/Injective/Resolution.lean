module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import WeilFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Injective resolutions of abelian sheaves on the small étale site

Let `S` be a scheme. Every sheaf of abelian groups `F` on the small étale site of `S` has an
injective resolution: an exact sequence `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯` of abelian sheaves in which every
`Iᵏ` is injective. This holds because the category of abelian sheaves is abelian with enough
injectives (it is Grothendieck abelian), and in such a category every object has an injective
resolution.

## Main results

* `AlgebraicGeometry.SmallEtale.nonempty_injectiveResolution`: every abelian sheaf on the small
  étale site `SmallEtale B S hS` has an injective resolution.
* `AlgebraicGeometry.SmallEtale.injectiveResolution_exact_succ`: the resolution
  `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯` is exact at every `Iⁿ`, `n ≥ 1` (exactness at `F` and `I⁰` are
  `CategoryTheory.InjectiveResolution.exact₀` and the monomorphism `ι.f 0`).
* `AlgebraicGeometry.Scheme.nonempty_injectiveResolution_sheaf_smallEtaleTopology`: the same on
  the small étale site `S.Etale` with the topology `S.smallEtaleTopology`.

## Implementation notes

An injective resolution is Mathlib's `CategoryTheory.InjectiveResolution F`: a cochain complex
`I` indexed by `ℕ` of injective objects with a quasi-isomorphism from `F` placed in degree `0`;
this is equivalent to the exactness of `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯`. The inductive construction by
cokernels and monomorphisms into injectives is `CategoryTheory.InjectiveResolution.of`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §2.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every sheaf of abelian groups on the small étale site of `S` has an injective resolution
`0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯`. -/
@[weil "lem_fk102_etale_injective_resolution_exists"]
theorem nonempty_injectiveResolution (F : Sheaf (topology B S hS) AddCommGrpCat.{u}) :
    Nonempty (InjectiveResolution F) :=
  ⟨injectiveResolution F⟩

/-- The sequence `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯` of an injective resolution of an abelian sheaf on the
small étale site is exact at `Iⁿ⁺¹`. -/
theorem injectiveResolution_exact_succ {F : Sheaf (topology B S hS) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact :=
  I.exact_succ n

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Scheme

variable [UnivLE.{u, w}]

/-- Every sheaf of abelian groups on Mathlib's small étale site `S.Etale` of a scheme `S` has an
injective resolution `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯`. -/
theorem nonempty_injectiveResolution_sheaf_smallEtaleTopology (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{w}) :
    Nonempty (InjectiveResolution F) :=
  ⟨injectiveResolution F⟩

end AlgebraicGeometry.Scheme

end
