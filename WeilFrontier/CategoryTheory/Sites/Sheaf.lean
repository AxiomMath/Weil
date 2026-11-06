module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.AffineEtale

/-!
# Global sections on the étale category are left exact

Let `A` be a commutative ring. The identity of `Spec A` is étale, so `A` itself is an object of
the étale category `Et(A)`. The functor `Γ : 𝓕 ↦ 𝓕(A)` from sheaves of abelian groups on `Et(A)`
to abelian groups is left exact: it is the composite of the inclusion of sheaves into presheaves
and evaluation at `A`, both of which preserve finite limits. Concretely, for every exact sequence
`0 → 𝓕 → 𝓖 → 𝓗` of abelian sheaves on `Et(A)`, the sequence `0 → 𝓕(A) → 𝓖(A) → 𝓗(A)` is exact.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.self A`: the ring `A` as an object of `EtaleCategory A`,
  i.e. the identity of `Spec A` as an object of the affine étale site.

## Main results

- `AlgebraicGeometry.EtaleCategory.preservesFiniteLimits_sheafSections`: for every object `X` of
  `EtaleCategory A`, the sections functor `𝓕 ↦ 𝓕(X)` preserves finite limits.
- `AlgebraicGeometry.EtaleCategory.preservesFiniteLimits_sheafSections_self`: the global sections
  functor `𝓕 ↦ 𝓕(A)` on abelian sheaves is left exact.
- `AlgebraicGeometry.EtaleCategory.mono_and_exact_sheafSections_self`: the global sections of an
  exact sequence `0 → 𝓕 → 𝓖 → 𝓗` of abelian sheaves form an exact sequence
  `0 → 𝓕(A) → 𝓖(A) → 𝓗(A)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace EtaleCategory

variable (A : CommRingCat.{u})

/-- The ring `A` as an object of its étale category: the identity of `Spec A`, which is
étale. -/
abbrev self : EtaleCategory A :=
  op (Scheme.AffineEtale.mk (𝟙 (Spec A)))

variable {A}

/-- For every object `X` of `Et(A)` and every category `C` with finite limits, the sections
functor `𝓕 ↦ 𝓕(X)` on `C`-valued sheaves on `Et(A)` preserves finite limits. -/
instance preservesFiniteLimits_sheafSections {C : Type*} [Category C] [HasFiniteLimits C]
    (X : EtaleCategory A) :
    PreservesFiniteLimits ((sheafSections (Scheme.AffineEtale.topology (Spec A)) C).obj X) :=
  preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation (J := Scheme.AffineEtale.topology (Spec A)) (A := C)
      (X := X.unop)).symm

variable (A)

/-- The global sections functor `Γ : 𝓕 ↦ 𝓕(A)` from sheaves of abelian groups on `Et(A)` to
abelian groups is left exact. -/
@[weil "lem_fk101_global_sections_left_exact"]
instance preservesFiniteLimits_sheafSections_self :
    PreservesFiniteLimits
      ((sheafSections (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}).obj (self A)) :=
  inferInstance

variable {A}

/-- For every exact sequence `0 → 𝓕 → 𝓖 → 𝓗` of sheaves of abelian groups on `Et(A)`, the
sequence of global sections `0 → 𝓕(A) → 𝓖(A) → 𝓗(A)` is exact. -/
@[weil "lem_fk101_global_sections_left_exact"]
theorem mono_and_exact_sheafSections_self
    (S : ShortComplex (Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}))
    (hS : S.Exact) [Mono S.f] :
    Mono (S.map ((sheafSections _ _).obj (self A))).f ∧
      (S.map ((sheafSections _ _).obj (self A))).Exact := by
  let Γ := (sheafSections (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}).obj (self A)
  exact ⟨inferInstanceAs (Mono (Γ.map S.f)),
    hS.map_of_mono_of_preservesKernel Γ inferInstance inferInstance⟩

end EtaleCategory

end AlgebraicGeometry
