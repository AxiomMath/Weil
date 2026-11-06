module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.SheafExactIffLocallyExact
public import WeilFrontier.CategoryTheory.Sites.Sheaf
public import WeilFrontier.RingTheory.Henselian.StrictlyHenselianEtaleSection

/-!
# Global sections over a strictly henselian local ring are exact

Let `A` be a strictly henselian local ring. The global sections functor `Γ : 𝓕 ↦ 𝓕(A)` from
sheaves of abelian groups on the étale category `Et(A)` to abelian groups is exact.

It is left exact for every ring. For right exactness, let `β : 𝓖 ⟶ 𝓗` be an epimorphism of
sheaves and `s ∈ 𝓗(A)`. Exactness of `𝓖 ⟶ 𝓗 ⟶ 0` is local for faithfully flat morphisms, so
there are a faithfully flat étale `A`-algebra `C` and `t ∈ 𝓖(C)` with `β(t) = s|_C`. Since `A` is
strictly henselian, `A → C` has an `A`-algebra retraction `ψ : C → A`, which is a morphism of
`Et(A)`; then `s = 𝓗(ψ)(s|_C) = β(𝓖(ψ)(t))`.

## Main results

- `AlgebraicGeometry.EtaleCategory.surjective_sheafSections_self_of_epi`: global sections of an
  epimorphism of abelian sheaves on `Et(A)` are surjective.
- `AlgebraicGeometry.EtaleCategory.preservesFiniteColimits_sheafSections_self`: the global
  sections functor preserves finite colimits.
- `AlgebraicGeometry.EtaleCategory.shortExact_map_sheafSections_self`: `Γ` takes short exact
  sequences of abelian sheaves to short exact sequences of abelian groups.

## Implementation notes

The source assumes `A` noetherian; the argument does not use it, and the results are stated
without it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Limits ZeroObject

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency.types false in
lemma structureMap_self_apply (a : A) : structureMap (self A) a = a := by
  have h : structureMap (self A) = 𝟙 _ :=
    Spec.map_injective ((spec_map_structureMap (self A)).trans (Spec.map_id A).symm)
  rw [h]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Over a strictly henselian local ring, every faithfully flat morphism `A ⟶ C` of `Et(A)`
out of `A` itself has a retraction in `Et(A)`. -/
lemma exists_comp_eq_id_of_faithfullyFlat [StrictlyHenselianLocalRing A] {C : EtaleCategory A}
    (g : self A ⟶ C) (hg : (ringHom g).hom.FaithfullyFlat) :
    ∃ ψ : C ⟶ self A, g ≫ ψ = 𝟙 (self A) := by
  have hφ : structureMap C = ringHom g := by
    ext a
    rw [← structureMap_comp_ringHom g, CommRingCat.comp_apply, structureMap_self_apply]
    rfl
  have he : (ringHom g).hom.Etale := hφ ▸ etale_structureMap C
  have : StrictlyHenselianLocalRing (self A).ring := ‹StrictlyHenselianLocalRing A›
  obtain ⟨ψ, hψ⟩ := RingHom.Etale.exists_comp_eq_id_of_faithfullyFlat hg he
  have h : structureMap C ≫ CommRingCat.ofHom ψ = structureMap (self A) := by
    rw [hφ]
    ext a
    rw [structureMap_self_apply]
    exact congr($hψ a)
  refine ⟨homMk (CommRingCat.ofHom ψ) h, hom_ext ?_⟩
  change ringHom g ≫ CommRingCat.ofHom ψ = 𝟙 _
  ext a
  exact congr($hψ a)

variable (A)

/-- Over a strictly henselian local ring `A`, the global sections `𝓖(A) → 𝓗(A)` of an
epimorphism `𝓖 ⟶ 𝓗` of sheaves of abelian groups on `Et(A)` are surjective. -/
@[weil "lem_fk101_strictly_henselian_global_sections_exact"]
theorem surjective_sheafSections_self_of_epi [StrictlyHenselianLocalRing A]
    {G H : Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}} (β : G ⟶ H)
    [Epi β] : Function.Surjective (β.hom.app (self A)) := by
  intro s
  have hex : (ShortComplex.mk β (0 : H ⟶ 0) comp_zero).Exact :=
    (ShortComplex.exact_iff_epi _ rfl).2 ‹_›
  obtain ⟨C, g, hg, t, ht⟩ :=
    (exact_iff_forall_exists_faithfullyFlat β (0 : H ⟶ 0) comp_zero).1 hex (self A) s
      (by simp)
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_id_of_faithfullyFlat g hg
  refine ⟨G.obj.map ψ t, ?_⟩
  have h1 := ConcreteCategory.congr_hom (β.hom.naturality ψ) t
  simp only [ConcreteCategory.comp_apply] at h1
  rw [h1, ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp, hψ, CategoryTheory.Functor.map_id]
  rfl

/-- Over a strictly henselian local ring `A`, the global sections functor `𝓕 ↦ 𝓕(A)` on
sheaves of abelian groups on `Et(A)` preserves finite colimits. Together with
`preservesFiniteLimits_sheafSections_self`, it is exact. -/
@[weil "lem_fk101_strictly_henselian_global_sections_exact"]
instance preservesFiniteColimits_sheafSections_self [StrictlyHenselianLocalRing A] :
    PreservesFiniteColimits
      ((sheafSections (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}).obj (self A)) := by
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  intro S hS
  have := hS.mono_f
  have := hS.epi_g
  refine ⟨(mono_and_exact_sheafSections_self S hS.exact).2, ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  exact surjective_sheafSections_self_of_epi A S.g

/-- Over a strictly henselian local ring `A`, the global sections functor `𝓕 ↦ 𝓕(A)` takes a
short exact sequence `0 → 𝓕' → 𝓕 → 𝓕'' → 0` of sheaves of abelian groups on `Et(A)` to a short
exact sequence `0 → 𝓕'(A) → 𝓕(A) → 𝓕''(A) → 0`. -/
@[weil "lem_fk101_strictly_henselian_global_sections_exact"]
theorem shortExact_map_sheafSections_self [StrictlyHenselianLocalRing A]
    {S : ShortComplex (Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u})}
    (hS : S.ShortExact) : (S.map ((sheafSections _ _).obj (self A))).ShortExact :=
  hS.map_of_exact _

end EtaleCategory

end AlgebraicGeometry
