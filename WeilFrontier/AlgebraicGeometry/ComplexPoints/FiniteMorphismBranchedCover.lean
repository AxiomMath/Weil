/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.EtaleLocalHomeomorph
public import WeilFrontier.Topology.Covering.BranchedCover

/-!
# Finite morphisms induce branched covers on complex points

Let `f : C ⟶ C'` be a morphism of schemes over `ℂ`, and give the complex points the analytic
topology. A complex point `p : Spec ℂ ⟶ C` is determined by the image of the point of `Spec ℂ`:
on an affine open `U` containing it, the kernel of evaluation `Γ(C, U) → ℂ` at `p` is the prime
ideal of that image, and a ring homomorphism over `ℂ` to `ℂ` is determined by its kernel. Hence
if `f` is finite, the fibres of `f(ℂ) : C(ℂ) → C'(ℂ)` are finite, since the fibres of `f` are.

If moreover `C'` is locally of finite type over `ℂ` and `f` is étale on a neighbourhood of every
point outside a set `Z`, then `f(ℂ)` is a local homeomorphism at every complex point outside
`Z`, because étale morphisms induce local homeomorphisms on complex points. So `f(ℂ)` is a
finite branched cover whose branch locus is contained in the image of the complex points lying
over `Z`; this image is finite when `Z` is.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.pointsOver Z`: the complex points of `C` whose image
  lies in a set `Z` of points of `C`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.injective_hom_base`: a complex point is determined by
  its image point.
* `AlgebraicGeometry.Scheme.ComplexPoints.finite_pointsOver`: finitely many complex points lie
  over a finite set of points.
* `AlgebraicGeometry.Scheme.ComplexPoints.finite_preimage_singleton_map`: a finite morphism has
  finite fibres on complex points.
* `AlgebraicGeometry.Scheme.ComplexPoints.isLocalHomeomorphOn_map`: `f(ℂ)` is a local
  homeomorphism at the complex points over which `f` is étale on a neighbourhood.
* `AlgebraicGeometry.Scheme.ComplexPoints.isBranchedCover_map`: a finite morphism étale outside
  `Z` induces a branched cover with branch locus in `f(ℂ)(pointsOver Z)`.

## References

* [SGA1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exposé XII, §1.
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {C : Scheme.{0}} {c : C ⟶ Spec (.of ℂ)}

/-- **A complex point is determined by its image point.** -/
theorem injective_hom_base (x : Spec (.of ℂ)) :
    Function.Injective fun p : ComplexPoints c ↦ p.hom.base x := by
  intro p q hpq
  simp only at hpq
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens)
    (show p.hom.base x ∈ (⊤ : C.Opens) from trivial)
  have hp : p.Mem U := (mem_iff x).2 hxU
  have hq : q.Mem U := (mem_iff x).2 (hpq ▸ hxU)
  -- `eval g p = 0 ↔ eval g q = 0`, as both say that the image point is outside `D(g)`
  have hzero : ∀ g : Γ(C, U), eval g p hp = 0 ↔ eval g q hq = 0 := by
    intro g
    rw [← not_iff_not, ← ne_eq, ← ne_eq, ← mem_basicOpen_iff hp, ← mem_basicOpen_iff hq,
      mem_iff x, mem_iff x, hpq]
  refine eq_of_eval_eq hU hp hq fun g ↦ ?_
  have h0 : eval (g - constHom (y := c) U (eval g p hp)) p hp = 0 := by
    rw [← evalHom_apply, map_sub, evalHom_apply, evalHom_apply, eval_constHom, sub_self]
  rw [hzero, ← evalHom_apply, map_sub, evalHom_apply, evalHom_apply, eval_constHom,
    sub_eq_zero] at h0
  exact h0.symm

/-- The complex points of `C` whose image lies in a set `Z` of points of `C`. -/
def pointsOver (c : C ⟶ Spec (.of ℂ)) (Z : Set C) : Set (ComplexPoints c) :=
  {p | ∃ x, p.hom.base x ∈ Z}

theorem mem_pointsOver_iff {Z : Set C} {p : ComplexPoints c} (x : Spec (.of ℂ)) :
    p ∈ pointsOver c Z ↔ p.hom.base x ∈ Z := by
  have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  exact ⟨fun ⟨x', h⟩ ↦ Subsingleton.elim x' x ▸ h, fun h ↦ ⟨x, h⟩⟩

/-- **Finitely many complex points lie over a finite set of points.** -/
theorem finite_pointsOver {Z : Set C} (hZ : Z.Finite) : (pointsOver c Z).Finite := by
  obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have : pointsOver c Z = (fun p : ComplexPoints c ↦ p.hom.base x) ⁻¹' Z := by
    ext p; exact mem_pointsOver_iff x
  rw [this]
  exact hZ.preimage (injective_hom_base x).injOn

variable {C' : Scheme.{0}} {c' : C' ⟶ Spec (.of ℂ)}

/-- **A locally quasi-finite, quasi-compact morphism (for instance a finite one) has finite
fibres on complex points.** -/
theorem finite_preimage_singleton_map (f : C ⟶ C') [LocallyQuasiFinite f] [QuasiCompact f]
    (hf : f ≫ c' = c) (q : ComplexPoints c') : (map f hf ⁻¹' {q}).Finite := by
  obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  refine ((f.finite_preimage_singleton (q.hom.base x)).preimage
    (injective_hom_base (c := c) x).injOn).subset ?_
  rintro p rfl
  simp [map_hom]

/-- **`f(ℂ)` is a local homeomorphism at every complex point near which `f` is étale**, for `C'`
locally of finite type over `ℂ`. -/
theorem isLocalHomeomorphOn_map [LocallyOfFiniteType c'] (f : C ⟶ C') (hf : f ≫ c' = c)
    {s : Set (ComplexPoints c)}
    (hs : ∀ p ∈ s, ∃ (x : Spec (.of ℂ)) (U : C.Opens), p.hom.base x ∈ U ∧ Etale (U.ι ≫ f)) :
    IsLocalHomeomorphOn (map f hf) s := by
  intro p hp
  obtain ⟨x, U, hxU, hU⟩ := hs p hp
  have hι : U.ι ≫ c = U.ι ≫ c := rfl
  have hcomp : (U.ι ≫ f) ≫ c' = U.ι ≫ c := by rw [Category.assoc, hf]
  have he := isOpenEmbedding_map_of_isOpenImmersion U.ι hι
  have hg := isLocalHomeomorph_map_of_etale (U.ι ≫ f) hcomp
  have heq : map (U.ι ≫ f) hcomp = map f hf ∘ map U.ι hι := by
    funext p'; exact map_comp U.ι hι f hf p'
  rw [heq] at hg
  have hon := IsLocalHomeomorphOn.of_comp_right (s := Set.univ) hg.isLocalHomeomorphOn
    he.isLocalHomeomorph.isLocalHomeomorphOn
  rw [Set.image_univ, range_map_of_isOpenImmersion] at hon
  refine hon p ?_
  refine (mem_iff x).2 ?_
  simpa [Scheme.Opens.opensRange_ι] using hxU

/-- **A finite morphism étale outside `Z` induces a finite branched cover on complex points**,
with branch locus contained in the image of the complex points over `Z`. -/
theorem isBranchedCover_map [LocallyOfFiniteType c'] (f : C ⟶ C') [LocallyQuasiFinite f]
    [QuasiCompact f] (hf : f ≫ c' = c) (Z : Set C)
    (hZ : ∀ x ∉ Z, ∃ U : C.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) :
    Weil.IsBranchedCover (map f hf) (map f hf '' pointsOver c Z) where
  continuous := continuous_map f hf
  finite_fiber := finite_preimage_singleton_map f hf
  isLocalHomeomorphOn := isLocalHomeomorphOn_map f hf fun p hp ↦ by
    obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
    have hpZ : p.hom.base x ∉ Z := fun h ↦ hp ⟨p, (mem_pointsOver_iff x).2 h, rfl⟩
    obtain ⟨U, hxU, hU⟩ := hZ _ hpZ
    exact ⟨x, U, hxU, hU⟩

/-- The branch locus `f(ℂ)(pointsOver Z)` is finite when `Z` is. -/
theorem finite_image_pointsOver (f : C ⟶ C') (hf : f ≫ c' = c) {Z : Set C} (hZ : Z.Finite) :
    (map f hf '' pointsOver c Z).Finite :=
  (finite_pointsOver hZ).image _

end AlgebraicGeometry.Scheme.ComplexPoints
