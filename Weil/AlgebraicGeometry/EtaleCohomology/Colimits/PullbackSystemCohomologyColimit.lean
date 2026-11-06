module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSystemRestrictIndex

/-!
# Étale cohomology commutes with projective limits of schemes

Let `X = lim X_α` be a projective system of schemes with limit
(`AlgebraicGeometry.IsProjectiveSystemWithLimit`), indexed by a directed set `I`, let `α₀ ∈ I`
and let `F_{α₀}` be an abelian sheaf on the small étale site of `X_{α₀}`. Write
`F_α = p_{αα₀}⁻¹ F_{α₀}` for `α ≥ α₀` and `F = p_{α₀}⁻¹ F_{α₀}` on `X`. The canonical maps
`H^i(X_α, F_α) → H^i(X, F)` — inverse image of an `Ext` class out of the constant sheaf `ℤ`,
followed by the identification of the inverse images of `F_{α₀}` along `p_α ∘ p_{αα₀} = p_{α₀}` —
form a compatible system, and induce a bijection
`colim_{α ≥ α₀} H^i(X_α, F_α) ≅ H^i(X, F)`.

## Main results

* `AlgebraicGeometry.IsProjectiveSystemWithLimit.cohomology_colimit`: the bijection
  `colim_{α ≥ α₀} H^i(X_α, F_α) ≅ H^i(X, F)`, stated elementwise: the canonical maps are
  compatible with the transition maps, every class on `X` comes from some `X_α`, and a class on
  `X_α` that vanishes on `X` vanishes on some `X_β`, `β ≥ α`.

## Implementation notes

The statement holds for every abelian sheaf `F_{α₀}`, not only for torsion sheaves; this is the
form of [Stacks, Tag 09YQ], which only asks the `X_α` to be quasi-compact and quasi-separated with
affine transition morphisms. The proof is that theorem, applied to the system of inverse images
of `F_{α₀}` over the directed set `{α ∈ I | α ≥ α₀}`, whose limit is still `X`.

The cohomology is Mathlib's `CategoryTheory.Sheaf.H` on the small étale site
`AlgebraicGeometry.Scheme.smallEtaleTopology`, with coefficients in `AddCommGrpCat.{u + 1}` for
schemes in `Scheme.{u}`: `H^i(X, F) = Ext^i(ℤ_X, F)`, and the canonical map is
`Stacks.EtaleCohomology.etaleCohomologyMapTo`, i.e. `ε⁻¹ ∘ p^* ∘ ε` with `p^*` the inverse image
on `Ext` groups and `ε` the identification of the inverse image of the constant sheaf `ℤ`.

The colimit statement is elementwise (joint surjectivity of the canonical maps and eventual
vanishing of their kernels). For a directed index and abelian groups this is exactly the
assertion that the induced map from the colimit is bijective.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

/- FK state the result for a torsion sheaf `F_{α₀}`; the
statement here has no torsion hypothesis (stronger than FK's statement). -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology Stacks.EtaleCohomology.SmallEtaleLimitCohomology

universe u

namespace AlgebraicGeometry.IsProjectiveSystemWithLimit

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}

/-- **Étale cohomology commutes with projective limits of schemes.** Let `X = lim X_α` be a
projective system of schemes with limit over a directed set `I`, let `α₀ ∈ I` and let `F_{α₀}` be
an abelian sheaf on the small étale site of `X_{α₀}`, with inverse images `F_α` on `X_α`
(`α ≥ α₀`) and `F` on `X`. Then the canonical maps `φ_α : H^p(X_α, F_α) → H^p(X, F)` induce a
bijection `colim_{α ≥ α₀} H^p(X_α, F_α) ≅ H^p(X, F)`: they are compatible with the transition maps
`ψ_{βα} : H^p(X_α, F_α) → H^p(X_β, F_β)`, every class on `X` is some `φ_α x`, and `φ_α x = 0`
implies `ψ_{βα} x = 0` for some `β ≥ α`. -/
@[weil "prop_fk104_cohomology_commutes_with_projective_limits"]
theorem cohomology_colimit (h : IsProjectiveSystemWithLimit D c) (α₀ : I)
    (F₀ : Sheaf (D.obj (op α₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (∀ (α β : I) (hα : α₀ ≤ α) (hβ : α₀ ≤ β) (hαβ : α ≤ β)
        (x : Sheaf.H.{u + 1, u + 1}
          ((etaleAbelianInverseImage.{u, u + 1} (D.map (homOfLE hα).op)).obj F₀) p),
        etaleCohomologyMapTo (c.π.app (op β))
            ((etaleAbelianInverseImageCompIso'.{u, u + 1} (c.π.app (op β))
              (D.map (homOfLE hβ).op) (c.π.app (op α₀)) (c.w _).symm).inv.app F₀) p
          (etaleCohomologyMapTo (D.map (homOfLE hαβ).op)
            ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map (homOfLE hαβ).op)
              (D.map (homOfLE hα).op) (D.map (homOfLE hβ).op)
              (by rw [← D.map_comp]; rfl)).inv.app F₀) p x) =
        etaleCohomologyMapTo (c.π.app (op α))
            ((etaleAbelianInverseImageCompIso'.{u, u + 1} (c.π.app (op α))
              (D.map (homOfLE hα).op) (c.π.app (op α₀)) (c.w _).symm).inv.app F₀) p x) ∧
    (∀ y : Sheaf.H.{u + 1, u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} (c.π.app (op α₀))).obj F₀) p,
      ∃ (α : I) (hα : α₀ ≤ α) (x : Sheaf.H.{u + 1, u + 1}
          ((etaleAbelianInverseImage.{u, u + 1} (D.map (homOfLE hα).op)).obj F₀) p),
        etaleCohomologyMapTo (c.π.app (op α))
            ((etaleAbelianInverseImageCompIso'.{u, u + 1} (c.π.app (op α))
              (D.map (homOfLE hα).op) (c.π.app (op α₀)) (c.w _).symm).inv.app F₀) p x = y) ∧
    (∀ (α : I) (hα : α₀ ≤ α) (x : Sheaf.H.{u + 1, u + 1}
          ((etaleAbelianInverseImage.{u, u + 1} (D.map (homOfLE hα).op)).obj F₀) p),
      etaleCohomologyMapTo (c.π.app (op α))
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (c.π.app (op α))
            (D.map (homOfLE hα).op) (c.π.app (op α₀)) (c.w _).symm).inv.app F₀) p x = 0 →
        ∃ (β : I) (hβ : α₀ ≤ β) (hαβ : α ≤ β),
          etaleCohomologyMapTo (D.map (homOfLE hαβ).op)
            ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map (homOfLE hαβ).op)
              (D.map (homOfLE hα).op) (D.map (homOfLE hβ).op)
              (by rw [← D.map_comp]; rfl)).inv.app F₀) p x = 0) := by
  have := h.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  have : ∀ (i : I), IsNoetherian (D.obj (op i)) := fun i => h.isNoetherian_obj _
  obtain ⟨hc⟩ := h.nonempty_isLimit
  let D' : (GeIndex α₀)ᵒᵖ ⥤ Scheme.{u} := geIndexOpFunctor α₀ ⋙ D
  let c' : Cone D' := c.whisker (geIndexOpFunctor α₀)
  have hc' : IsLimit c' := isLimit_whisker_geIndexOpFunctor α₀ hc
  have : ∀ {i j : (GeIndex α₀)ᵒᵖ} (a : i ⟶ j), IsAffineHom (D'.map a) :=
    fun a => h.isAffineHom_map _
  have : ∀ i : (GeIndex α₀)ᵒᵖ, CompactSpace (D'.obj i) := fun i => inferInstanceAs
    (CompactSpace (D.obj (op i.unop.1)))
  have : ∀ i : (GeIndex α₀)ᵒᵖ, QuasiSeparatedSpace (D'.obj i) := fun i => inferInstanceAs
    (QuasiSeparatedSpace (D.obj (op i.unop.1)))
  let s : ∀ i : (GeIndex α₀)ᵒᵖ, D'.obj i ⟶ D.obj (op α₀) := fun i => D.map (homOfLE i.unop.2).op
  have hs : ∀ {i j : (GeIndex α₀)ᵒᵖ} (a : i ⟶ j), s i = D'.map a ≫ s j := fun a => by
    simp only [s, D', Functor.comp_map, ← D.map_comp]; rfl
  let sc : c'.pt ⟶ D.obj (op α₀) := c.π.app (op α₀)
  have hsc : ∀ i : (GeIndex α₀)ᵒᵖ, sc = conePi c' i ≫ s i := fun i => (c.w _).symm
  have H := isCohomologyColimit_pullbackPresentedSystem F₀ s hs hc' sc hsc p
  let E := pullbackPresentedSystem F₀ s hs sc hsc
  refine ⟨fun α β hα hβ hαβ x => ?_, fun y => ?_, fun α hα x hx => ?_⟩
  · let a : (op (⟨β, hβ⟩ : GeIndex α₀)) ⟶ op ⟨α, hα⟩ :=
      (homOfLE (show (⟨α, hα⟩ : GeIndex α₀) ≤ ⟨β, hβ⟩ from hαβ)).op
    have h1 : etaleCohomologyMapTo (conePi c' (op ⟨β, hβ⟩))
          (pullbackSystemLeg F₀ s hs sc hsc (op ⟨β, hβ⟩)) p
          (etaleCohomologyMapTo (D'.map a) (systemTransitionMap (pullbackSystem F₀ s hs) a) p x) =
        etaleCohomologyMapTo (conePi c' (op ⟨α, hα⟩))
          (pullbackSystemLeg F₀ s hs sc hsc (op ⟨α, hα⟩)) p x :=
      E.leg_transition a p x
    rw [systemTransitionMap_pullbackSystem] at h1
    exact h1
  · obtain ⟨⟨α, hα⟩, x, hx⟩ := H.exists_leg_eq y
    exact ⟨α, hα, x, hx⟩
  · obtain ⟨⟨β, hβ⟩, a, ha⟩ := H.exists_transition_eq_zero (op ⟨α, hα⟩) x hx
    have hαβ : α ≤ β := leOfHom a.unop
    refine ⟨β, hβ, hαβ, ?_⟩
    have h2 : etaleCohomologyMapTo (D'.map a)
        (systemTransitionMap (pullbackSystem F₀ s hs) a) p x = 0 := ha
    rw [systemTransitionMap_pullbackSystem] at h2
    exact h2

end AlgebraicGeometry.IsProjectiveSystemWithLimit
