module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable

/-!
# Morphisms from a connected object into disjoint copies of the final object

Let `S` be a scheme in a big étale site, `π : U ⟶ S` a connected nonempty object of the small
étale site of `S`, and `m : ℕ`. The `S`-morphisms `U ⟶ S^{⊔ m}` into the disjoint union of `m`
copies of the final object `S / S` are exactly the composites `ι_i ∘ π` with the inclusions of
the copies: the map `i ↦ ι_i ∘ π` is a bijection from the index set of the copies onto
`Hom_S(U, S^{⊔ m})`.

Indeed, the preimages under an `S`-morphism `a : U ⟶ S^{⊔ m}` of the copies are open, pairwise
disjoint and cover `U`, so as `U` is connected `a` factors through a single copy, and then
`a = ι_i ∘ b` with `b` an `S`-morphism `U ⟶ S`, i.e. `b = π`. Distinct copies give distinct
morphisms since `U` is nonempty and the copies are disjoint.

## Main results

* `Stacks.EtaleCohomology.bijective_comp_disjointCopiesι_of_connectedSpace` — for a connected
  object `U` of the small étale site of `S`, `i ↦ π ≫ ι_i` is a bijection from `Fin m` onto
  `U ⟶ S^{⊔ m}`.

## Implementation notes

The copies are indexed by `Fin m`, that is by `0, …, m - 1`, rather than by `1, …, m`. The
final object of the small étale site is `AlgebraicGeometry.SmallEtale.final`, and `π` is the
unique morphism to it. Connectedness of `U` is `ConnectedSpace` of its underlying scheme, which
includes nonemptiness.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], §I.3
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {S : AlgebraicGeometry.Scheme.{u}}
  (hS : B.Contains S)

/-- **Morphisms from a connected object into disjoint copies of the final object.** For a
connected (in particular nonempty) object `U` of the small étale site of `S` and `m : ℕ`, the
map `i ↦ π ≫ ι_i`, with `π : U ⟶ S / S` the morphism to the final object and `ι_i` the
inclusion of the `i`-th copy into `(S / S)^{⊔ m}`, is a bijection from `Fin m` onto the
morphisms `U ⟶ (S / S)^{⊔ m}`. -/
@[weil "lem_fk103_morphisms_to_copies_connected"]
theorem bijective_comp_disjointCopiesι_of_connectedSpace (U : SmallEtale B S hS)
    [ConnectedSpace ((SmallEtale.toScheme B S hS).obj U)] (m : ℕ) :
    Function.Bijective fun i : Fin m =>
      (SmallEtale.finalIsTerminal B S hS).from U ≫
        disjointCopiesι B hS (SmallEtale.final B S hS) m i := by
  set π := (SmallEtale.finalIsTerminal B S hS).from U
  let F := SmallEtale.toScheme B S hS
  let g : Fin m → Scheme.{u} := fun _ => F.obj (SmallEtale.final B S hS)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (F.obj U))
  constructor
  · intro i j hij
    by_contra hne
    have hsq : CommSq (F.map π) (F.map π) (Sigma.ι g i) (Sigma.ι g j) := ⟨by
      have := congrArg F.map hij
      rwa [Functor.map_comp, Functor.map_comp, toScheme_map_disjointCopiesι,
        toScheme_map_disjointCopiesι] at this⟩
    exact (isEmpty_of_commSq_sigmaι_of_ne (g := g) hsq hne).elim x₀
  · intro a
    let φ : F.obj U ⟶ ∐ g := F.map a
    have hcov : ∀ y : ↥(∐ g), ∃ i, y ∈ Set.range (Sigma.ι g i) := fun y => by
      obtain ⟨k, hk⟩ := (sigmaOpenCover g).exists_eq y
      exact ⟨k, hk⟩
    have huniq : ∀ (y : ↥(∐ g)) (i j : Fin m), y ∈ Set.range (Sigma.ι g i) →
        y ∈ Set.range (Sigma.ι g j) → i = j := by
      intro y i j hi hj
      by_contra hne
      have hd := disjoint_opensRange_sigmaι g i j hne
      exact (eq_bot_iff.mp (disjoint_iff.mp hd) (show y ∈ _ ⊓ _ from ⟨hi, hj⟩) :)
    -- the index of the copy containing the image of a point
    let idx : F.obj U → Fin m := fun x => Classical.choose (hcov (φ x))
    have hidx_spec : ∀ x, φ x ∈ Set.range (Sigma.ι g (idx x)) := fun x =>
      Classical.choose_spec (hcov (φ x))
    have hidx : Continuous idx := by
      rw [continuous_discrete_rng]
      intro i
      have : idx ⁻¹' {i} = φ ⁻¹' Set.range (Sigma.ι g i) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => h ▸ hidx_spec x, fun h => huniq _ _ _ (hidx_spec x) h⟩
      rw [this]
      exact (Sigma.ι g i).opensRange.2.preimage φ.continuous
    refine ⟨idx x₀, ?_⟩
    have hrange : Set.range φ ⊆ Set.range (Sigma.ι g (idx x₀)) := by
      rintro _ ⟨x, rfl⟩
      have hx : idx x = idx x₀ := PreconnectedSpace.constant inferInstance hidx
      exact hx ▸ hidx_spec x
    let b := IsOpenImmersion.lift (Sigma.ι g (idx x₀)) φ hrange
    have hb : b ≫ Sigma.ι g (idx x₀) = φ := IsOpenImmersion.lift_fac _ _ _
    apply hom_ext B hS
    change F.map (π ≫ disjointCopiesι B hS (SmallEtale.final B S hS) m (idx x₀)) = φ
    rw [Functor.map_comp, toScheme_map_disjointCopiesι, ← hb]
    congr 1
    -- both are `S`-morphisms to the final object, whose structure morphism is the identity
    have hπ := toScheme_map_comp_hom B hS π
    have hb' : b ≫ B.inclusion.map (SmallEtale.final B S hS).obj.hom =
        B.inclusion.map U.obj.hom := by
      have h2 := ι_comp_inclusion_map_hom_disjointUnionObj B hS
        (fun _ : Fin m => SmallEtale.final B S hS) (idx x₀)
      have h3 := toScheme_map_comp_hom B hS a
      rw [← h2]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans h3)
    have hid : B.inclusion.map (SmallEtale.final B S hS).obj.hom = 𝟙 _ := by
      simp [SmallEtale.final]
    have h := hπ.trans hb'.symm
    rw [hid] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))

end Stacks.EtaleCohomology
