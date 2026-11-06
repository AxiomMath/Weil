module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Morphisms.Etale
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.Defs.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringSpace
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.InducedActionOnPoints
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

/-!
# A scheme representing a torsor is a Galois covering space

Let `X` be a locally noetherian scheme, `F` a finite group and `𝒢` an `F_X`-torsor on the étale
category `Et(X)`, where `F_X` is the constant sheaf of groups of locally constant `F`-valued maps.
Suppose that `X'` is an object of `Et(X)` with an action `τ ↦ a_τ` of `F` by `X`-automorphisms,
and that `θ : h_{X'} ≅ 𝒢` is an isomorphism of sheaves with `θ(t ^ σ) = θ(t) ^ σ`, where
`t ↦ t ^ σ` is the right action of `F_X` on `h_{X'}` induced by the action on `X'`. Then
`X' → X` is surjective and `X'` is an `F`-Galois covering space of `X`: the morphism
`∐_{τ ∈ F} X' → X' ×_X X'`, `x' ↦ (a_τ x', x')` on the copy indexed by `τ`, is an isomorphism.

The inverse is built from the two projections `t₁, t₂ ∈ h_{X'}(X' ×_X X')`: there is a unique
`σ ∈ F_X(X' ×_X X')` with `t₂ ^ σ = t₁`, and on the open and closed subset `{σ = τ}` the
inverse is the second projection followed by the inclusion of the copy indexed by `τ⁻¹`.
Surjectivity holds because `𝒢` has sections, hence `X'` has `U`-points, on the members `U` of
an étale covering.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.existsUnique_locallyConstantSMul_eq` — the
  sections of `F_X` act simply transitively on the sections of `h_{X'}`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.surjective_structureMorphism_of_isTorsor` —
  `X' → X` is surjective.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isGaloisCovering_of_isTorsor` — `X'` is an
  `F`-Galois covering space of `X`.

## Implementation notes

The torsor is a pseudo `F_X`-torsor (`PseudoTorsor`, for the left action) satisfying
`PseudoTorsor.IsTorsor`; its right action `t ^ σ = σ⁻¹ • t` is `PseudoTorsor.toRightAction`, which
is how the compatibility of `θ` with the actions is stated. The torsor condition of
`PseudoTorsor.IsTorsor` asks for a covering of every object of `Et(X)` on whose members `𝒢` has
sections; this is equivalent to asking it for a covering of `X`. Finiteness of `F` is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} [IsLocallyNoetherian X]
  {F : Type u} [Group F]

/-- The fibre product `X' ×_X X'` of an object `X'` of `Et(X)` with itself, as an object of
`Et(X)` with structure morphism the first projection followed by `X' → X`. -/
def pullbackSelf (X' : SmallNoetherianSeparatedEtale B X hX) :
    SmallNoetherianSeparatedEtale B X hX :=
  have : IsNoetherian (pullback (structureMorphism X') (structureMorphism X')) :=
    isNoetherian_pullback_of_etale _ _
  have : (pullback (structureMorphism X') (structureMorphism X')).IsSeparated :=
    isSeparated_pullback_of_isSeparated _ _
  mk (pullback (structureMorphism X') (structureMorphism X'))
    (Scheme.size_pullback_lt _ _ (contains_toScheme_obj X') (contains_toScheme_obj X'))
    (pullback.fst _ _ ≫ structureMorphism X')

/-- **Simple transitivity on `h_{X'}`.** If `θ : h_{X'} ≅ 𝒢` is compatible with the actions of
`F_X`, for an `F_X`-pseudo torsor `𝒢`, then for all sections `t, s` of `h_{X'}` over `U` there is a
unique `σ ∈ F_X(U)` with `t ^ σ = s`. -/
theorem existsUnique_locallyConstantSMul_eq
    (T : PseudoTorsor.{u} (locallyConstantSheafOfGroups B X hX F))
    (X' : SmallNoetherianSeparatedEtale B X hX) (ρ : F →* Aut ((toOver B X hX).obj X'))
    (θ : representablePresheaf B X hX ((toOver B X hX).obj X') ≅ T.presheaf)
    (hθ : ∀ (U : SmallNoetherianSeparatedEtale B X hX)
      (σ : (locallyConstantPresheafGrp B X hX F).obj (op U))
      (t : (representablePresheaf B X hX ((toOver B X hX).obj X')).obj (op U)),
      θ.hom.app (op U) (letI := inducedMulAction ρ U; MulOpposite.op σ • t) =
        T.toRightAction.act (op U) (θ.hom.app (op U) t) σ)
    (U : SmallNoetherianSeparatedEtale B X hX)
    (t s : (toOver B X hX).obj U ⟶ (toOver B X hX).obj X') :
    ∃! σ : LocallyConstant ((toOver B X hX).obj U).left F,
      Over.locallyConstantSMul ρ σ t = s := by
  have hinj : Function.Injective (θ.hom.app (op U)) :=
    ((θ.app (op U)).toEquiv).injective
  let G := (locallyConstantSheafOfGroups B X hX F).presheaf.obj (op U)
  let e : LocallyConstant ((toOver B X hX).obj U).left F ≃ G := Equiv.refl _
  have key (σ : G) :
      Over.locallyConstantSMul ρ (e.symm σ) t = s ↔
        T.act (op U) σ⁻¹ (θ.hom.app (op U) t) = θ.hom.app (op U) s := by
    have h := hθ U σ t
    refine ⟨fun h' ↦ ?_, fun h' ↦ hinj ?_⟩
    · rw [← h']
      exact h.symm
    · exact h.trans h'
  obtain ⟨g, hg, hu⟩ := T.simplyTransitive (op U) ⟨θ.hom.app (op U) t⟩
    (θ.hom.app (op U) t) (θ.hom.app (op U) s)
  refine ⟨e.symm g⁻¹, (key g⁻¹).2 (by rw [inv_inv]; exact hg), fun τ hτ ↦ ?_⟩
  have := hu (e τ)⁻¹ ((key (e τ)).1 hτ)
  rw [e.eq_symm_apply, ← this, inv_inv]

/-- **The structure morphism of a scheme representing a torsor is surjective.** If `h_{X'}` is
isomorphic to the underlying sheaf of an `F_X`-torsor, then `X' → X` is surjective. -/
theorem surjective_structureMorphism_of_isTorsor
    (T : PseudoTorsor.{u} (locallyConstantSheafOfGroups B X hX F)) (hT : T.IsTorsor)
    (X' : SmallNoetherianSeparatedEtale B X hX)
    (θ : representablePresheaf B X hX ((toOver B X hX).obj X') ≅ T.presheaf) :
    Surjective (structureMorphism X') := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨R, j, _, hj, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) (by simp)
  have hR : B.Contains (Spec R) := (Scheme.size_le_of_locallyOfFiniteType j).trans_lt hX
  have : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian j
  have : IsNoetherian (Spec R) := {}
  obtain ⟨y, rfl⟩ := hj
  obtain ⟨S, hS, hne⟩ := hT (mk (Spec R) hR j)
  obtain ⟨V, f, hf, z, rfl⟩ := (mem_topology_iff B X hX S).1 hS y
  obtain ⟨g⟩ := hne hf
  let t : (toOver B X hX).obj V ⟶ (toOver B X hX).obj X' := θ.inv.app (op V) g
  refine ⟨t.left z, ?_⟩
  have h1 : (t.left ≫ structureMorphism X') z =
      ((toScheme B X hX).map f ≫ structureMorphism (mk (hS := hX) (Spec R) hR j)) z := by
    rw [toScheme_map_comp_structureMorphism]
    exact congrArg (fun φ : _ ⟶ X ↦ φ z) (Over.w t)
  exact h1

/-- **A scheme representing an `F_X`-torsor is an `F`-Galois covering space.** Let `𝒢` be an
`F_X`-torsor on `Et(X)`, `X'` an object of `Et(X)` with an action `ρ` of `F` by `X`-automorphisms,
and `θ : h_{X'} ≅ 𝒢` an isomorphism with `θ(t ^ σ) = θ(t) ^ σ`, for the induced action
`t ↦ t ^ σ` of `F_X` on `h_{X'}`. Then `X'` is an `F`-Galois covering space of `X`; in particular
`X' → X` is surjective. -/
@[weil "lem_fk102_torsor_representing_scheme_is_galois"]
theorem isGaloisCovering_of_isTorsor
    (T : PseudoTorsor.{u} (locallyConstantSheafOfGroups B X hX F)) (hT : T.IsTorsor)
    (X' : SmallNoetherianSeparatedEtale B X hX) (ρ : F →* Aut ((toOver B X hX).obj X'))
    (θ : representablePresheaf B X hX ((toOver B X hX).obj X') ≅ T.presheaf)
    (hθ : ∀ (U : SmallNoetherianSeparatedEtale B X hX)
      (σ : (locallyConstantPresheafGrp B X hX F).obj (op U))
      (t : (representablePresheaf B X hX ((toOver B X hX).obj X')).obj (op U)),
      θ.hom.app (op U) (letI := inducedMulAction ρ U; MulOpposite.op σ • t) =
        T.toRightAction.act (op U) (θ.hom.app (op U) t) σ) :
    IsGaloisCovering ((toOver B X hX).obj X') ρ := by
  have hu := existsUnique_locallyConstantSMul_eq T X' ρ θ hθ
  refine ⟨inferInstanceAs (Etale (structureMorphism X')),
    surjective_structureMorphism_of_isTorsor T hT X' θ, ?_⟩
  let Q := pullbackSelf X'
  let t₁ : (toOver B X hX).obj Q ⟶ (toOver B X hX).obj X' :=
    Over.homMk (pullback.fst ((toOver B X hX).obj X').hom ((toOver B X hX).obj X').hom) rfl
  let t₂ : (toOver B X hX).obj Q ⟶ (toOver B X hX).obj X' :=
    Over.homMk (pullback.snd ((toOver B X hX).obj X').hom ((toOver B X hX).obj X').hom)
      pullback.condition.symm
  obtain ⟨σ, hσ, -⟩ := hu Q t₂ t₁
  obtain ⟨σ', hσ'⟩ : ∃ σ' : LocallyConstant
      ↥(pullback ((toOver B X hX).obj X').hom ((toOver B X hX).obj X').hom) F,
      ∀ y, σ' y = σ y := ⟨σ, fun _ ↦ rfl⟩
  -- On `{σ = τ}`, the first projection is the second followed by `a_{τ⁻¹}`.
  have hfib (τ : F) : (fiberOpen F σ' τ).ι ≫ pullback.fst _ _ =
      (fiberOpen F σ' τ).ι ≫ pullback.snd _ _ ≫ (ρ τ⁻¹).hom.left := by
    have h := Over.comp_locallyConstantSMul_left_of_forall
      (fiberOpen F σ' τ).ι ρ σ t₂ τ fun (y : ↥(fiberOpen F σ' τ)) ↦ (hσ' y.1).symm.trans y.2
    rw [hσ] at h
    exact h
  -- Along `x' ↦ (a_ν x', x')`, `σ` is constant with value `ν⁻¹`.
  have hconst (ν : F) (hp : (ρ ν).hom.left ≫ ((toOver B X hX).obj X').hom =
      𝟙 _ ≫ ((toOver B X hX).obj X').hom) (y : ((toOver B X hX).obj X').left) :
      σ' (pullback.lift (ρ ν).hom.left (𝟙 _) hp y) = ν⁻¹ := by
    let p := pullback.lift (ρ ν).hom.left (𝟙 _) hp
    let pO : (toOver B X hX).obj X' ⟶ (toOver B X hX).obj Q := Over.homMk p (by
      change p ≫ pullback.fst _ _ ≫ ((toOver B X hX).obj X').hom = ((toOver B X hX).obj X').hom
      rw [pullback.lift_fst_assoc]
      exact Over.w (ρ ν).hom)
    have h : σ.comap p.base.hom = LocallyConstant.const _ ν⁻¹ := by
      refine (hu X' (pO ≫ t₂) (pO ≫ t₁)).unique ?_ ?_
      · have h := Over.comp_locallyConstantSMul pO ρ σ t₂
        rw [hσ] at h
        exact h.symm
      · ext1
        rw [Over.locallyConstantSMul_left, Scheme.twistByLocallyConstant_const]
        change (p ≫ pullback.snd _ _) ≫ (ρ ν⁻¹⁻¹).hom.left = p ≫ pullback.fst _ _
        rw [inv_inv, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
    exact (hσ' _).trans (congrArg (· y) h)
  obtain ⟨a, ha⟩ : ∃ a : F → ((∐ fun _ : F ↦ ((toOver B X hX).obj X').left) ⟶
      (∐ fun _ : F ↦ ((toOver B X hX).obj X').left)), ∀ τ ν,
      Sigma.ι (fun _ : F ↦ ((toOver B X hX).obj X').left) ν ≫ a τ =
        Sigma.ι (fun _ : F ↦ ((toOver B X hX).obj X').left) (ν * τ⁻¹) :=
    ⟨fun τ ↦ Limits.Sigma.desc fun ν ↦
      Sigma.ι (fun _ : F ↦ ((toOver B X hX).obj X').left) (ν * τ⁻¹),
      fun τ ν ↦ Sigma.ι_desc _ _⟩
  refine ⟨Scheme.twistByLocallyConstant a σ'
    (pullback.snd ((toOver B X hX).obj X').hom ((toOver B X hX).obj X').hom ≫
      Sigma.ι (fun _ : F ↦ ((toOver B X hX).obj X').left) 1), ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun ν ↦ ?_
    have hp : (ρ ν).hom.left ≫ ((toOver B X hX).obj X').hom =
        𝟙 _ ≫ ((toOver B X hX).obj X').hom := by
      rw [Category.id_comp]
      exact Over.w (ρ ν).hom
    have hfac : galoisCoveringMap ((toOver B X hX).obj X') ρ =
        Limits.Sigma.desc fun ν ↦ pullback.lift (ρ ν).hom.left (𝟙 _) (by
          rw [Category.id_comp]; exact Over.w (ρ ν).hom) := rfl
    rw [hfac, Sigma.ι_desc_assoc, Category.comp_id,
      Scheme.comp_twistByLocallyConstant_of_forall _ a σ' _ ν⁻¹ (hconst ν hp), Category.assoc]
    erw [pullback.lift_snd_assoc]
    rw [Category.id_comp, ha, one_mul, inv_inv]
  · refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨fiberOpen F σ' (σ' x), rfl, ?_⟩
    rw [Scheme.ι_fiberOpen_twistByLocallyConstant_assoc, Category.assoc,
      ← Category.assoc (Sigma.ι _ 1), ha, one_mul]
    apply pullback.hom_ext
    · simp only [Category.assoc, ι_galoisCoveringMap_fst, Category.id_comp]
      exact (hfib _).symm
    · simp only [Category.assoc, ι_galoisCoveringMap_snd, Category.comp_id]

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
