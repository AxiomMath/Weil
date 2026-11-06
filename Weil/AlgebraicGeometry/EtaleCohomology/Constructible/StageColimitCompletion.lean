module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import Weil.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import Weil.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageColimitCompletion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulnessModules

/-!
# Exactness of a sequence of constructible sheaves descends to a finite level

Let `X = lim X_α` be a projective system of schemes with limit, `α₀` an index, and
`F ⟶ G ⟶ H` maps `u`, `v` of constructible sheaves on the small étale site of `X_{α₀}`. If the
inverse image `p_{α₀}^* F ⟶ p_{α₀}^* G ⟶ p_{α₀}^* H` on `X` is exact, then the inverse image
`F_α ⟶ G_α ⟶ H_α` to `X_α` is exact for some `α ≥ α₀`.

For an exact functor `T` between abelian categories, `T F ⟶ T G ⟶ T H` is exact if and only if
`T` kills both `v ∘ u` and the composite `ker v ⟶ G ⟶ coker u`; equivalently, if `T` kills the
single map `ψ = (v ∘ u) ⊕ (ker v ⟶ coker u) : F ⊕ ker v ⟶ H ⊕ coker u`. The sheaves `F ⊕ ker v`
and `H ⊕ coker u` are constructible, and the inverse image to `X` kills `ψ`, so by the
faithfulness of the comparison of constructible sheaves along the system ([Stacks, Tag 09YU])
some inverse image to a stage kills `ψ` as well.

## Main results

* `CategoryTheory.Functor.exists_exact_map_iff_map_biprodMap_eq_zero`: an exact functor sends
  `u`, `v` to an exact sequence if and only if it kills `(v ∘ u) ⊕ (ker v ⟶ coker u)`.
* `AlgebraicGeometry.IsProjectiveSystemWithLimit.exists_exact_smallEtaleInverseImage`:
  exactness of a sequence of constructible abelian sheaves on the limit descends to a stage.
* `AlgebraicGeometry.IsProjectiveSystemWithLimit.exists_exact_smallEtaleInverseImage_moduleCat`:
  the same for constructible sheaves of `Λ`-modules, `Λ` a Noetherian ring.

## Implementation notes

The source states the result for constructible sheaves of `ℤ/n`-modules. Both versions here
contain it: such a sheaf is a constructible abelian sheaf killed by `n`, and it is a constructible
sheaf of modules over the Noetherian ring `ULift (ZMod n)`. Exactness of a sequence of sheaves of
`ℤ/n`-modules is exactness of the underlying sequence of abelian sheaves.

The argument differs from the source's, which descends the vanishing of `v ∘ u` first and then
that of the homology `ker v / im u` at the later stage. Here both conditions are packed into the
vanishing of the single map `ψ` at the base stage, so one application of faithfulness suffices
and no comparison of iterated inverse images is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.18][FreitagKiehl]
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (T : C ⥤ D) [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- For an exact functor `T`, the composite `ker (T v) ⟶ T G ⟶ coker (T u)` vanishes if and
only if `T` kills the composite `ker v ⟶ G ⟶ coker u`. -/
theorem kernel_ι_map_comp_cokernel_π_map_eq_zero_iff {F G H : C} (u : F ⟶ G) (v : G ⟶ H) :
    kernel.ι (T.map v) ≫ cokernel.π (T.map u) = 0 ↔
      T.map (kernel.ι v ≫ cokernel.π u) = 0 := by
  rw [← PreservesKernel.iso_inv_ι T v, ← PreservesCokernel.π_iso_hom T u, Category.assoc,
    ← Category.assoc (T.map (kernel.ι v)), ← T.map_comp]
  constructor
  · intro h
    have h' := congrArg (fun f => (PreservesKernel.iso T v).hom ≫ f ≫
      (PreservesCokernel.iso T u).inv) h
    simpa using h'
  · intro h
    simp [h]

/-- **An exact functor preserves exactness of `u`, `v` iff it kills one map.** For an exact
functor `T` between abelian categories and maps `u : F ⟶ G`, `v : G ⟶ H`, the sequence
`T F ⟶ T G ⟶ T H` is exact if and only if `T` kills
`(v ∘ u) ⊕ (ker v ⟶ coker u) : F ⊞ ker v ⟶ H ⊞ coker u`. -/
theorem exists_exact_map_iff_map_biprodMap_eq_zero {F G H : C} (u : F ⟶ G) (v : G ⟶ H) :
    (∃ w : T.map u ≫ T.map v = 0, (ShortComplex.mk _ _ w).Exact) ↔
      T.map (biprod.map (u ≫ v) (kernel.ι v ≫ cokernel.π u)) = 0 := by
  have : T.Additive := Functor.additive_of_preserves_binary_products T
  constructor
  · rintro ⟨w, hw⟩
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hw
    have h₂ := (kernel_ι_map_comp_cokernel_π_map_eq_zero_iff T u v).1 hw
    rw [← T.map_comp] at w
    rw [biprod.map_eq, T.map_add, T.map_comp _ ((u ≫ v) ≫ _), T.map_comp (u ≫ v), w,
      T.map_comp _ ((kernel.ι v ≫ cokernel.π u) ≫ _), T.map_comp (kernel.ι v ≫ cokernel.π u), h₂]
    simp
  · intro h
    have h₁ : T.map (u ≫ v) = 0 := by
      have := congrArg (fun f => T.map biprod.inl ≫ f ≫ T.map biprod.fst) h
      simp only [comp_zero, zero_comp] at this
      rwa [← T.map_comp, ← T.map_comp, biprod.inl_map_assoc, biprod.inl_fst,
        Category.comp_id] at this
    have h₂ : T.map (kernel.ι v ≫ cokernel.π u) = 0 := by
      have := congrArg (fun f => T.map biprod.inr ≫ f ≫ T.map biprod.snd) h
      simp only [comp_zero, zero_comp] at this
      rwa [← T.map_comp, ← T.map_comp, biprod.inr_map_assoc, biprod.inr_snd,
        Category.comp_id] at this
    refine ⟨by rw [← T.map_comp, h₁], ?_⟩
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    exact (kernel_ι_map_comp_cokernel_π_map_eq_zero_iff T u v).2 h₂

end CategoryTheory.Functor

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)
  (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

section

variable {B Dg c hX}

/-- The stages of a projective system with limit are quasi-compact. -/
lemma IsProjectiveSystemWithLimit.compactSpace_stage
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (p : I) :
    CompactSpace (Dg.obj (op p)).obj :=
  have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p)
  inferInstance

/-- The stages of a projective system with limit are quasi-separated. -/
lemma IsProjectiveSystemWithLimit.quasiSeparatedSpace_stage
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (p : I) :
    QuasiSeparatedSpace (Dg.obj (op p)).obj :=
  have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p)
  inferInstance

end

/-- **Exactness descends to a finite level.** Let `X = lim X_α` be a projective system of schemes
with limit, `α₀` an index and `u : F ⟶ G`, `v : G ⟶ H` maps of constructible abelian sheaves on
the small étale site of `X_{α₀}`. If `p_{α₀}^* F ⟶ p_{α₀}^* G ⟶ p_{α₀}^* H` is exact on `X`, then
`F_α ⟶ G_α ⟶ H_α` is exact for some `α ≥ α₀`, where `F_α = p_{α α₀}^* F` and so on. -/
@[weil "lem_fk104_exactness_descends_to_finite_level"]
theorem IsProjectiveSystemWithLimit.exists_exact_smallEtaleInverseImage
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) {α₀ : I}
    {F G H : Sheaf (SmallEtale.topology B (Dg.obj (op α₀)).obj (Dg.obj (op α₀)).property)
      AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleAbelianSheaf B (Dg.obj (op α₀)) F)
    (hG : IsConstructibleAbelianSheaf B (Dg.obj (op α₀)) G)
    (hH : IsConstructibleAbelianSheaf B (Dg.obj (op α₀)) H) (u : F ⟶ G) (v : G ⟶ H)
    (w : (smallEtaleInverseImage B
        (ObjectProperty.homMk (c.π.app (op α₀)) : B.obj c.pt hX ⟶ Dg.obj (op α₀))
        AddCommGrpCat.{u + 1}).map u ≫
      (smallEtaleInverseImage B
        (ObjectProperty.homMk (c.π.app (op α₀)) : B.obj c.pt hX ⟶ Dg.obj (op α₀))
        AddCommGrpCat.{u + 1}).map v = 0)
    (hexact : (ShortComplex.mk _ _ w).Exact) :
    ∃ (α : I) (h : α₀ ≤ α)
      (wα : (smallEtaleInverseImage B (Dg.map (homOfLE h).op) AddCommGrpCat.{u + 1}).map u ≫
        (smallEtaleInverseImage B (Dg.map (homOfLE h).op) AddCommGrpCat.{u + 1}).map v = 0),
      (ShortComplex.mk _ _ wα).Exact := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  let P : ObjectProperty (Sheaf (SmallEtale.topology B (Dg.obj (op α₀)).obj
      (Dg.obj (op α₀)).property) AddCommGrpCat.{u + 1}) :=
    fun K => IsConstructibleAbelianSheaf B (Dg.obj (op α₀)) K
  let _ : P.IsWeakSerreClass := constructibleAbelianSheaf_isWeakSerreClass B (Dg.obj (op α₀))
  have hsrc : P (F ⊞ kernel v) := P.prop_biprod hF (P.prop_kernel v hG hH)
  have htgt : P (H ⊞ cokernel u) := P.prop_biprod hH (P.prop_cokernel u hF hG)
  let p : B.obj c.pt hX ⟶ Dg.obj (op α₀) := ObjectProperty.homMk (c.π.app (op α₀))
  have := smallEtaleInverseImage_preservesFiniteLimits B p
  have := smallEtaleInverseImage_preservesFiniteColimits B p
  have hψ := ((smallEtaleInverseImage B p
        AddCommGrpCat.{u + 1}).exists_exact_map_iff_map_biprodMap_eq_zero u v).1 ⟨w, hexact⟩
  obtain ⟨α, h, hα⟩ := smallEtaleStagesFaithful_isConstructibleAbelianSheaf B Dg c hX hc
    (fun e => hD.isAffineHom_map e) hD.compactSpace_stage hD.quasiSeparatedSpace_stage α₀
    _ _ hsrc htgt _ 0 (hψ.trans (Functor.map_zero _ _ _).symm)
  have := smallEtaleInverseImage_preservesFiniteLimits B (Dg.map (homOfLE h).op)
  have := smallEtaleInverseImage_preservesFiniteColimits B (Dg.map (homOfLE h).op)
  refine ⟨α, h, ((smallEtaleInverseImage B (Dg.map (homOfLE h).op)
    AddCommGrpCat.{u + 1}).exists_exact_map_iff_map_biprodMap_eq_zero u v).2 ?_⟩
  exact hα.trans (Functor.map_zero _ _ _)

/-- **Exactness descends to a finite level, for sheaves of modules.** Let `X = lim X_α` be a
projective system of schemes with limit, `Λ` a Noetherian ring, `α₀` an index and
`u : F ⟶ G`, `v : G ⟶ H` maps of constructible sheaves of `Λ`-modules on the small étale site of
`X_{α₀}`. If `p_{α₀}^* F ⟶ p_{α₀}^* G ⟶ p_{α₀}^* H` is exact on `X`, then `F_α ⟶ G_α ⟶ H_α` is
exact for some `α ≥ α₀`. For `Λ = ℤ/n` this is the statement for sheaves of `ℤ/n`-modules. -/
@[weil "lem_fk104_exactness_descends_to_finite_level"]
theorem IsProjectiveSystemWithLimit.exists_exact_smallEtaleInverseImage_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) {α₀ : I}
    {F G H : Sheaf (SmallEtale.topology B (Dg.obj (op α₀)).obj (Dg.obj (op α₀)).property)
      (ModuleCat.{u + 1} Λ)}
    (hF : IsConstructibleModuleSheaf B (Dg.obj (op α₀)) Λ F)
    (hG : IsConstructibleModuleSheaf B (Dg.obj (op α₀)) Λ G)
    (hH : IsConstructibleModuleSheaf B (Dg.obj (op α₀)) Λ H) (u : F ⟶ G) (v : G ⟶ H)
    (w : (smallEtaleInverseImage B
        (ObjectProperty.homMk (c.π.app (op α₀)) : B.obj c.pt hX ⟶ Dg.obj (op α₀))
        (ModuleCat.{u + 1} Λ)).map u ≫
      (smallEtaleInverseImage B
        (ObjectProperty.homMk (c.π.app (op α₀)) : B.obj c.pt hX ⟶ Dg.obj (op α₀))
        (ModuleCat.{u + 1} Λ)).map v = 0)
    (hexact : (ShortComplex.mk _ _ w).Exact) :
    ∃ (α : I) (h : α₀ ≤ α)
      (wα : (smallEtaleInverseImage B (Dg.map (homOfLE h).op) (ModuleCat.{u + 1} Λ)).map u ≫
        (smallEtaleInverseImage B (Dg.map (homOfLE h).op) (ModuleCat.{u + 1} Λ)).map v = 0),
      (ShortComplex.mk _ _ wα).Exact := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  let P : ObjectProperty (Sheaf (SmallEtale.topology B (Dg.obj (op α₀)).obj
      (Dg.obj (op α₀)).property) (ModuleCat.{u + 1} Λ)) :=
    fun K => IsConstructibleModuleSheaf B (Dg.obj (op α₀)) Λ K
  let _ : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  have hsrc : P (F ⊞ kernel v) := P.prop_biprod hF (P.prop_kernel v hG hH)
  have htgt : P (H ⊞ cokernel u) := P.prop_biprod hH (P.prop_cokernel u hF hG)
  let p : B.obj c.pt hX ⟶ Dg.obj (op α₀) := ObjectProperty.homMk (c.π.app (op α₀))
  have := preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B p Λ
  have := preservesFiniteColimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B p Λ
  have hψ := ((smallEtaleInverseImage B p
        (ModuleCat.{u + 1} Λ)).exists_exact_map_iff_map_biprodMap_eq_zero u v).1 ⟨w, hexact⟩
  obtain ⟨α, h, hα⟩ := smallEtaleStagesFaithful_isConstructibleModuleSheaf B Λ Dg c hX hc
    (fun e => hD.isAffineHom_map e) hD.compactSpace_stage hD.quasiSeparatedSpace_stage α₀
    _ _ hsrc htgt _ 0 (hψ.trans (Functor.map_zero _ _ _).symm)
  have := preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B
    (Dg.map (homOfLE h).op) Λ
  have := preservesFiniteColimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B
    (Dg.map (homOfLE h).op) Λ
  refine ⟨α, h, ((smallEtaleInverseImage B (Dg.map (homOfLE h).op)
    (ModuleCat.{u + 1} Λ)).exists_exact_map_iff_map_biprodMap_eq_zero u v).2 ?_⟩
  exact hα.trans (Functor.map_zero _ _ _)

end AlgebraicGeometry

end
