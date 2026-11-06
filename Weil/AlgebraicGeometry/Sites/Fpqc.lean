module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Weil.Defs.AlgebraicGeometry.Pullbacks
public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.Etale
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtaleFibreProductInEt
public import Weil.Defs.CategoryTheory.Yoneda

/-!
# Fpqc descent of morphisms of schemes

Let `f : T ⟶ S` be a flat, surjective, quasi-compact morphism of schemes and `X`, `X'` schemes
over `S`. Then the descent sequence of morphisms
```
Hom_S(X, X') ⟶ Hom_T(X_T, X'_T) ⇉ Hom_{T ×_S T}(X_{T ×_S T}, X'_{T ×_S T})
```
is exact: base change `u ↦ u_T` is injective, and its image is the set of `T`-morphisms
`g : X_T ⟶ X'_T` with `p₁^* g = p₂^* g`.

## Main results

* `AlgebraicGeometry.DescentSequence.isSheafFor_yoneda_baseChangeProj`: the representable
  presheaf of `X'` on `Over S` satisfies the sheaf condition for the singleton presieve on the
  projection `X_T ⟶ X`.
* `AlgebraicGeometry.DescentSequence.baseChangeHom_injective_and_range_eq`: the exactness of the
  descent sequence of morphisms.

## Implementation notes

The projection `X_T ⟶ X` is the base change of `f` along `X ⟶ S`, hence flat, surjective and
quasi-compact, so it is an effective epimorphism in the category of schemes
(`AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat`, whose proof is the
reduction to the affine case by quasi-compactness). Effective descent of a morphism of schemes
along it gives the sheaf condition in `Over S`, since a morphism out of `X` is over `S` as soon as
its composite with the epimorphism `X_T ⟶ X` is. The exactness of the sequence is then
`AlgebraicGeometry.DescentSequence.isSheafFor_singleton_iff`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.DescentSequence

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- For `f` flat, surjective and quasi-compact, the representable presheaf of `X'` on `Over S`
is a sheaf for the singleton presieve on the projection `X_T ⟶ X`. -/
theorem isSheafFor_yoneda_baseChangeProj [Flat f] [Surjective f] [QuasiCompact f]
    (X X' : Over S) :
    Presieve.IsSheafFor (yoneda.obj X') (Presieve.singleton (baseChangeProj f X)) := by
  have hy : ∀ {Z W : Over S} (p : Z ⟶ W) (y : W ⟶ X'), (yoneda.obj X').map p.op y = p ≫ y :=
    fun _ _ => rfl
  rw [Presieve.isSheafFor_singleton]
  simp only [hy]
  intro x hx
  have hπ : EffectiveEpi (pullback.fst X.hom f) := inferInstance
  have hc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback X.hom f),
      g₁ ≫ pullback.fst X.hom f = g₂ ≫ pullback.fst X.hom f → g₁ ≫ x.left = g₂ ≫ x.left := by
    intro Z g₁ g₂ hg
    let Z' : Over S := Over.mk (g₁ ≫ (baseChangeOver f X).hom)
    let q₁ : Z' ⟶ baseChangeOver f X := Over.homMk g₁ rfl
    let q₂ : Z' ⟶ baseChangeOver f X := Over.homMk g₂ (by
      simp only [Z', Over.mk_hom, ← Category.assoc, ← pullback.condition]
      simp only [Category.assoc, reassoc_of% hg])
    have := hx q₁ q₂ (by ext; simpa [q₁, q₂] using hg)
    simpa [q₁, q₂] using congrArg CommaMorphism.left this
  let y₀ : X.left ⟶ X'.left := EffectiveEpi.desc (pullback.fst X.hom f) x.left hc
  have hy₀ : pullback.fst X.hom f ≫ y₀ = x.left := EffectiveEpi.fac _ _ _
  have hw : y₀ ≫ X'.hom = X.hom := by
    rw [← cancel_epi (pullback.fst X.hom f), reassoc_of% hy₀, pullback.condition]
    simp
  refine ⟨Over.homMk y₀ hw, ?_, fun v hv => ?_⟩
  · apply Over.OverMorphism.ext
    simpa using hy₀
  · have hv' : baseChangeProj f X ≫ v = x := hv
    apply Over.OverMorphism.ext
    rw [← cancel_epi (pullback.fst X.hom f)]
    simpa [hy₀] using congrArg CommaMorphism.left hv'

/-- **Fpqc descent of morphisms of schemes.** Let `f : T ⟶ S` be flat, surjective and
quasi-compact and `X`, `X'` schemes over `S`. Then base change `u ↦ u_T` from `S`-morphisms
`X ⟶ X'` to `T`-morphisms `X_T ⟶ X'_T` is injective, and its image is the set of `T`-morphisms
`g` with `p₁^* g = p₂^* g`. -/
@[weil "lem_fka3_fpqc_descent_morphisms"]
theorem baseChangeHom_injective_and_range_eq [Flat f] [Surjective f] [QuasiCompact f]
    (X X' : Over S) :
    Function.Injective (baseChangeHom f X X') ∧
      Set.range (baseChangeHom f X X') =
        {g | pullbackHom f X X' _ (fst_comp_eq f) g =
          pullbackHom f X X' _ (snd_comp_eq f) g} :=
  (isSheafFor_singleton_iff f X X').1 (isSheafFor_yoneda_baseChangeProj f X X')

end AlgebraicGeometry.DescentSequence

end

/-! ### Representable presheaves on the étale category are sheaves -/

/-!
# Representable presheaves on the étale category are sheaves

Let `S` be a scheme and `X'` an `S`-scheme. The presheaf `h_{X'} = Hom_S(-, X')` on the étale
category `Et(S)` of noetherian separated étale `S`-schemes is an étale sheaf of sets: for every
object `U` of `Et(S)` and every family `(φᵢ : Uᵢ ⟶ U)ᵢ` of morphisms of `Et(S)` whose images
cover `U`, the map
`Hom_S(U, X') ⟶ {(sᵢ) ∈ ∏ᵢ Hom_S(Uᵢ, X') | sᵢ, sⱼ agree on Uᵢ ×_U Uⱼ}` is bijective.

The proof descends morphisms of schemes along the étale covering: a jointly surjective family
of étale morphisms is a covering for the fppf topology on schemes, which is subcanonical, so the
functor of points of the scheme underlying `X'` satisfies the sheaf condition for it. A family
compatible in `Et(S)` is compatible in the category of schemes because `Et(S)` contains the
fibre products `Uᵢ ×_U Uⱼ`, and the glued morphism is a morphism over `S` because the covering
is an epimorphic family.

## Main results

* `AlgebraicGeometry.Scheme.isSheafFor_yoneda_ofArrows_of_etale`: the functor of points of a
  scheme satisfies the sheaf condition for a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.representablePresheaf.isSheafFor_ofArrows`: `h_{X'}` satisfies the sheaf
  condition for every family of morphisms of `Et(S)` whose images cover the target.
* `AlgebraicGeometry.representablePresheaf.isSheafFor_ofArrows_of_isEtaleCovering`: the same
  for étale coverings (finite jointly surjective families).

## Implementation notes

The sheaf condition is stated as `CategoryTheory.Presieve.IsSheafFor` for the presieve
generated by the covering family; by `CategoryTheory.Presieve.isSheafFor_arrows_iff` this is the
bijectivity of `s ↦ (φᵢ^* s)ᵢ` onto the compatible families, and compatibility may be tested on
the fibre products `Uᵢ ×_U Uⱼ`, which exist in `Et(S)`. The main statement allows families
indexed by an arbitrary type; the étale coverings of Freitag–Kiehl are the finite ones.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The functor of points of a scheme `Y` satisfies the sheaf condition for a jointly surjective
family of étale morphisms: such a family is an fppf covering, and the fppf topology is
subcanonical. -/
theorem Scheme.isSheafFor_yoneda_ofArrows_of_etale {U : Scheme.{u}} {ι : Type*}
    {V : ι → Scheme.{u}} (φ : ∀ i, V i ⟶ U) [∀ i, Etale (φ i)]
    (hφ : ∀ x : U, ∃ i, x ∈ Set.range (φ i)) (Y : Scheme.{u}) :
    Presieve.IsSheafFor (yoneda.obj Y) (Presieve.ofArrows V φ) := by
  have hmem : Presieve.ofArrows V φ ∈ Scheme.fppfPrecoverage U := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hφ, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  have hsh := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) (yoneda.obj Y)).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hmem)
  exact hsh

namespace representablePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Representable presheaves are étale sheaves.** For every `S`-scheme `X'`, the presheaf
`h_{X'}` on `Et(S)` satisfies the sheaf condition for every family `(φᵢ : Uᵢ ⟶ U)ᵢ` of morphisms
of `Et(S)` whose images cover `U`. -/
@[weil "lem_fk102_representable_is_sheaf"]
theorem isSheafFor_ofArrows (X' : Over S) {U : SmallNoetherianSeparatedEtale B S hS}
    {ι : Type*} {V : ι → SmallNoetherianSeparatedEtale B S hS} (φ : ∀ i, V i ⟶ U)
    (hφ : ∀ x : (toScheme B S hS).obj U, ∃ i, x ∈ Set.range ((toScheme B S hS).map (φ i))) :
    Presieve.IsSheafFor (representablePresheaf B S hS X') (Presieve.ofArrows V φ) := by
  have hY := Scheme.isSheafFor_yoneda_ofArrows_of_etale
    (fun i ↦ (toScheme B S hS).map (φ i)) hφ X'.left
  rw [Presieve.isSheafFor_arrows_iff] at hY ⊢
  intro x hx
  -- the underlying family of morphisms of schemes
  let y : ∀ i, (toScheme B S hS).obj (V i) ⟶ X'.left := fun i ↦ (x i).left
  have hy : Presieve.Arrows.Compatible (yoneda.obj X'.left)
      (fun i ↦ (toScheme B S hS).map (φ i)) y := by
    intro i j Z gi gj hg
    have hc := hx i j (pullbackObj (φ i) (φ j)) (pullbackFst (φ i) (φ j))
      (pullbackSnd (φ i) (φ j)) (isPullback_pullbackFst_pullbackSnd (φ i) (φ j)).w
    have hc' : pullback.fst ((toScheme B S hS).map (φ i)) ((toScheme B S hS).map (φ j)) ≫ y i =
        pullback.snd ((toScheme B S hS).map (φ i)) ((toScheme B S hS).map (φ j)) ≫ y j :=
      congrArg CommaMorphism.left hc
    let gi' : Z ⟶ (toScheme B S hS).obj (V i) := gi
    let gj' : Z ⟶ (toScheme B S hS).obj (V j) := gj
    have hg' : gi' ≫ (toScheme B S hS).map (φ i) = gj' ≫ (toScheme B S hS).map (φ j) := hg
    change gi' ≫ y i = gj' ≫ y j
    calc gi' ≫ y i = pullback.lift gi' gj' hg' ≫
          pullback.fst ((toScheme B S hS).map (φ i)) ((toScheme B S hS).map (φ j)) ≫ y i := by
            rw [pullback.lift_fst_assoc]
      _ = pullback.lift gi' gj' hg' ≫
          pullback.snd ((toScheme B S hS).map (φ i)) ((toScheme B S hS).map (φ j)) ≫ y j := by
            rw [hc']
      _ = gj' ≫ y j := by rw [pullback.lift_snd_assoc]
  obtain ⟨t, ht, htuniq⟩ := hY y hy
  have ht' : ∀ i, (toScheme B S hS).map (φ i) ≫ t = y i := ht
  -- the glued morphism lies over `S`
  have hS' : t ≫ X'.hom = structureMorphism U := by
    have hYS := Scheme.isSheafFor_yoneda_ofArrows_of_etale
      (fun i ↦ (toScheme B S hS).map (φ i)) hφ S
    rw [Presieve.isSheafFor_arrows_iff] at hYS
    obtain ⟨_, -, huniq⟩ := hYS (fun i ↦ structureMorphism (V i)) (by
      intro i j Z gi gj hg
      have hg' : gi ≫ (toScheme B S hS).map (φ i) = gj ≫ (toScheme B S hS).map (φ j) := hg
      change gi ≫ structureMorphism (V i) = gj ≫ structureMorphism (V j)
      rw [← toScheme_map_comp_structureMorphism (φ i),
        ← toScheme_map_comp_structureMorphism (φ j), ← Category.assoc, hg', Category.assoc])
    refine (huniq _ fun i ↦ ?_).trans (huniq _ fun i ↦ ?_).symm
    · change (toScheme B S hS).map (φ i) ≫ t ≫ X'.hom = structureMorphism (V i)
      rw [← Category.assoc, ht' i]
      exact Over.w (x i)
    · exact toScheme_map_comp_structureMorphism (φ i)
  refine ⟨Over.homMk (U := (toOver B S hS).obj U) (V := X') t hS', fun i ↦ ?_, fun t₂ ht₂ ↦ ?_⟩
  · exact Over.OverMorphism.ext (ht' i)
  · exact Over.OverMorphism.ext
      (htuniq t₂.left fun i ↦ congrArg CommaMorphism.left (ht₂ i))

/-- **Representable presheaves are étale sheaves**, for étale coverings: `h_{X'}` satisfies the
sheaf condition for every finite family of morphisms of `Et(S)` whose images cover the
target. -/
@[weil "lem_fk102_representable_is_sheaf"]
theorem isSheafFor_ofArrows_of_isEtaleCovering (X' : Over S)
    {U : SmallNoetherianSeparatedEtale B S hS} {ι : Type*}
    {V : ι → SmallNoetherianSeparatedEtale B S hS} (φ : ∀ i, V i ⟶ U)
    (hφ : Scheme.IsEtaleCovering fun i ↦ (toScheme B S hS).map (φ i)) :
    Presieve.IsSheafFor (representablePresheaf B S hS X') (Presieve.ofArrows V φ) :=
  isSheafFor_ofArrows X' φ hφ.exists_mem_range

end representablePresheaf

end AlgebraicGeometry

end
