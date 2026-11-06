module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.PullbackCarrier
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleCategoryFibreProduct
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleCoveringFk101
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringMorphism

/-!
# The coverings of an object of the étale category form a directed system

Let `A` be a commutative ring and `B` an object of the étale category `Et(A)`. For two coverings
`𝔅 = (gᵢ : B ⟶ Bᵢ)_{i ∈ I}` and `𝔅' = (g'ⱼ : B ⟶ B'ⱼ)_{j ∈ J}` of `B`, the family
`(B ⟶ Bᵢ ⊗_B B'ⱼ)_{(i, j) ∈ I × J}` is again a covering of `B`, and the canonical maps
`Bᵢ ⟶ Bᵢ ⊗_B B'ⱼ`, `B'ⱼ ⟶ Bᵢ ⊗_B B'ⱼ` give morphisms of coverings `𝔅 ⟶ 𝔅''` and `𝔅' ⟶ 𝔅''`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.pushoutObj g₁ g₂`: for morphisms `g₁ : B ⟶ C₁`, `g₂ : B ⟶ C₂` of
  `Et(A)`, the object `C₁ ⊗_B C₂` of `Et(A)`, with the canonical morphisms
  `AlgebraicGeometry.EtaleCategory.pushoutInl` and `AlgebraicGeometry.EtaleCategory.pushoutInr`.
- `AlgebraicGeometry.EtaleCategory.Covering.inf 𝔅 𝔅'`: the covering `(Bᵢ ⊗_B B'ⱼ)_{(i, j)}`,
  with the morphisms `Covering.toInfLeft : 𝔅 ⟶ 𝔅.inf 𝔅'` and `Covering.toInfRight : 𝔅' ⟶ 𝔅.inf 𝔅'`.

## Main results

- `AlgebraicGeometry.EtaleCategory.Covering.cocone_objs`: any two coverings of `B` admit
  morphisms to a common covering of `B`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

/-- Every object `X` of `Et(A)` is the image of the étale `A`-algebra `toAlgebra X`. -/
def fromAlgebrasObjToAlgebraIso (X : EtaleCategory A) : (fromAlgebras A).obj (toAlgebra X) ≅ X :=
  ofAlgebraToAlgebraIso X

/-- The morphism of étale `A`-algebras underlying a morphism of `Et(A)`. -/
def toAlgebraHom {X Y : EtaleCategory A} (g : X ⟶ Y) : toAlgebra X ⟶ toAlgebra Y :=
  (fullyFaithfulFromAlgebras A).preimage
    ((fromAlgebrasObjToAlgebraIso X).hom ≫ g ≫ (fromAlgebrasObjToAlgebraIso Y).inv)

lemma fromAlgebras_map_toAlgebraHom {X Y : EtaleCategory A} (g : X ⟶ Y) :
    (fromAlgebras A).map (toAlgebraHom g) =
      (fromAlgebrasObjToAlgebraIso X).hom ≫ g ≫ (fromAlgebrasObjToAlgebraIso Y).inv :=
  (fullyFaithfulFromAlgebras A).map_preimage _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma toAlgebraHom_hom_toRingHom {X Y : EtaleCategory A} (g : X ⟶ Y) :
    (toAlgebraHom g).hom.hom.toRingHom = (ringHom g).hom := rfl

variable {B C₁ C₂ : EtaleCategory A}

/-- The object `C₁ ⊗_B C₂` of `Et(A)` attached to morphisms `g₁ : B ⟶ C₁` and `g₂ : B ⟶ C₂`. -/
abbrev pushoutObj (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) : EtaleCategory A :=
  (fromAlgebras A).obj (tensorProduct (toAlgebraHom g₁) (toAlgebraHom g₂))

/-- The canonical morphism `C₁ ⟶ C₁ ⊗_B C₂`. -/
def pushoutInl (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) : C₁ ⟶ pushoutObj g₁ g₂ :=
  (fromAlgebrasObjToAlgebraIso C₁).inv ≫
    (fromAlgebras A).map (inl (toAlgebraHom g₁) (toAlgebraHom g₂))

/-- The canonical morphism `C₂ ⟶ C₁ ⊗_B C₂`. -/
def pushoutInr (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) : C₂ ⟶ pushoutObj g₁ g₂ :=
  (fromAlgebrasObjToAlgebraIso C₂).inv ≫
    (fromAlgebras A).map (inr (toAlgebraHom g₁) (toAlgebraHom g₂))

@[reassoc]
lemma comp_pushoutInl_eq_comp_pushoutInr (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) :
    g₁ ≫ pushoutInl g₁ g₂ = g₂ ≫ pushoutInr g₁ g₂ := by
  have h₁ : g₁ ≫ (fromAlgebrasObjToAlgebraIso C₁).inv =
      (fromAlgebrasObjToAlgebraIso B).inv ≫ (fromAlgebras A).map (toAlgebraHom g₁) := by
    simp [fromAlgebras_map_toAlgebraHom]
  have h₂ : g₂ ≫ (fromAlgebrasObjToAlgebraIso C₂).inv =
      (fromAlgebrasObjToAlgebraIso B).inv ≫ (fromAlgebras A).map (toAlgebraHom g₂) := by
    simp [fromAlgebras_map_toAlgebraHom]
  rw [pushoutInl, pushoutInr, reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp,
    ← Functor.map_comp, comp_inl_eq_comp_inr]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given primes of `C₁` and `C₂` over the same prime of `B`, some prime of `C₁ ⊗_B C₂` lies over
both. -/
lemma exists_comap_pushoutInl_eq (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (q₁ : PrimeSpectrum C₁.ring)
    (q₂ : PrimeSpectrum C₂.ring)
    (h : PrimeSpectrum.comap (ringHom g₁).hom q₁ = PrimeSpectrum.comap (ringHom g₂).hom q₂) :
    ∃ P : PrimeSpectrum (pushoutObj g₁ g₂).ring,
      PrimeSpectrum.comap (ringHom (pushoutInl g₁ g₂)).hom P = q₁ ∧
      PrimeSpectrum.comap (ringHom (pushoutInr g₁ g₂)).hom P = q₂ := by
  obtain ⟨P, hP, h₁, h₂⟩ := @Ideal.exists_isPrime_tensorProduct_comap_eq (toAlgebra B).obj
    (toAlgebra C₁).obj (toAlgebra C₂).obj _ _ _ (algebraOfHom (toAlgebraHom g₁))
    (algebraOfHom (toAlgebraHom g₂)) q₁.asIdeal q₁.isPrime q₂.asIdeal q₂.isPrime
    (congrArg PrimeSpectrum.asIdeal h)
  exact ⟨⟨P, hP⟩, PrimeSpectrum.ext h₁, PrimeSpectrum.ext h₂⟩

namespace Covering

/-- The common refinement `(B ⟶ Bᵢ ⊗_B B'ⱼ)_{(i, j) ∈ I × J}` of two coverings
`𝔅 = (gᵢ : B ⟶ Bᵢ)_{i ∈ I}` and `𝔅' = (g'ⱼ : B ⟶ B'ⱼ)_{j ∈ J}` of `B`. -/
def inf (𝔅 𝔅' : Covering.{w} B) : Covering.{w} B where
  ι := 𝔅.ι × 𝔅'.ι
  obj k := pushoutObj (𝔅.map k.1) (𝔅'.map k.2)
  map k := 𝔅.map k.1 ≫ pushoutInl (𝔅.map k.1) (𝔅'.map k.2)
  isCovering := by
    have := 𝔅.isCovering.finite
    have := 𝔅'.isCovering.finite
    refine ⟨inferInstance, fun p ↦ ?_⟩
    obtain ⟨i, q, hq⟩ := 𝔅.isCovering.exists_comap_eq p
    obtain ⟨j, q', hq'⟩ := 𝔅'.isCovering.exists_comap_eq p
    obtain ⟨P, hP, -⟩ := exists_comap_pushoutInl_eq (𝔅.map i) (𝔅'.map j) q q' (hq.trans hq'.symm)
    refine ⟨(i, j), P, ?_⟩
    rw [ringHom_comp, CommRingCat.hom_comp, PrimeSpectrum.comap_comp, Function.comp_apply,
      hP, hq]

/-- The morphism of coverings `𝔅 ⟶ 𝔅.inf 𝔅'`, given by `(i, j) ↦ i` and the canonical maps
`Bᵢ ⟶ Bᵢ ⊗_B B'ⱼ`. -/
def toInfLeft (𝔅 𝔅' : Covering.{w} B) : 𝔅 ⟶ 𝔅.inf 𝔅' :=
  HomOver.toHom
    { σ := Prod.fst
      h k := pushoutInl (𝔅.map k.1) (𝔅'.map k.2)
      comm _ := (Category.id_comp _).symm }

/-- The morphism of coverings `𝔅' ⟶ 𝔅.inf 𝔅'`, given by `(i, j) ↦ j` and the canonical maps
`B'ⱼ ⟶ Bᵢ ⊗_B B'ⱼ`. -/
def toInfRight (𝔅 𝔅' : Covering.{w} B) : 𝔅' ⟶ 𝔅.inf 𝔅' :=
  HomOver.toHom
    { σ := Prod.snd
      h k := pushoutInr (𝔅.map k.1) (𝔅'.map k.2)
      comm k := by
        rw [Category.id_comp]
        exact (comp_pushoutInl_eq_comp_pushoutInr _ _).symm }

/-- **The coverings of an object of `Et(A)` are directed.** For any two coverings `𝔅`, `𝔅'` of
`B` there are a covering `𝔅''` of `B` and morphisms of coverings `𝔅 ⟶ 𝔅''` and `𝔅' ⟶ 𝔅''`. -/
@[weil "lem_fk101_coverings_directed"]
theorem cocone_objs (𝔅 𝔅' : Covering.{w} B) :
    ∃ (𝔅'' : Covering.{w} B) (_ : 𝔅 ⟶ 𝔅'') (_ : 𝔅' ⟶ 𝔅''), True :=
  ⟨𝔅.inf 𝔅', toInfLeft 𝔅 𝔅', toInfRight 𝔅 𝔅', trivial⟩

end Covering

end EtaleCategory

end AlgebraicGeometry
