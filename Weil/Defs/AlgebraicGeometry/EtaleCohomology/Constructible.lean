module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian

/-!
# Constructible sheaves on the small étale site

A sheaf of sets `F` on the small étale site of a scheme `X` is *constructible* if there are
finitely many locally closed subschemes `Y₁, …, Yᵣ` of `X` covering `X` such that the inverse
image of `F` along each immersion `Yⱼ ⟶ X` is finite locally constant. A sheaf of abelian groups
is constructible if its underlying sheaf of sets is.

The library's definitions are those of Stacks, Tag 03RW: `AlgebraicGeometry.IsConstructibleSetSheaf`
and `AlgebraicGeometry.IsConstructibleAbelianSheaf` ask, on every affine open `U` of `X`, for a
finite partition of `U` by constructible locally closed subschemes on which the inverse image of
`F` is finite locally constant (for abelian sheaves: finite locally constant as an abelian sheaf).
This file proves that, on a scheme whose underlying space is Noetherian, these are the
definitions of [FK].

## Main results

* `AlgebraicGeometry.isConstructibleFiniteSheaf_iff_exists_immersion_cover`: on a scheme with
  Noetherian underlying space, a sheaf with values in a concrete category is constructible if and
  only if there are finitely many immersions `Yⱼ ⟶ X` jointly surjective onto `X` along each of
  which its inverse image is finite locally constant.
* `AlgebraicGeometry.isConstructibleSetSheaf_iff_exists_immersion_cover`: the case of sheaves of
  sets.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf`: an abelian sheaf
  is constructible if and only if its underlying sheaf of sets is.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_iff_exists_immersion_cover`: the form of the
  definition for sheaves of abelian groups with finitely many immersions.

## Implementation notes

A locally closed subscheme `Y ⊆ X` is recorded by an object `Y` of the big étale site together
with a morphism `Y ⟶ X` which is an immersion; its image is the locally closed subset `|Y|`.
The covering condition `|X| = |Y₁| ∪ ⋯ ∪ |Yᵣ|` is joint surjectivity of the immersions.

Over a Noetherian space every locally closed subset is constructible, which is why the
constructibility of the strata required by Stacks is automatic in the setting of [FK]; and the
Stacks condition on every affine open reduces to one stratification of `X` itself because a
Noetherian space is quasi-compact and quasi-separated (Stacks, Tag 095E).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v t u

namespace AlgebraicGeometry

section Concrete

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (V : SmallEtale B S.obj S.property),
    ((Over.post (X := V) (smallEtaleBaseChange B f)).sheafPushforwardContinuous D
      ((SmallEtale.topology B S.obj S.property).over V)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj V))).IsRightAdjoint]

/-- **Constructibility by a finite cover by locally closed subschemes.** On a scheme `X` whose
underlying space is Noetherian, a sheaf on the small étale site of `X` with values in a concrete
category is constructible if and only if there are finitely many immersions `Yⱼ ⟶ X`, jointly
surjective onto `X`, along each of which the inverse image of the sheaf is finite locally
constant. -/
theorem isConstructibleFiniteSheaf_iff_exists_immersion_cover [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) :
    IsConstructibleFiniteSheaf B X F ↔
      ∃ (n : ℕ) (Y : Fin n → B.Scheme) (j : ∀ i, Y i ⟶ X),
        (∀ i, IsImmersion (B.inclusion.map (j i))) ∧
        (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base ∧
        ∀ i, SmallEtale.IsFiniteLocallyConstant B (Y i).obj (Y i).property (FD := FD) (CD := CD)
          (((smallEtaleBaseChange B (j i)).sheafPullback D
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (Y i).obj (Y i).property)).obj F) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := ((isConstructibleFiniteSheaf_tfae B X F).out 1 3).mp h
    refine ⟨s.n, s.piece, s.inclusion, s.isImmersion, ?_, hs⟩
    simpa using s.covers
  · rintro ⟨n, Y, j, hj, hcover, hF⟩
    have : NoetherianSpace (B.inclusion.obj X) := ‹NoetherianSpace X.obj›
    refine isConstructibleFiniteSheaf_of_constructible_immersion_cover B X F Y j hj
      (fun i => isConstructible_of_isLocallyClosed (hj i).isLocallyClosed_range) hcover
      (fun i => ?_)
    have := hF i
    exact isConstructibleFiniteSheaf_of_isFiniteLocallyConstant B (Y i) _

end Concrete

section Sets

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Constructible sheaves of sets.** On a scheme `X` whose underlying space is Noetherian, a
sheaf of sets on the small étale site of `X` is constructible if and only if there are finitely
many locally closed subschemes `Yⱼ ⟶ X` covering `X` such that each restriction `F|_{Yⱼ}` (the
inverse image along the immersion) is finite locally constant. -/
@[weil "def_fk104_constructible_sheaf"]
theorem isConstructibleSetSheaf_iff_exists_immersion_cover [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∃ (n : ℕ) (Y : Fin n → B.Scheme) (j : ∀ i, Y i ⟶ X),
        (∀ i, IsImmersion (B.inclusion.map (j i))) ∧
        (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base ∧
        ∀ i, SmallEtale.IsFiniteLocallyConstant B (Y i).obj (Y i).property
          ((smallEtaleSetPullback B (j i)).obj F) :=
  isConstructibleFiniteSheaf_iff_exists_immersion_cover B X F

end Sets

section Abelian

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Constructible sheaves of abelian groups.** A sheaf of abelian groups on the small étale site
of `X` is constructible if and only if its underlying sheaf of sets is. -/
@[weil "def_fk104_constructible_sheaf"]
theorem isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B X F ↔
      IsConstructibleSetSheaf B X ((smallEtaleUnderlyingSetSheaf B X).obj F) :=
  ⟨isConstructibleSetSheaf_underlying B X (smallEtaleUnderlyingSetCommutes B X),
    isConstructibleAbelianSheaf_of_underlying B X (smallEtaleUnderlyingSetCommutes B X)⟩

/-- **Constructible sheaves of abelian groups by a finite cover by locally closed subschemes.** On
a scheme `X` whose underlying space is Noetherian, a sheaf of abelian groups on the small étale
site of `X` is constructible if and only if there are finitely many locally closed subschemes
`Yⱼ ⟶ X` covering `X` on each of which the inverse image of its underlying sheaf of sets is finite
locally constant. -/
@[weil "def_fk104_constructible_sheaf"]
theorem isConstructibleAbelianSheaf_iff_exists_immersion_cover [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B X F ↔
      ∃ (n : ℕ) (Y : Fin n → B.Scheme) (j : ∀ i, Y i ⟶ X),
        (∀ i, IsImmersion (B.inclusion.map (j i))) ∧
        (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base ∧
        ∀ i, SmallEtale.IsFiniteLocallyConstant B (Y i).obj (Y i).property
          ((smallEtaleSetPullback B (j i)).obj ((smallEtaleUnderlyingSetSheaf B X).obj F)) := by
  rw [isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf,
    isConstructibleSetSheaf_iff_exists_immersion_cover]

end Abelian

end AlgebraicGeometry
