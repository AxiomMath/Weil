module

public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Sites.FreeModuleSheafSections
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeAdjunction

/-!
# The inverse image of a representable sheaf on the small étale site

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B` and let `Z` be an étale
`S`-scheme of the small étale site of `S`. The base change `T ×_S Z`, with its projection to `T`,
is an étale `T`-scheme of the small étale site of `T` (`AlgebraicGeometry.smallEtaleBaseChange`),
and the inverse image `f^* h_Z` of the sheaf represented by `Z` is the sheaf represented by
`T ×_S Z`, naturally in `Z`.

The proof is by corepresentability. For a sheaf `F` on the small étale site of `T`, the
adjunction `f^* ⊣ f_*` and the Yoneda lemma for sheaves give
`Hom(f^* h_Z, F) ≃ Hom(h_Z, f_* F) ≃ (f_* F)(Z) = F(T ×_S Z)`, and the Yoneda lemma alone gives
`Hom(h_{T ×_S Z}, F) ≃ F(T ×_S Z)`, naturally in `F`; two objects corepresenting the same functor
are canonically isomorphic.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageUliftYonedaIso` — `f^* h_Z ≅ h_{T ×_S Z}` for the
  Yoneda sheaves of the small étale sites, natural in `Z`.
* `AlgebraicGeometry.smallEtaleInverseImageRepresentableSheafIso` — the same for the sheaves
  `h_Z : U ↦ Hom_S(U, Z)` of `AlgebraicGeometry.SmallEtale.representableSheaf`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageUliftYonedaIso_hom_app_comp` — the equation
  characterising the isomorphism: under the adjunction and the Yoneda bijections, precomposing
  with it is the identity on sections over `T ×_S Z`.

## Implementation notes

The inverse image `f^*` is taken with values in `Type (max (u + 1) w)`, where `u` is the
universe of the schemes: the small étale site has objects in `Type (u + 1)` and morphisms in
`Type u`, and colimits of that size are needed to build `f^*`. The sheaf `h_Z`, whose values
`Hom_S(U, Z)` lie in `Type u`, is therefore lifted along `uliftFunctor` before `f^*` is applied.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The functor `F ↦ (f_* F)(Z)` on sheaves of sets on the small étale site of `T`, which both
`f^* h_Z` and `h_{T ×_S Z}` corepresent. -/
abbrev smallEtaleSectionsOfDirectImage (Z : SmallEtale B S.obj S.property) :
    Sheaf (SmallEtale.topology B T.obj T.property) (Type (max (u + 1) w)) ⥤
      Type (max (u + 1) w) :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) w))
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) ⋙
    (sheafSections (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) w))).obj (op Z)

/-- `f^* h_Z` corepresents `F ↦ (f_* F)(Z)`: the adjunction `f^* ⊣ f_*` followed by the Yoneda
bijection for sheaves. -/
def corepresentableBySmallEtaleInverseImageUliftYoneda (Z : SmallEtale B S.obj S.property) :
    (smallEtaleSectionsOfDirectImage.{w} B f Z).CorepresentableBy
      ((smallEtaleInverseImage B f (Type (max (u + 1) w))).obj
        ((SmallEtale.topology B S.obj S.property).uliftYoneda.{max (u + 1) w}.obj Z)) where
  homEquiv := ((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) w))).homEquiv _ _).trans
    (SmallEtale.topology B S.obj S.property).uliftYonedaEquiv
  homEquiv_comp g h := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right,
      (SmallEtale.topology B S.obj S.property).uliftYonedaEquiv_comp]
    rfl

/-- `h_{T ×_S Z}` corepresents `F ↦ (f_* F)(Z)`: the Yoneda bijection for sheaves. -/
def corepresentableBySmallEtaleUliftYonedaBaseChange (Z : SmallEtale B S.obj S.property) :
    (smallEtaleSectionsOfDirectImage.{w} B f Z).CorepresentableBy
      ((SmallEtale.topology B T.obj T.property).uliftYoneda.{max (u + 1) w}.obj
        ((smallEtaleBaseChange B f).obj Z)) where
  homEquiv := (SmallEtale.topology B T.obj T.property).uliftYonedaEquiv
  homEquiv_comp g h := (SmallEtale.topology B T.obj T.property).uliftYonedaEquiv_comp h g

/-- Naturality in `Z` of the corepresentability bijection of `f^* h_Z`. -/
lemma corepresentableBySmallEtaleInverseImageUliftYoneda_homEquiv_map
    {Z Z' : SmallEtale B S.obj S.property} (g : Z ⟶ Z')
    (F : Sheaf (SmallEtale.topology B T.obj T.property) (Type (max (u + 1) w)))
    (h : (smallEtaleInverseImage B f (Type (max (u + 1) w))).obj
        ((SmallEtale.topology B S.obj S.property).uliftYoneda.{max (u + 1) w}.obj Z') ⟶ F) :
    (corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z).homEquiv
        ((smallEtaleInverseImage B f (Type (max (u + 1) w))).map
          ((SmallEtale.topology B S.obj S.property).uliftYoneda.map g) ≫ h) =
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) w))
        (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj.map g.op
          ((corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z').homEquiv h) := by
  dsimp only [corepresentableBySmallEtaleInverseImageUliftYoneda, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact ((SmallEtale.topology B S.obj S.property).uliftYonedaEquiv_naturality _ _).symm

/-- Naturality in `Z` of the Yoneda bijection of `h_{T ×_S Z}`. -/
lemma corepresentableBySmallEtaleUliftYonedaBaseChange_homEquiv_map
    {Z Z' : SmallEtale B S.obj S.property} (g : Z ⟶ Z')
    (F : Sheaf (SmallEtale.topology B T.obj T.property) (Type (max (u + 1) w)))
    (h : (SmallEtale.topology B T.obj T.property).uliftYoneda.{max (u + 1) w}.obj
        ((smallEtaleBaseChange B f).obj Z') ⟶ F) :
    (corepresentableBySmallEtaleUliftYonedaBaseChange.{w} B f Z).homEquiv
        ((SmallEtale.topology B T.obj T.property).uliftYoneda.map
          ((smallEtaleBaseChange B f).map g) ≫ h) =
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) w))
        (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj.map g.op
          ((corepresentableBySmallEtaleUliftYonedaBaseChange.{w} B f Z').homEquiv h) :=
  ((SmallEtale.topology B T.obj T.property).uliftYonedaEquiv_naturality _ _).symm

/-- Two corepresentations of one functor are compared by the isomorphism of their
corepresenting objects: precomposing with it carries one bijection to the other. -/
private lemma homEquiv_uniqueUpToIso_hom_comp {C : Type*} [Category C] {F : C ⥤ Type*}
    {A A' : C} (e : F.CorepresentableBy A) (e' : F.CorepresentableBy A') {X : C} (g : A' ⟶ X) :
    e.homEquiv ((e.uniqueUpToIso e').hom ≫ g) = e'.homEquiv g := by
  rw [e.homEquiv_comp, e'.homEquiv_eq g]
  congr 1
  rw [Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage]
  simp [NatIso.ofComponents]

/-- **`f^* h_Z ≅ h_{T ×_S Z}`, Yoneda form.** The inverse image of the Yoneda sheaf of an étale
`S`-scheme `Z` is the Yoneda sheaf of the base change `T ×_S Z`, naturally in `Z`. -/
def smallEtaleInverseImageUliftYonedaIso :
    (SmallEtale.topology B S.obj S.property).uliftYoneda.{max (u + 1) w} ⋙
        smallEtaleInverseImage B f (Type (max (u + 1) w)) ≅
      smallEtaleBaseChange B f ⋙
        (SmallEtale.topology B T.obj T.property).uliftYoneda.{max (u + 1) w} :=
  NatIso.ofComponents
    (fun Z ↦ (corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z).uniqueUpToIso
      (corepresentableBySmallEtaleUliftYonedaBaseChange.{w} B f Z)) (by
    intro Z Z' g
    apply (corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z).homEquiv.injective
    have hL := corepresentableBySmallEtaleInverseImageUliftYoneda_homEquiv_map.{w} B f g _
      ((corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z').uniqueUpToIso
        (corepresentableBySmallEtaleUliftYonedaBaseChange.{w} B f Z')).hom
    have hI := homEquiv_uniqueUpToIso_hom_comp
      (corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z')
      (corepresentableBySmallEtaleUliftYonedaBaseChange.{w} B f Z') (𝟙 _)
    rw [Category.comp_id] at hI
    have hY := corepresentableBySmallEtaleUliftYonedaBaseChange_homEquiv_map.{w} B f g
      ((SmallEtale.topology B T.obj T.property).uliftYoneda.{max (u + 1) w}.obj
        ((smallEtaleBaseChange B f).obj Z')) (𝟙 _)
    rw [Category.comp_id] at hY
    dsimp only [Functor.comp_map]
    rw [hL, hI, ← hY]
    exact (homEquiv_uniqueUpToIso_hom_comp _ _ _).symm)

/-- The equation characterising `smallEtaleInverseImageUliftYonedaIso`: under the adjunction
`f^* ⊣ f_*` and the Yoneda bijections for sheaves, precomposing with its component at `Z` is the
identity on the sections of `F` over `T ×_S Z`. -/
lemma smallEtaleInverseImageUliftYonedaIso_hom_app_comp (Z : SmallEtale B S.obj S.property)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) (Type (max (u + 1) w)))
    (g : (SmallEtale.topology B T.obj T.property).uliftYoneda.{max (u + 1) w}.obj
      ((smallEtaleBaseChange B f).obj Z) ⟶ F) :
    (SmallEtale.topology B S.obj S.property).uliftYonedaEquiv
        (((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) w))).homEquiv _ _)
          (((smallEtaleInverseImageUliftYonedaIso.{w} B f).app Z).hom ≫ g)) =
      (SmallEtale.topology B T.obj T.property).uliftYonedaEquiv g :=
  homEquiv_uniqueUpToIso_hom_comp (corepresentableBySmallEtaleInverseImageUliftYoneda.{w} B f Z)
    (corepresentableBySmallEtaleUliftYonedaBaseChange.{w} B f Z) g

/-- **The inverse image of a representable sheaf.** For a morphism `f : T ⟶ S` and an étale
`S`-scheme `Z`, the base change `T ×_S Z` is an étale `T`-scheme
(`smallEtaleBaseChange B f`), and `f^* h_Z ≅ h_{T ×_S Z}` as sheaves of sets on the small étale
site of `T`, naturally in `Z`. Here `h_Z : U ↦ Hom_S(U, Z)` is
`SmallEtale.representableSheaf`, lifted to the universe in which `f^*` is formed. -/
@[weil "lem_fk102_inverse_image_of_representable"]
def smallEtaleInverseImageRepresentableSheafIso :
    SmallEtale.representableSheaf B S.obj S.property ⋙
        sheafCompose (SmallEtale.topology B S.obj S.property) uliftFunctor.{max (u + 1) w} ⋙
          smallEtaleInverseImage B f (Type (max (u + 1) w)) ≅
      smallEtaleBaseChange B f ⋙ SmallEtale.representableSheaf B T.obj T.property ⋙
        sheafCompose (SmallEtale.topology B T.obj T.property) uliftFunctor.{max (u + 1) w} :=
  Functor.isoWhiskerRight (SmallEtale.representableSheafIsoYoneda B S.obj S.property)
      (sheafCompose (SmallEtale.topology B S.obj S.property) uliftFunctor.{max (u + 1) w} ⋙
        smallEtaleInverseImage B f (Type (max (u + 1) w))) ≪≫
    smallEtaleInverseImageUliftYonedaIso.{w} B f ≪≫
    Functor.isoWhiskerLeft (smallEtaleBaseChange B f)
      (Functor.isoWhiskerRight (SmallEtale.representableSheafIsoYoneda B T.obj T.property)
        (sheafCompose (SmallEtale.topology B T.obj T.property) uliftFunctor.{max (u + 1) w})).symm

end AlgebraicGeometry

end

/-! ### The inverse image of a constant sheaf on the small étale site -/

/-!
# The inverse image of a constant sheaf on the small étale site

Let `f : Z ⟶ X` be a morphism of schemes of a big étale site `B` and let `M` be a set (or, more
generally, an object of a coefficient category `A`). The inverse image `f^*` of the constant
sheaf `M_X` on the small étale site of `X` is the constant sheaf `M_Z` on the small étale site
of `Z`, naturally in `M`.

Both `constantSheaf ⋙ f^*` and `constantSheaf` are left adjoint to sections over the final
object `Z / Z` of the small étale site of `Z`: the constant sheaf functor is left adjoint to
sections over a final object, `f^*` is left adjoint to the direct image `f_*`, and
`(f_* F)(X / X) = F(Z ×_X X) = F(Z / Z)` because base change carries the final object to a final
object. Uniqueness of left adjoints gives the isomorphism.

## Main definitions

* `AlgebraicGeometry.constantSheafCompSmallEtaleInverseImageIso` — `constantSheaf ⋙ f^* ≅
  constantSheaf`, an isomorphism of functors, i.e. `f^*(M_X) ≅ M_Z` naturally in `M`.
* `AlgebraicGeometry.smallEtaleInverseImageConstantSheafIso` — its component at `M`.

## Implementation notes

The constant sheaf is Mathlib's `CategoryTheory.constantSheaf`, the sheafification of the
constant presheaf, and the inverse image is `AlgebraicGeometry.smallEtaleInverseImage`. The
statement is made for an arbitrary coefficient category `A` with the colimits needed for `f^*`;
sheaves of sets are the case `A = Type (u + 1)`, sheaves of abelian groups the case
`A = AddCommGrpCat.{u + 1}`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Z : B.Scheme} (f : Z ⟶ X)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
  [HasWeakSheafify (SmallEtale.topology B Z.obj Z.property) A]

/-- **The inverse image of a constant sheaf is constant.** For a morphism `f : Z ⟶ X` the
inverse image `f^*` carries the constant sheaf `M_X` to the constant sheaf `M_Z`, naturally in
`M`: an isomorphism of functors `constantSheaf ⋙ f^* ≅ constantSheaf`. -/
@[weil "lem_fk104_inverse_image_constant_sheaf"]
def constantSheafCompSmallEtaleInverseImageIso :
    constantSheaf (SmallEtale.topology B X.obj X.property) A ⋙ smallEtaleInverseImage B f A ≅
      constantSheaf (SmallEtale.topology B Z.obj Z.property) A :=
  Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso (smallEtaleBaseChange B f)
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property) A
    (SmallEtale.finalIsTerminal B X.obj X.property)
    (smallEtaleBaseChange_finalIsTerminal B f) (Iso.refl _)

/-- The inverse image of the constant sheaf `M_X` is the constant sheaf `M_Z`. -/
def smallEtaleInverseImageConstantSheafIso (M : A) :
    (smallEtaleInverseImage B f A).obj
        ((constantSheaf (SmallEtale.topology B X.obj X.property) A).obj M) ≅
      (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj M :=
  (constantSheafCompSmallEtaleInverseImageIso B f A).app M

/-- The isomorphism `f^*(M_X) ≅ M_Z` is natural in `M`. -/
@[reassoc]
lemma smallEtaleInverseImageConstantSheafIso_hom_naturality {M N : A} (φ : M ⟶ N) :
    (smallEtaleInverseImage B f A).map
        ((constantSheaf (SmallEtale.topology B X.obj X.property) A).map φ) ≫
        (smallEtaleInverseImageConstantSheafIso B f A N).hom =
      (smallEtaleInverseImageConstantSheafIso B f A M).hom ≫
        (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).map φ :=
  (constantSheafCompSmallEtaleInverseImageIso B f A).hom.naturality φ

end AlgebraicGeometry

end

/-! ### The free sheaf of `Λ`-modules commutes with inverse image -/

/-!
# The free sheaf of `Λ`-modules commutes with inverse image

Let `Λ` be a ring, `f : T ⟶ S` a morphism of schemes of a big étale site and `M` a sheaf of sets
on the small étale site of `S`. The free sheaf of `Λ`-modules `M^Λ` on `M` is the sheafification
of the presheaf `U ↦ Λ^(M(U))`. Then the inverse image of `M^Λ` as a sheaf of `Λ`-modules is
canonically isomorphic to the free sheaf of `Λ`-modules on the inverse image `f^* M` of `M` as a
sheaf of sets:
`f^* (M^Λ) ≅ (f^* M)^Λ`, naturally in `M`.

Both functors `M ↦ f^* (M^Λ)` and `M ↦ (f^* M)^Λ` are left adjoint to the functor sending a sheaf
of `Λ`-modules `H` on the small étale site of `T` to the underlying sheaf of sets of `f_* H`, which
is the direct image of the underlying sheaf of sets of `H`; so they are isomorphic by uniqueness
of left adjoints.

## Main results

* `AlgebraicGeometry.smallEtaleFreeModuleSheafInverseImageIso` — `f^* (M^Λ) ≅ (f^* M)^Λ`,
  naturally in `M`.
* `AlgebraicGeometry.smallEtaleFreeModuleSheafInverseImageObjIso` — the same isomorphism for one
  sheaf of sets `M`.
* `AlgebraicGeometry.smallEtaleInverseImage_map_smulEnd` — the inverse image of multiplication by
  `λ ∈ Λ` on a sheaf of `Λ`-modules is multiplication by `λ` on its inverse image.

## Implementation notes

The free sheaf of `Λ`-modules is `CategoryTheory.Sheaf.composeAndSheafify` of `ModuleCat.free Λ`,
and the inverse image of sheaves of `Λ`-modules is the inverse image
`AlgebraicGeometry.smallEtaleInverseImage` with values in `ModuleCat Λ`, the left adjoint of the
direct image of sheaves of `Λ`-modules. The source defines the inverse image of a sheaf of
`Λ`-modules as its inverse image as an abelian sheaf, with `Λ` acting by the inverse images of
the multiplications; with values in `ModuleCat Λ` the action of `λ` on the inverse image is the
inverse image of the action of `λ` (`AlgebraicGeometry.smallEtaleInverseImage_map_smulEnd`).
The isomorphism is the Stacks project's
`CategoryTheory.Sheaf.composeAndSheafifyFreeSheafPullbackIso` for the base change functor of
small étale sites. The ring `Λ` need not be commutative.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (Λ : Type (u + 1)) [Ring Λ]

/-- **The free sheaf of `Λ`-modules commutes with inverse image.** For a morphism `f : T ⟶ S`,
the inverse image of the free sheaf of `Λ`-modules `M^Λ` on a sheaf of sets `M` on the small
étale site of `S` is the free sheaf of `Λ`-modules on `f^* M`, naturally in `M`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_pullback"]
def smallEtaleFreeModuleSheafInverseImageIso :
    Sheaf.composeAndSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.free Λ) ⋙
        smallEtaleInverseImage B f (ModuleCat.{u + 1} Λ) ≅
      smallEtaleInverseImage B f (Type (u + 1)) ⋙
        Sheaf.composeAndSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.free Λ) :=
  Sheaf.composeAndSheafifyFreeSheafPullbackIso (SmallEtale.topology B S.obj S.property) Λ
    (SmallEtale.topology B T.obj T.property) (smallEtaleBaseChange B f)

/-- **`f^* (M^Λ) ≅ (f^* M)^Λ`.** For a sheaf of sets `M` on the small étale site of `S`, the
inverse image of the free sheaf of `Λ`-modules on `M` is isomorphic, as a sheaf of `Λ`-modules,
to the free sheaf of `Λ`-modules on the inverse image of `M`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_pullback"]
def smallEtaleFreeModuleSheafInverseImageObjIso
    (M : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    (smallEtaleInverseImage B f (ModuleCat.{u + 1} Λ)).obj
        ((Sheaf.composeAndSheafify (SmallEtale.topology B S.obj S.property)
          (ModuleCat.free Λ)).obj M) ≅
      (Sheaf.composeAndSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.free Λ)).obj
        ((smallEtaleInverseImage B f (Type (u + 1))).obj M) :=
  (smallEtaleFreeModuleSheafInverseImageIso B f Λ).app M

/-- The isomorphism `f^* (M^Λ) ≅ (f^* M)^Λ` is natural in the sheaf of sets `M`. -/
@[reassoc]
lemma smallEtaleFreeModuleSheafInverseImageObjIso_hom_naturality
    {M M' : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))} (φ : M ⟶ M') :
    (smallEtaleInverseImage B f (ModuleCat.{u + 1} Λ)).map
        ((Sheaf.composeAndSheafify (SmallEtale.topology B S.obj S.property)
          (ModuleCat.free Λ)).map φ) ≫
        (smallEtaleFreeModuleSheafInverseImageObjIso B f Λ M').hom =
      (smallEtaleFreeModuleSheafInverseImageObjIso B f Λ M).hom ≫
        (Sheaf.composeAndSheafify (SmallEtale.topology B T.obj T.property)
          (ModuleCat.free Λ)).map ((smallEtaleInverseImage B f (Type (u + 1))).map φ) :=
  (smallEtaleFreeModuleSheafInverseImageIso B f Λ).hom.naturality φ

/-- **`f^* (λ_G) = λ_{f^* G}`.** The inverse image of multiplication by `r` on a sheaf of
`Λ`-modules `G` on the small étale site of `S` is multiplication by `r` on `f^* G`. -/
lemma smallEtaleInverseImage_map_smulEnd {Λ : Type (u + 1)} [CommRing Λ] (r : Λ)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)) :
    (smallEtaleInverseImage B f (ModuleCat.{u + 1} Λ)).map
        (Sheaf.smulEnd (SmallEtale.topology B S.obj S.property) r G) =
      Sheaf.smulEnd (SmallEtale.topology B T.obj T.property) r
        ((smallEtaleInverseImage B f (ModuleCat.{u + 1} Λ)).obj G) :=
  Sheaf.map_smulEnd_of_adjunction _ _ (smallEtaleInverseImageAdjunction B f (ModuleCat.{u + 1} Λ))
    (fun _ _ ↦ rfl) r G

end AlgebraicGeometry

end

/-! ### The inverse image of étale sheaves of sets preserves finite products -/

/-!
# The inverse image of étale sheaves of sets preserves finite products

Let `h : Z' ⟶ Z` be a morphism of schemes of a big étale site `B`. The inverse image
`h^*` from sheaves of sets on the small étale site of `Z` to sheaves of sets on the small étale
site of `Z'` preserves finite limits. In particular, for sheaves `𝒜, ℬ` on the small étale site
of `Z`, the comparison map `h^*(𝒜 × ℬ) ⟶ h^* 𝒜 × h^* ℬ` with components `h^*(pr₁)` and
`h^*(pr₂)` is an isomorphism, and `h^*` sends the terminal sheaf (one point over every object)
to the terminal sheaf.

The inverse image is the sheafification of the left Kan extension along the opposite of base
change. Base change of small étale sites preserves finite limits, so it is representably flat:
the categories indexing the colimits that compute the Kan extension are filtered, and filtered
colimits of sets commute with finite limits. Sheafification is left exact.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_preservesFiniteLimits_types` — `h^*` on sheaves of
  sets preserves finite limits.
* `AlgebraicGeometry.isIso_prodComparison_smallEtaleInverseImage` — the map
  `h^*(𝒜 × ℬ) ⟶ h^* 𝒜 × h^* ℬ` is an isomorphism.
* `AlgebraicGeometry.isTerminalSmallEtaleInverseImageObjTerminal` — `h^*` of the terminal sheaf
  is terminal.

## Implementation notes

The sheaves of sets take values in `Type (u + 1)` for the scheme universe `u`, the coefficients
at which the colimits computing the Kan extension exist. The schemes need not be noetherian or
separated.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The inverse image of sheaves of sets on the small étale sites preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_types :
    PreservesFiniteLimits (smallEtaleInverseImage B f (Type (u + 1))) := by
  let G := smallEtaleBaseChange B f
  have : PreservesFiniteLimits
      (G.op.lan : ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ Type (u + 1)) ⥤ _) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation _ J
    intro K
    have : IsFiltered (CostructuredArrow G.op K) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G K.unop)
    exact preservesLimitsOfShape_of_natIso
      (Stacks.Topology.lanCompEvaluationIsoColim (Type (u + 1)) G.op K).symm
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1))
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)) ⋙ G.op.lan ⋙
        presheafToSheaf (SmallEtale.topology B T.obj T.property) (Type (u + 1)))
    infer_instance
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso G (Type (u + 1))
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).symm

/-- **The inverse image commutes with binary products.** For sheaves of sets `𝒜, ℬ` on the small
étale site of `S`, the map `f^*(𝒜 × ℬ) ⟶ f^* 𝒜 × f^* ℬ` with components `f^*(pr₁)` and
`f^*(pr₂)` is an isomorphism. -/
@[weil "lem_fk104_inverse_image_preserves_finite_products"]
theorem isIso_prodComparison_smallEtaleInverseImage
    (𝒜 ℬ : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    IsIso (prodComparison (smallEtaleInverseImage B f (Type (u + 1))) 𝒜 ℬ) :=
  inferInstance

/-- **The inverse image of the terminal sheaf is terminal.** The inverse image `f^*` sends the
terminal sheaf of sets on the small étale site of `S` (one point over every object) to a terminal
sheaf on the small étale site of `T`. -/
@[weil "lem_fk104_inverse_image_preserves_finite_products"]
def isTerminalSmallEtaleInverseImageObjTerminal :
    IsTerminal ((smallEtaleInverseImage B f (Type (u + 1))).obj
      (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))) :=
  isLimitOfHasTerminalOfPreservesLimit (smallEtaleInverseImage B f (Type (u + 1)))

end AlgebraicGeometry

end

/-! ### The inverse image along an étale morphism is restriction -/

/-!
# The inverse image along an étale morphism is restriction

Let `B` be a big étale site containing a scheme `X`, and let `U` be an object of the small étale
site of `X`, with structure morphism `u : U ⟶ X`, which is étale. Post-composition with `u`
regards an étale `U`-scheme as an étale `X`-scheme; this is a continuous functor
`AlgebraicGeometry.SmallEtale.postcompose` from the small étale site of `U` to that of `X`, and the
restriction `G|_U` of a sheaf `G` on the small étale site of `X` is `V ↦ G(V → U → X)`.

The inverse image `u^* G` is canonically isomorphic to `G|_U`, naturally in `G`. Both functors are
left adjoint to the direct image `F ↦ (W ↦ F(U ×_X W))`: the inverse image by construction, and
restriction because post-composition with `u` is left adjoint to base change along `u`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafRestriction` — the restriction `G ↦ G|_U` of sheaves on the
  small étale site of `X` to the small étale site of `U`.
* `AlgebraicGeometry.SmallEtale.sheafRestrictionAdjunction` — restriction is left adjoint to the
  direct image along `u`.
* `AlgebraicGeometry.SmallEtale.inverseImageIsoSheafRestriction` — the natural isomorphism
  `u^* ≅ (-)|_U`.

## Main results

* `AlgebraicGeometry.SmallEtale.inverseImageIsoSheafRestriction_hom_naturality` — the
  isomorphism `u^* G ≅ G|_U` is natural in `G`.

## Implementation notes

The statement holds for sheaves with values in any category `A` for which the inverse image is
defined; abelian sheaves are the case `A = AddCommGrpCat.{u + 1}`. The proof identifies the two
functors as left adjoints of the same functor, rather than computing the colimit defining the
inverse image presheaf; the two arguments are equivalent, the initial object `(V, id_V)` of the
index category being the unit of the adjunction between post-composition and base change.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 03PM](https://stacks.math.columbia.edu/tag/03PM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- Post-composition with the structure morphism of `U` is continuous: it is the localization
equivalence onto the slice at `U` followed by the forgetful functor of the slice. -/
instance postcompose_isContinuous :
    (postcompose B X hX U).IsContinuous (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (SmallEtale.topology B X hX) := by
  rw [← localizationEquivalence_restriction]
  exact Functor.isContinuous_comp _ _ _ ((SmallEtale.topology B X hX).over U) _

/-- Base change along the structure morphism of `U` is continuous. -/
instance isContinuous_smallEtaleBaseChange_hom :
    (smallEtaleBaseChange B U.obj.hom).IsContinuous (SmallEtale.topology B X hX)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property) :=
  smallEtaleBaseChange_isContinuous B U.obj.hom

variable (A : Type w) [Category.{v} A]

/-- **Restriction of sheaves to `U`.** The sheaf `G|_U : V ↦ G(V → U → X)` on the small étale
site of `U`, for a sheaf `G` on the small étale site of `X`. -/
abbrev sheafRestriction :
    Sheaf (SmallEtale.topology B X hX) A ⥤
      Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) A :=
  (postcompose B X hX U).sheafPushforwardContinuous A
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (SmallEtale.topology B X hX)

/-- Restriction to `U` is left adjoint to the direct image along the structure morphism of `U`,
`F ↦ (W ↦ F(U ×_X W))`. -/
def sheafRestrictionAdjunction :
    sheafRestriction B X hX U A ⊣
      (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous A
        (SmallEtale.topology B X hX) (SmallEtale.topology B U.obj.left.obj U.obj.left.property) :=
  (postcomposeBaseChangeAdjunction B X hX U).sheafPushforwardContinuous (E := A) _ _

variable [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B U.obj.left.obj U.obj.left.property) A]

/-- **The inverse image along an étale morphism is restriction.** For `U` étale over `X`, the
inverse image `u^* G` of a sheaf `G` on the small étale site of `X` along the structure morphism
`u : U ⟶ X` is isomorphic to the restriction `G|_U`, naturally in `G`. -/
@[weil "lem_fk108_open_inverse_image_is_restriction"]
def inverseImageIsoSheafRestriction :
    smallEtaleInverseImage B U.obj.hom A ≅ sheafRestriction B X hX U A :=
  (smallEtaleInverseImageAdjunction B U.obj.hom A).leftAdjointUniq
    (sheafRestrictionAdjunction B X hX U A)

/-- The isomorphism `u^* G ≅ G|_U` is natural in `G`. -/
@[reassoc]
lemma inverseImageIsoSheafRestriction_hom_naturality
    {G G' : Sheaf (SmallEtale.topology B X hX) A} (φ : G ⟶ G') :
    (smallEtaleInverseImage B U.obj.hom A).map φ ≫
        (inverseImageIsoSheafRestriction B X hX U A).hom.app G' =
      (inverseImageIsoSheafRestriction B X hX U A).hom.app G ≫
        (sheafRestriction B X hX U A).map φ :=
  (inverseImageIsoSheafRestriction B X hX U A).hom.naturality φ

end AlgebraicGeometry.SmallEtale

end
