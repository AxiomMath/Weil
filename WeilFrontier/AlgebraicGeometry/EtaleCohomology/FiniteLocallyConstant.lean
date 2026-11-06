module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteTypeLocality

/-!
# The inverse image of a finite locally constant sheaf

Let `f : Z ⟶ X` be a morphism of schemes and `F` a finite locally constant sheaf on the small
étale site of `X`. Then the inverse image `f^* F` is finite locally constant on the small étale
site of `Z`. If `(Uᵢ ⟶ X)` is an étale covering with `F|_{Uᵢ} ≅ (Mᵢ)_{Uᵢ}`, `Mᵢ` finite, then the
base changes `Z ×_X Uᵢ ⟶ Z` form an étale covering of `Z` on which `f^* F` restricts to the
constant sheaves `(Mᵢ)_{Z ×_X Uᵢ}`.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_smallEtaleInverseImage`: the inverse
  image of a finite locally constant sheaf is finite locally constant.

## Implementation notes

The inverse image `f^*` is the inverse image along base change
`AlgebraicGeometry.smallEtaleBaseChange B f`, a continuous left exact functor of small étale
sites, so the result is the general statement for such functors,
`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback`. The coefficient category is an
arbitrary concrete category with the colimits the inverse image needs; sheaves of sets, the case
of the source, are coefficients `Type (u + 1)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Z : B.Scheme} (f : Z ⟶ X)
variable {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ P Q, FunLike (FD P Q) (CD P) (CD Q)] [ConcreteCategory.{w} D FD]
  [HasColimitsOfSize.{u, u + 1} D]
  [∀ (Y : B.Scheme) (U : SmallEtale B Y.obj Y.property),
    HasWeakSheafify ((topology B Y.obj Y.property).over U) D]
  [∀ Y : B.Scheme, HasWeakSheafify (topology B Y.obj Y.property) D]

/-- **The inverse image of a finite locally constant sheaf is finite locally constant.** For a
morphism `f : Z ⟶ X` and a finite locally constant sheaf `F` on the small étale site of `X`, the
inverse image `f^* F` is finite locally constant on the small étale site of `Z`. -/
@[weil "lem_fk104_flc_inverse_image"]
theorem isFiniteLocallyConstant_smallEtaleInverseImage
    (F : Sheaf (topology B X.obj X.property) D)
    (hF : IsFiniteLocallyConstant B X.obj X.property (FD := FD) (CD := CD) F) :
    IsFiniteLocallyConstant B Z.obj Z.property (FD := FD) (CD := CD)
      ((smallEtaleInverseImage B f D).obj F) := by
  have (V : SmallEtale B X.obj X.property) :
      ((Over.post (X := V) (smallEtaleBaseChange B f)).sheafPushforwardContinuous D
        ((topology B X.obj X.property).over V)
        ((topology B Z.obj Z.property).over ((smallEtaleBaseChange B f).obj V))).IsRightAdjoint :=
    inferInstance
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback _ _
    (smallEtaleBaseChange B f) F hF

end AlgebraicGeometry.SmallEtale

end

/-! ### Finite local constancy is étale local -/

/-!
# Finite local constancy is étale local

Let `S` be a scheme and `F` a sheaf on the small étale site of `S`. If there is a family of
objects `Vₖ` of the site whose structure morphisms `Vₖ ⟶ S` are jointly surjective (for instance
an étale covering of `S`), and the restriction `F|_{Vₖ}` is finite locally constant on `Vₖ` for
every `k`, then `F` is finite locally constant.

The proof is the composition of coverings: each `F|_{Vₖ}` is constant with finite value on the
members `Vₖᵢ` of a covering of `Vₖ`, the composites `Vₖᵢ ⟶ Vₖ ⟶ S` cover `S`, and the restriction
of `F|_{Vₖ}` to `Vₖᵢ` is the restriction of `F` to `Vₖᵢ`. The general form, for a site with a
final object and pullbacks, and an arbitrary concrete coefficient category, is
`CategoryTheory.Sheaf.isFiniteLocallyConstant_of_isFiniteLocallyConstant_over`.

## Main results

* `CategoryTheory.Sheaf.isFiniteLocallyConstant_of_isFiniteLocallyConstant_over`: on a site with
  a final object `T`, a sheaf whose restrictions to the members of one covering family of `T` are
  finite locally constant is finite locally constant.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_of_forall_over`: the same on the small
  étale site, for a jointly surjective family of objects.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_of_isEtaleCovering_of_forall_over`: the
  same for an étale covering `(Vₖ ⟶ S)` in the sense of
  `AlgebraicGeometry.Scheme.IsEtaleCovering`.

## Implementation notes

The restriction `F|_{Vₖ}` is Mathlib's restriction to the localized site,
`CategoryTheory.Sheaf.over`, and "finite locally constant on `Vₖ`" is
`Stacks.ConstantSheaf.IsFiniteLocallyConstant` on that localized site. A trivialization of
`(F|_{Vₖ})|_{W}`, for `W` an object over `Vₖ`, is turned into one of `F|_{W}` along the
equivalence of the slice of a slice with a slice, by
`Stacks.ConstantSheaf.constantTrivializationFromIteratedSlice`.

The covering families of the source are finite; the statement for a jointly surjective family
of arbitrary size contains that case.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' u' v u

attribute [local instance] Stacks.ConstantSheaf.hasWeakSheafify_over_over
  Stacks.ConstantSheaf.iteratedSliceBackward_sheafPushforward_isEquivalence

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  [∀ U : C, HasWeakSheafify (J.over U) D]

/-- **Finite local constancy is local.** On a site with pullbacks and a final object `T`, if the
restriction of a sheaf `F` to each member `X i` of a covering family of `T` is finite locally
constant on `C/X i`, then `F` is finite locally constant. -/
theorem isFiniteLocallyConstant_of_isFiniteLocallyConstant_over [HasPullbacks C] {T : C}
    (hT : IsTerminal T)
    (F : Sheaf J D) {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hf : Sieve.ofArrows X f ∈ J T)
    (hF : ∀ i, Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
      (J.over (X i)) (F.over (X i))) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD) J F := by
  classical
  choose I' V g hg hV using fun i => (hF i).exists_finite_cover (Over.mk (𝟙 (X i)))
  let V' (i : Σ j, I' j) : C := (V i.1 i.2).left
  let g' (i : Σ j, I' j) : V' i ⟶ T := (g i.1 i.2).left ≫ f i.1
  refine Stacks.ConstantSheaf.Localization.isFiniteLocallyConstant_of_finite_cover J D hT F
    (X := V') (f := g') ?_ ?_
  · apply J.transitive hf
    intro Y a ha
    obtain ⟨Z, b, c, ⟨i⟩, rfl⟩ := ha
    rw [Sieve.pullback_comp]
    apply J.pullback_stable
    apply J.superset_covering (S := Sieve.ofArrows (fun j => (V i j).left)
      (fun j => (g i j).left))
    · intro Z a ha
      obtain ⟨W, b, c, ⟨j⟩, rfl⟩ := ha
      change (Sieve.ofArrows V' g') ((b ≫ (g i j).left) ≫ f i)
      rw [Category.assoc]
      exact (Sieve.ofArrows V' g').downward_closed
        (Sieve.le_generate _ _ _ ⟨⟨i, j⟩⟩) b
    · simpa only [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] using hg i
  · rintro ⟨i, j⟩
    obtain ⟨E, hE, ⟨e⟩⟩ := hV i j
    exact ⟨E, hE, ⟨Stacks.ConstantSheaf.constantTrivializationFromIteratedSlice J (X i)
      (V i j) F E e⟩⟩

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  [∀ U : SmallEtale B S hS, HasWeakSheafify ((topology B S hS).over U) D]

/-- **Finite local constancy is étale local.** Let `(Vₖ)` be objects of the small étale site of
`S` whose structure morphisms `Vₖ ⟶ S` are jointly surjective, and `F` a sheaf on the site such
that every restriction `F|_{Vₖ}` is finite locally constant on `Vₖ`. Then `F` is finite locally
constant. -/
@[weil "lem_fk104_flc_etale_local"]
theorem isFiniteLocallyConstant_of_forall_over {K : Type*} (V : K → SmallEtale B S hS)
    (hV : ∀ x : S, ∃ k, x ∈ Set.range (B.inclusion.map (V k).obj.hom))
    (F : Sheaf (topology B S hS) D)
    (hF : ∀ k, Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
      ((topology B S hS).over (V k)) (F.over (V k))) :
    IsFiniteLocallyConstant B S hS (FD := FD) (CD := CD) F := by
  refine Sheaf.isFiniteLocallyConstant_of_isFiniteLocallyConstant_over
    (finalIsTerminal B S hS) F (f := fun k => (finalIsTerminal B S hS).from (V k)) ?_ hF
  refine mem_topology_of_jointlySurjective fun x => ?_
  obtain ⟨k, hk⟩ := hV x
  exact ⟨V k, _, Sieve.ofArrows_mk _ _ k, by rwa [toScheme_map_from_final]⟩

/-- **Finite local constancy is étale local**, for an étale covering `(Vₖ ⟶ S)_{k ∈ K}` of `S`
by objects of the small étale site: if every restriction `F|_{Vₖ}` is finite locally constant on
`Vₖ`, then `F` is finite locally constant. -/
@[weil "lem_fk104_flc_etale_local"]
theorem isFiniteLocallyConstant_of_isEtaleCovering_of_forall_over {K : Type*}
    (V : K → SmallEtale B S hS)
    (hV : Scheme.IsEtaleCovering (U := S) (fun k => B.inclusion.map (V k).obj.hom))
    (F : Sheaf (topology B S hS) D)
    (hF : ∀ k, Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
      ((topology B S hS).over (V k)) (F.over (V k))) :
    IsFiniteLocallyConstant B S hS (FD := FD) (CD := CD) F :=
  isFiniteLocallyConstant_of_forall_over V hV.exists_mem_range F hF

end AlgebraicGeometry.SmallEtale
