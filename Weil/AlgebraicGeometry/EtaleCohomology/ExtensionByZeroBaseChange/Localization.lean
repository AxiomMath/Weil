module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import Weil.Attr

/-!
# Restriction to an étale object preserves open difference loci

Let `F` be a presheaf of sets on the small étale site of a scheme `X`, let `T` be an object of
that site and let `j : Et(T) ⥤ Et(X)` be composition with the structure morphism `T ⟶ X`. The
restriction `F|_T` of `F` to `T` is the presheaf `V ↦ F(j V)` on the small étale site of `T`.
For `V ∈ Et(T)` and `α β ∈ F|_T(V) = F(j V)`, the coincidence set of `α` and `β` formed in `F|_T`
equals the one formed in `F`, with `V` regarded as the object `j V` of `Et(X)`. In particular,
if `F` has open difference loci, so has `F|_T`.

The two germs of a section at a geometric point `v̄` of `V` live in different stalks, the
stalk of `F|_T` at the image of `v̄` in `T` and the stalk of `F` at its image in `X`. Their
equality is compared directly through the description of equality in a stalk: two sections
have the same germ if and only if they agree on some étale neighbourhood refining `(V, v̄)`.
An étale neighbourhood of `T` refining `V` is one of `X` through `j`, and conversely an étale
`X`-scheme `W` with a map to `V` is étale over `T` through that map.

## Main results

* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_smallEtalePostcompose`: the coincidence set
  in `F|_T` equals the one in `F`.
* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.smallEtalePostcompose`: `F|_T` has open
  difference loci when `F` has.

## Implementation notes

Restriction is `(AlgebraicGeometry.smallEtalePostcompose B X hX T).op ⋙ F`, the site-level
restriction of Stacks 03S3 on the small étale site `AlgebraicGeometry.SmallEtale`, where
coincidence sets and open difference loci are defined. The statements are for presheaves,
which contains the case of a sheaf through its underlying presheaf.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The germs of two sections of `F|_T` at a geometric point `v̄` of `V ∈ Et(T)` agree if and
only if the germs of the same sections of `F` at `v̄`, for `V` regarded as an object of
`Et(X)`, agree. -/
lemma germ_smallEtalePostcompose_eq_iff (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    (T : SmallEtale B X hX) {V : SmallEtale B T.obj.left.1 T.obj.left.property}
    (α β : F.obj (op ((smallEtalePostcompose B X hX T).obj V)))
    (v : GeometricPoint ((SmallEtale.toScheme B _ _).obj V)) :
    germ ((smallEtalePostcompose B X hX T).op ⋙ F) α v =
        germ ((smallEtalePostcompose B X hX T).op ⋙ F) β v ↔
      germ F (U := (smallEtalePostcompose B X hX T).obj V) α v =
        germ F (U := (smallEtalePostcompose B X hX T).obj V) β v := by
  refine (GrothendieckTopology.Point.toPresheafFiber_eq_iff' _ _ _ _ _).trans
    (Iff.trans ?_ (GrothendieckTopology.Point.toPresheafFiber_eq_iff' _ _ _ _ _).symm)
  constructor
  · rintro ⟨Y, f, y, hy, h⟩
    refine ⟨(smallEtalePostcompose B X hX T).obj Y, (smallEtalePostcompose B X hX T).map f,
      ⟨y.1, ?_⟩, ?_, h⟩
    · have h2 := y.2
      change y.1 ≫ B.inclusion.map (Y.obj.hom ≫ T.obj.hom) =
        v.hom ≫ B.inclusion.map (V.obj.hom ≫ T.obj.hom)
      change y.1 ≫ B.inclusion.map Y.obj.hom = v.hom ≫ B.inclusion.map V.obj.hom at h2
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, h2, Category.assoc]
    · have h1 : y.1 ≫ B.inclusion.map f.hom.left = v.hom := congrArg Subtype.val hy
      exact Subtype.ext h1
  · rintro ⟨Y, f, y, hy, h⟩
    let a : Y.obj.left ⟶ V.obj.left := f.hom.left
    have hw : a ≫ (V.obj.hom ≫ T.obj.hom) = Y.obj.hom := Over.w f.hom
    have hY : Etale (B.inclusion.map (a ≫ V.obj.hom)) :=
      B.etale_map_comp _ _
        (B.etale_map_of_postcomp a (V.obj.hom ≫ T.obj.hom) Y.obj.hom Y.property
          (B.etale_map_comp _ _ V.property T.property) hw) V.property
    let Y' : SmallEtale B T.obj.left.1 T.obj.left.property := ⟨Over.mk (a ≫ V.obj.hom), hY⟩
    let f' : Y' ⟶ V := ObjectProperty.homMk (Over.homMk a rfl)
    let e : (smallEtalePostcompose B X hX T).obj Y' ≅ Y :=
      (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
        (Over.isoMk (Iso.refl _) (by
          change 𝟙 _ ≫ Y.obj.hom = (a ≫ V.obj.hom) ≫ T.obj.hom
          rw [Category.id_comp, Category.assoc]
          exact hw.symm))
    have hf : (smallEtalePostcompose B X hX T).map f' = e.hom ≫ f := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change a = 𝟙 _ ≫ a
      rw [Category.id_comp]
    have hya : y.1 ≫ B.inclusion.map a = v.hom := congrArg Subtype.val hy
    refine ⟨Y', f', ⟨y.1, ?_⟩, ?_, ?_⟩
    · change y.1 ≫ B.inclusion.map (a ≫ V.obj.hom) = v.hom ≫ B.inclusion.map V.obj.hom
      rw [Functor.map_comp, ← Category.assoc, hya]
    · apply Subtype.ext
      exact hya
    · change F.map ((smallEtalePostcompose B X hX T).map f').op α =
        F.map ((smallEtalePostcompose B X hX T).map f').op β
      rw [hf, op_comp, F.map_comp, types_comp_apply, types_comp_apply, h]

/-- **Restriction and coincidence sets.** For a presheaf of sets `F` on the small étale site of
`X`, an object `T` of that site, `V ∈ Et(T)` and sections `α β ∈ F|_T(V) = F(V)`, the
coincidence set of `α` and `β` formed in the restriction `F|_T` equals the one formed in `F`,
with `V` regarded as an object of `Et(X)`. -/
@[weil "lem_fk103_restriction_open_difference_loci"]
theorem germCoincidenceSet_smallEtalePostcompose (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    (T : SmallEtale B X hX) {V : SmallEtale B T.obj.left.1 T.obj.left.property}
    (α β : F.obj (op ((smallEtalePostcompose B X hX T).obj V))) :
    germCoincidenceSet ((smallEtalePostcompose B X hX T).op ⋙ F) (U := V) α β =
      germCoincidenceSet F (U := (smallEtalePostcompose B X hX T).obj V) α β := by
  ext x
  exact forall₂_congr fun v _ ↦ germ_smallEtalePostcompose_eq_iff F T α β v

/-- **Restriction preserves open difference loci.** If a presheaf of sets `F` on the small
étale site of `X` has open difference loci, so has its restriction `F|_T` to any object `T`
of that site. -/
@[weil "lem_fk103_restriction_open_difference_loci"]
theorem HasOpenDifferenceLoci.smallEtalePostcompose {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (hF : HasOpenDifferenceLoci F) (T : SmallEtale B X hX) :
    HasOpenDifferenceLoci ((AlgebraicGeometry.smallEtalePostcompose B X hX T).op ⋙ F) := by
  intro V α β
  rw [germCoincidenceSet_smallEtalePostcompose]
  exact hF _ α β

end AlgebraicGeometry.SmallEtale

end
