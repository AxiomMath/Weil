module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import Weil.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import Weil.Attr

/-!
# Extension by zero commutes with direct limits

Let `f : U ⟶ X` be an étale morphism of schemes and let `(F_i)_{i ∈ I}` be a direct system of
abelian sheaves on the small étale site of `U`. Then the canonical morphism
`colim_i f_! F_i ⟶ f_! (colim_i F_i)` is an isomorphism. The reason is formal: extension by zero
`f_!` is left adjoint to restriction, and a left adjoint preserves all colimits. The statement
here is proved for every diagram shape for which the colimit exists, which contains the case of
a directed index set.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_colimit_post_abelianExtensionByZero`: on the small étale
  site of Stacks Tag 021B, for an object `U` of the small étale site of `X`, the canonical
  morphism `colim_i f_! F_i ⟶ f_! (colim_i F_i)` is an isomorphism.
* `AlgebraicGeometry.isIso_colimit_post_extensionByZero`: the same on Mathlib's small étale
  site, for an arbitrary étale morphism `f : X ⟶ Y`.

## Implementation notes

[FK] deduce the statement from the stalk formula for `f_!`; here it follows from the adjunction
`f_! ⊣ (-)|_U`, as in the Stacks Project (Tag 03S5's proof of right exactness). The direct limits
of the statement exist because the categories of abelian sheaves involved are cocomplete; the
statement takes the existence of the colimit as an instance argument, so that it applies to every
indexing category.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w' w v u

namespace AlgebraicGeometry

/-- **Extension by zero commutes with direct limits**, on the small étale site of Stacks
Tag 021B: for an object `U` of the small étale site of `X`, with structure morphism `f : U ⟶ X`,
and a diagram `i ↦ F_i` of abelian sheaves on `U` (for instance a direct system indexed by a
directed set), the canonical morphism `colim_i f_! F_i ⟶ f_! (colim_i F_i)` is an
isomorphism. -/
@[weil "lem_fk108_extension_by_zero_commutes_direct_limits"]
theorem SmallEtale.isIso_colimit_post_abelianExtensionByZero (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX) {J : Type w} [Category.{w'} J]
    (F : J ⥤ Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1})
    [HasColimit F] [HasColimit (F ⋙ abelianExtensionByZero B X hX U)] :
    IsIso (colimit.post F (abelianExtensionByZero B X hX U)) := by
  have : PreservesColimitsOfSize.{w', w} (abelianExtensionByZero B X hX U) :=
    (abelianExtensionByZeroAdjunction B X hX U).leftAdjoint_preservesColimits
  infer_instance

/-- **Extension by zero commutes with direct limits**, on Mathlib's small étale site: for an
étale morphism `f : X ⟶ Y` and a diagram `i ↦ F_i` of abelian sheaves on `X` (for instance a
direct system indexed by a directed set), the canonical morphism
`colim_i f_! F_i ⟶ f_! (colim_i F_i)` is an isomorphism. -/
@[weil "lem_fk108_extension_by_zero_commutes_direct_limits"]
theorem isIso_colimit_post_extensionByZero {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    {J : Type w} [Category.{w'} J]
    (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [HasColimit F] [HasColimit (F ⋙ Stacks.EtaleCohomology.extensionByZero.{u, v} f)] :
    IsIso (colimit.post F (Stacks.EtaleCohomology.extensionByZero.{u, v} f)) := by
  have : PreservesColimitsOfSize.{w', w} (Stacks.EtaleCohomology.extensionByZero.{u, v} f) :=
    (Stacks.EtaleCohomology.extensionByZeroAdj.{u, v} f).leftAdjoint_preservesColimits
  infer_instance

end AlgebraicGeometry

end
