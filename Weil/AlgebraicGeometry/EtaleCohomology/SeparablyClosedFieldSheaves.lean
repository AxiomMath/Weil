module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.CategoryTheory.Sites.GlobalSections
public import Weil.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.Attr

/-!
# Higher direct images to the spectrum of a separably closed field

Let `k` be a separably closed field, `f : X ⟶ Spec k` a morphism and `F` an abelian sheaf on the
small étale site of `X`. Then the global sections of the higher direct image are the étale
cohomology of `X`:
`(R^i f_* F)(Spec k) ≅ H^i(X, F)` for all `i ≥ 0`, naturally in `F`.

Over a separably closed field every étale scheme is covered by rational points, so the global
sections functor `Γ(Spec k, -)` is an equivalence from abelian étale sheaves on `Spec k` to
abelian groups; in particular it is exact, and an exact functor commutes with right derived
functors: `Γ(Spec k, R^i f_* F) ≅ R^i(Γ(Spec k, -) ∘ f_*)(F)`. Finally
`Γ(Spec k, f_* G) = G(X ×_k Spec k) ≅ Γ(X, G)`, naturally in `G`, and the right derived functors
of `Γ(X, -)` are the étale cohomology groups.

## Main results

* `AlgebraicGeometry.SmallEtale.isEquivalence_globalSections_of_isSepClosed`: over a separably
  closed field, global sections on the small étale site of `Spec k` is an equivalence.
* `AlgebraicGeometry.BigEtaleSite.smallPushforwardCompGlobalSectionsIso`: `Γ(Y, f_* G) ≅ Γ(X, G)`.
* `AlgebraicGeometry.BigEtaleSite.higherDirectImageCompGlobalSectionsIso`:
  `Γ(Spec k, R^i f_* -) ≅ H^i(X, -)`, as functors.
* `AlgebraicGeometry.BigEtaleSite.higherDirectImageGlobalSectionsAddEquiv`: the same on one sheaf.

## Implementation notes

The source works on the site `Et(X)` of noetherian separated étale `X`-schemes; here, following
the conventions of this library, the sites are the size-bounded small étale sites
`AlgebraicGeometry.SmallEtale` of a big étale site, with coefficients in `AddCommGrpCat.{u}`.
That `Γ(Spec k, -)` is an equivalence is deduced from the corresponding statement on Mathlib's
small étale site, `Stacks.EtaleCohomology.isEquivalence_sheafSections_final_of_isSepClosed`,
through the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` of the sheaf categories, whose
inverse is restriction.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.2
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

namespace SmallEtale

variable (k : Type u) [Field k] [IsSepClosed k] (hk : B.Contains (Spec (.of k)))

/-- **Over a separably closed field, global sections is an equivalence** from abelian sheaves on
the small étale site of `Spec k` to abelian groups. -/
theorem isEquivalence_globalSections_of_isSepClosed :
    (globalSections.{u} B (Spec (.of k)) hk).IsEquivalence := by
  let E := sheafEquiv B (Spec (.of k)) hk AddCommGrpCat.{u}
  let T := (toEtaleSite B (Spec (.of k)) hk).obj (final B _ hk)
  have : IsIso T.hom := by
    change IsIso (𝟙 _)
    infer_instance
  have hT : IsTerminal T := Stacks.EtaleCohomology.isTerminalOfIsIsoHom T
  have : IsIso (Scheme.Etale.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of k))))
  let e : T ≅ Scheme.Etale.mk (𝟙 (Spec (.of k))) :=
    hT.uniqueUpToIso (Stacks.EtaleCohomology.isTerminalOfIsIsoHom _)
  have := Stacks.EtaleCohomology.isEquivalence_sheafSections_final_of_isSepClosed k
    AddCommGrpCat.{u}
  -- `E.inverse` is restriction along `toEtaleSite`, so `E.inverse ⋙ Γ` is evaluation at `T`.
  have : (E.inverse ⋙ globalSections.{u} B (Spec (.of k)) hk).IsEquivalence :=
    Functor.isEquivalence_of_iso
      ((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u}).mapIso e.op)
  exact Functor.isEquivalence_of_iso
    ((Functor.isoWhiskerRight E.unitIso.symm _ ≪≫ Functor.leftUnitor _).symm ≪≫
      Functor.associator _ _ _).symm

/-- Over a separably closed field, global sections of abelian étale sheaves on `Spec k` is
exact. -/
instance preservesFiniteColimits_globalSections_of_isSepClosed :
    PreservesFiniteColimits (globalSections.{u} B (Spec (.of k)) hk) := by
  have := isEquivalence_globalSections_of_isSepClosed B k hk
  infer_instance

end SmallEtale

namespace BigEtaleSite

/-- Global sections of a direct image are global sections: `Γ(Y, f_* G) = G(X ×_Y Y) ≅ Γ(X, G)`,
naturally in the abelian sheaf `G`, the base change of the final object being final. -/
def smallPushforwardCompGlobalSectionsIso {X Y : B.Scheme} (f : X ⟶ Y) :
    B.smallPushforward f AddCommGrpCat.{u} ⋙ SmallEtale.globalSections B Y.obj Y.property ≅
      SmallEtale.globalSections.{u} B X.obj X.property :=
  (sheafSections _ AddCommGrpCat.{u}).mapIso
    ((smallEtaleBaseChange_finalIsTerminal B f).uniqueUpToIso
      (SmallEtale.finalIsTerminal B X.obj X.property)).symm.op

variable (k : Type u) [Field k] [IsSepClosed k] (hk : B.Contains (Spec (.of k)))
  {X : B.Scheme} (f : X ⟶ B.obj (Spec (.of k)) hk)

/-- **Higher direct images to the spectrum of a separably closed field.** For a morphism
`f : X ⟶ Spec k` with `k` separably closed, the global sections of the higher direct image
`R^i f_* F` are the étale cohomology `H^i(X, F)`, naturally in the abelian sheaf `F`. -/
@[weil "lem_fk102_direct_image_to_separably_closed_point"]
def higherDirectImageCompGlobalSectionsIso (i : ℕ) :
    letI := SmallEtale.hasExt_sheaf B X.obj X.property
    higherDirectImage.{u} B f i ⋙ SmallEtale.globalSections B (Spec (.of k)) hk ≅
      Sheaf.functorH (SmallEtale.topology B X.obj X.property) i :=
  letI := SmallEtale.hasExt_sheaf B X.obj X.property
  (Functor.rightDerivedCompIso _ _ i).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (smallPushforwardCompGlobalSectionsIso B f) i ≪≫
    (SmallEtale.functorHIsoRightDerivedSections B X.obj X.property i).symm

/-- For a morphism `f : X ⟶ Spec k` with `k` separably closed and an abelian sheaf `F` on the
small étale site of `X`, `(R^i f_* F)(Spec k) ≃+ H^i(X, F)`. -/
def higherDirectImageGlobalSectionsAddEquiv (i : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u}) :
    letI := SmallEtale.hasExt_sheaf B X.obj X.property
    ((higherDirectImage.{u} B f i).obj F).obj.obj (op (SmallEtale.final B _ hk)) ≃+ F.H i :=
  letI := SmallEtale.hasExt_sheaf B X.obj X.property
  ((higherDirectImageCompGlobalSectionsIso B k hk f i).app F).addCommGroupIsoToAddEquiv

end BigEtaleSite

end AlgebraicGeometry
