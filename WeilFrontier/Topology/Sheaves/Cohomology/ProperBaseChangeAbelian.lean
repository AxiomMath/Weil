module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.HigherDirectImageStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperFiberStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FlasqueSoft
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueAbelianSheavesAreAcyclic

/-!
# Proper base change at a point for abelian sheaves, and the degenerate Leray isomorphism

Let `f : X ⟶ Y` be a continuous map of topological spaces which is closed and separated and
whose fibres are quasi-compact (for instance a proper map, `IsProperMap`, out of a Hausdorff
space), and let `F` be an abelian sheaf on `X`. Write `X_y = f⁻¹(y)` for the fibre over `y`, with
the subspace topology, and `F|_{X_y}` for the inverse image of `F` along the inclusion.

* **Proper base change at a point** [Stacks, Tag 09V5]: for every `q` and every `y : Y` the stalk
  of the higher direct image is the cohomology of the fibre,
  `(R^q f_* F)_y ≅ H^q(X_y, F|_{X_y})`.
* **Degenerate Leray** [Stacks, Tag 01F4 (1)]: if the higher direct images of `F` vanish, then
  `H^n(X, F) ≅ H^n(Y, f_* F)` for every `n`. By the previous point this holds as soon as
  `H^q(X_y, F|_{X_y}) = 0` for every `y` and every `q > 0`.
* **Discrete fibres.** On a discrete space every abelian sheaf is flasque, so its higher
  cohomology vanishes, and its global sections are the product of its stalks. Hence for a proper
  separated map with discrete (for instance finite) fibres, `H^n(X, F) ≅ H^n(Y, f_* F)` for every
  abelian sheaf `F`, and `(f_* F)_y ≅ ∏_{x ∈ X_y} (F|_{X_y})_x`.

Cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ`, with the
`HasExt` structure supplied by the caller; higher direct images are the right derived functors
`(pushforwardSheafFunctor f).rightDerived q` of the direct image of abelian sheaves.

## Main definitions

* `TopologicalSpace.ProperBaseChange.fiber`: the fibre `f⁻¹(y)`.
* `TopologicalSpace.ProperBaseChange.stalkToFiberSections`: the comparison
  `(f_* F)_y ⟶ Γ(X_y, F|_{X_y})`, natural in `F`.
* `TopologicalSpace.ProperBaseChange.higherDirectImageStalkIso`: proper base change at a point,
  in right derived global sections.
* `TopologicalSpace.ProperBaseChange.higherDirectImageStalkIsoSheafH`: the same with `Sheaf.H`.
* `TopologicalSpace.ProperBaseChange.sheafHIsoOfIsZeroHigherDirectImage`: degenerate Leray.
* `TopologicalSpace.ProperBaseChange.sheafHAddEquivPushforward`: degenerate Leray for a proper
  separated map under vanishing of the higher cohomology of the fibres.
* `TopologicalSpace.ProperBaseChange.sheafHAddEquivPushforwardOfDiscreteFibers` and
  `TopologicalSpace.ProperBaseChange.sheafHAddEquivPushforwardOfFiniteFibers`: the same with no
  hypothesis on `F`, for discrete, respectively finite, fibres.
* `TopologicalSpace.ProperBaseChange.sheafHZeroAddEquivPiStalk`: `H^0` of an abelian sheaf on a
  discrete space is the product of its stalks.
* `TopologicalSpace.ProperBaseChange.pushforwardStalkAddEquivPiStalk`: the stalk of `f_* F` at
  `y` is the product of the stalks of `F|_{X_y}`, for a discrete fibre.

## Main results

* `TopologicalSpace.ProperBaseChange.isIso_stalkToFiberSections`: the degree-zero comparison is
  an isomorphism.
* `TopologicalSpace.ProperBaseChange.isZero_rightDerived_pushforward_of_isZero_fiber`: the
  higher direct image vanishes when the cohomology of every fibre does.
* `TopologicalSpace.ProperBaseChange.isFlasque_of_discreteTopology`: abelian sheaves on a
  discrete space are flasque.
* `TopologicalSpace.ProperBaseChange.subsingleton_sheafH_of_discreteTopology`: their higher
  cohomology vanishes.

## Implementation notes

Proper base change at a point is assembled as [Stacks, Tag 0A3E] is for spectral maps
(`Stacks.Topology.higherDirectImageStalkIso`): the stalk functor is exact, so it commutes with
the right derived functors of `f_*`; the degree-zero comparison is the isomorphism
`Stacks.Topology.isIso_fiberStalkSectionsMap`; and restriction to the fibre is exact and carries
injective sheaves (which are flasque) to sheaves acyclic for global sections on the fibre
(`Stacks.Topology.rightAcyclic_sections_pullback_of_isFlasque`), so that the right derived
functors of `Γ(X_y, -) ∘ (-)|_{X_y}` are those of `Γ(X_y, -)` applied to `F|_{X_y}`.
Degenerate Leray is the same composite-functor argument for `Γ(X, -) = Γ(Y, -) ∘ f_*`, the
direct image preserving injectives because it is right adjoint to the exact inverse image.

[Stacks, Tag 09V5] is in the library only for sheaves of modules on ringed spaces with a
conclusion in the derived category of modules over the local ring
(`Stacks.Cohomology.ProperBaseChange.isIso_properBaseChangeMap`); the abelian statement here is
proved directly from its abelian ingredients rather than by specialising to the constant ring
`ℤ`.

## References

* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 0A3E](https://stacks.math.columbia.edu/tag/0A3E)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.ProperBaseChange

open Stacks.Topology

/-! ### The degree-zero comparison -/

section DegreeZero

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)

/-- The fibre `f⁻¹(y)` of `f` over `y`. -/
abbrev fiber : Set X := (f.hom : X → Y) ⁻¹' ({y} : Set Y)

/-- Restriction of abelian sheaves on `X` to the fibre over `y`, followed by global sections. -/
abbrev fiberSectionsFunctor :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  restrictionFunctor X (fiber f y) ⋙ sectionsFunctor (TopCat.of (fiber f y))

/-- The comparison `(f_* F)_y ⟶ Γ(f⁻¹(y), F|_{f⁻¹(y)})`, natural in the abelian sheaf `F`: the
germ at `y` of a section of `F` over `f⁻¹(V)` goes to the section it induces on the fibre. -/
def stalkToFiberSections :
    pushforwardSheafFunctor f ⋙ sheafStalkFunctor y ⟶ fiberSectionsFunctor f y where
  app F := fiberStalkSectionsMap f y F
  naturality F G β := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun V hy ↦
      ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    refine (ConcreteCategory.comp_apply _ _ s).trans ?_
    refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ s).symm
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
    refine ((congrArg (fiberStalkSectionsMap f y G)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
        ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          ((pushforwardSheafFunctor f).map β)) s)).trans
      (fiberStalkSectionsMap_germ f y G V hy _)).trans ?_
    exact ((ambientSection_naturality_apply
        (Stacks.subsetInclusion X (fiber f y)) β _ s).symm).trans
      (congrArg ((fiberSectionsFunctor f y).map β)
        (fiberStalkSectionsMap_germ f y F V hy s)).symm

variable {f} in
/-- **The degree-zero comparison is an isomorphism** for a closed separated map with
quasi-compact fibre over `y`. -/
theorem isIso_stalkToFiberSections (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : IsCompact (fiber f y)) (hsep : IsSeparatedMap (f.hom : X → Y)) :
    IsIso (stalkToFiberSections f y) := by
  have : ∀ F, IsIso ((stalkToFiberSections f y).app F) := fun F ↦
    isIso_fiberStalkSectionsMap f y hclosed hcompact hsep F
  exact NatIso.isIso_of_isIso_app _

variable {f} in
/-- The degree-zero comparison as an isomorphism of functors. -/
def stalkIsoFiberSections (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : IsCompact (fiber f y)) (hsep : IsSeparatedMap (f.hom : X → Y)) :
    pushforwardSheafFunctor f ⋙ sheafStalkFunctor y ≅ fiberSectionsFunctor f y :=
  have := isIso_stalkToFiberSections y hclosed hcompact hsep
  asIso (stalkToFiberSections f y)

end DegreeZero

/-! ### Cohomology as right derived global sections -/

/-- The cohomology `Sheaf.H G n` of an abelian sheaf on a topological space is the `n`-th right
derived functor of global sections applied to `G`. -/
def sheafHIsoRightDerivedSections (Z : TopCat.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u} G n) ≅ ((sectionsFunctor Z).rightDerived n).obj G :=
  (Stacks.Cohomology.TerminalCohomology.h'IsoH (Opens.grothendieckTopology Z) G n ⊤
      Stacks.Cohomology.TerminalCohomology.topIsTerminal).symm ≪≫
    Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections _ G n ⊤

/-! ### Proper base change at a point, and degenerate Leray -/

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The direct image of abelian sheaves is left exact, being a right adjoint. -/
instance preservesFiniteLimits_pushforwardSheafFunctor :
    PreservesFiniteLimits (pushforwardSheafFunctor f) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    f).rightAdjoint_preservesLimits.preservesFiniteLimits.{u, u}

variable {f} in
/-- The restriction of an injective abelian sheaf to a quasi-compact fibre of a separated map is
acyclic for global sections on the fibre. -/
theorem rightAcyclic_sections_restriction_of_injective (y : Y)
    (hcompact : IsCompact (fiber f y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I] :
    (sectionsFunctor (TopCat.of (fiber f y))).rightAcyclic
      ((restrictionFunctor X (fiber f y)).obj I) := by
  have hinj : Injective (C := TopCat.Sheaf AddCommGrpCat.{u} X) I := ‹Injective I›
  have : TopCat.Sheaf.IsFlasque (C := AddCommGrpCat.{u}) (X := X) I := isFlasque_of_injective I
  exact rightAcyclic_sections_pullback_of_isFlasque I hcompact
    (fiberPairwiseSeparated_of_isSeparatedMap f y hsep)

variable {f} in
/-- **Proper base change at a point** [Stacks, Tag 09V5], for abelian sheaves. Let `f` be a
closed separated continuous map whose fibre over `y` is quasi-compact. Then for every `q` the
stalk at `y` of `R^q f_* F` is the `q`-th cohomology of the restriction of `F` to the fibre:
`(R^q f_* F)_y ≅ H^q(f⁻¹(y), F|_{f⁻¹(y)})`, cohomology being right derived global sections. -/
def higherDirectImageStalkIso (y : Y) (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : IsCompact (fiber f y)) (hsep : IsSeparatedMap (f.hom : X → Y)) (q : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((pushforwardSheafFunctor f).rightDerived q ⋙ sheafStalkFunctor y).obj F ≅
      ((sectionsFunctor (TopCat.of (fiber f y))).rightDerived q).obj
        ((restrictionFunctor X (fiber f y)).obj F) :=
  (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPostcomposeIso
      (F := pushforwardSheafFunctor f) (sheafStalkFunctor y) q).app F ≪≫
    (Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
      (stalkIsoFiberSections y hclosed hcompact hsep) q).app F ≪≫
    Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso
      (restrictionFunctor X (fiber f y))
      (sectionsFunctor (TopCat.of (fiber f y)))
      (fun I _ ↦ rightAcyclic_sections_restriction_of_injective y hcompact hsep I) F
      (Functor.isIso_rightDerivedFunctorPlusUnit_app_of_exact _ _) q

variable {f} in
/-- **The higher direct image vanishes when the cohomology of every fibre does.** Its stalks
are the cohomology of the fibres, by proper base change at a point, and an abelian sheaf whose
stalks vanish is zero. -/
theorem isZero_rightDerived_pushforward_of_isZero_fiber
    (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : ∀ y, IsCompact (fiber f y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ)
    (hF : ∀ y, IsZero (((sectionsFunctor (TopCat.of (fiber f y))).rightDerived q).obj
      ((restrictionFunctor X (fiber f y)).obj F))) :
    IsZero (((pushforwardSheafFunctor f).rightDerived q).obj F) :=
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (F := (((pushforwardSheafFunctor f).rightDerived q).obj F :
      TopCat.Sheaf AddCommGrpCat.{u} Y))).2
    fun y ↦ (hF y).of_iso (higherDirectImageStalkIso y hclosed (hcompact y) hsep q F)

/-- The direct image of an injective abelian sheaf is acyclic for global sections: it is
injective, the direct image being right adjoint to the exact inverse image. -/
theorem rightAcyclic_sections_pushforward_of_injective
    (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I] :
    (sectionsFunctor Y).rightAcyclic ((pushforwardSheafFunctor f).obj I) := by
  have hI : Injective ((pushforwardSheafFunctor f).obj I) :=
    Adjunction.map_injective (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f) I
      ‹_›
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa using Functor.isZero_rightDerived_obj_injective_succ (sectionsFunctor Y) q _

/-- Global sections on `X` are the direct image followed by global sections on `Y`. -/
def pushforwardCompSectionsIso :
    pushforwardSheafFunctor f ⋙ sectionsFunctor Y ≅ sectionsFunctor X :=
  Iso.refl _

/-- **Degenerate Leray**, in right derived global sections: if `R^q f_* F = 0` for every
`q > 0`, then `R^nΓ(X, F) ≅ R^nΓ(Y, f_* F)` for every `n`. -/
def rightDerivedSectionsIsoOfIsZero
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ q : ℕ, 0 < q → IsZero (((pushforwardSheafFunctor f).rightDerived q).obj F))
    (n : ℕ) :
    ((sectionsFunctor X).rightDerived n).obj F ≅
      ((sectionsFunctor Y).rightDerived n).obj ((pushforwardSheafFunctor f).obj F) :=
  ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso (pushforwardCompSectionsIso f) n).app
      F).symm ≪≫
    Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso
      (pushforwardSheafFunctor f) (sectionsFunctor Y)
      (fun I _ ↦ rightAcyclic_sections_pushforward_of_injective f I) F
      ((Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ F).2 hF) n

end Derived

section SheafH

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **Degenerate Leray** [Stacks, Tag 01F4 (1)], for abelian sheaves on topological spaces: if
the higher direct images `R^q f_* F`, `q > 0`, vanish, then `H^n(X, F) ≅ H^n(Y, f_* F)` for
every `n`. -/
def sheafHIsoOfIsZeroHigherDirectImage
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ q : ℕ, 0 < q → IsZero (((pushforwardSheafFunctor f).rightDerived q).obj F))
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u} F n) ≅
      AddCommGrpCat.of (Sheaf.H.{u} ((pushforwardSheafFunctor f).obj F) n) :=
  sheafHIsoRightDerivedSections X F n ≪≫ rightDerivedSectionsIsoOfIsZero f F hF n ≪≫
    (sheafHIsoRightDerivedSections Y _ n).symm

variable {f} in
/-- **Proper base change at a point** [Stacks, Tag 09V5], with `Sheaf.H`: for a proper
separated map `f`, `(R^q f_* F)_y ≅ H^q(f⁻¹(y), F|_{f⁻¹(y)})`. -/
def higherDirectImageStalkIsoSheafH
    (hf : IsProperMap (f.hom : X → Y)) (hsep : IsSeparatedMap (f.hom : X → Y)) (y : Y)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of (fiber f y))) AddCommGrpCat.{u})]
    (q : ℕ) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((pushforwardSheafFunctor f).rightDerived q ⋙ sheafStalkFunctor y).obj F ≅
      AddCommGrpCat.of (Sheaf.H.{u} ((restrictionFunctor X (fiber f y)).obj F) q) :=
  higherDirectImageStalkIso y hf.isClosedMap (hf.isCompact_preimage isCompact_singleton) hsep q
      F ≪≫
    (sheafHIsoRightDerivedSections _ _ q).symm

variable {f} in
/-- **Leray degenerates for a proper map with acyclic fibres.** Let `f` be a proper separated
map and `F` an abelian sheaf on `X` such that `H^q(f⁻¹(y), F|_{f⁻¹(y)}) = 0` for every `y` and
every `q > 0`. Then `H^n(X, F) ≃ H^n(Y, f_* F)` for every `n`. -/
def sheafHAddEquivPushforward
    (hf : IsProperMap (f.hom : X → Y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    [∀ y : Y, HasExt.{u}
      (Sheaf (Opens.grothendieckTopology (TopCat.of (fiber f y))) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ (y : Y) (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u} ((restrictionFunctor X (fiber f y)).obj F) q))
    (n : ℕ) :
    Sheaf.H.{u} F n ≃+ Sheaf.H.{u} ((pushforwardSheafFunctor f).obj F) n :=
  (sheafHIsoOfIsZeroHigherDirectImage f F (fun q hq ↦
    isZero_rightDerived_pushforward_of_isZero_fiber hf.isClosedMap
      (fun _ ↦ hf.isCompact_preimage isCompact_singleton) hsep F q fun y ↦
        haveI := hF y q hq
        (AddCommGrpCat.isZero_of_subsingleton _).of_iso
          (sheafHIsoRightDerivedSections _ _ q).symm) n).addCommGroupIsoToAddEquiv

end SheafH

/-! ### Discrete spaces -/

section Discrete

/-- Sections of an abelian sheaf over the empty open form a trivial group. -/
theorem subsingleton_obj_of_eq_bot {Z : TopCat.{u}} (G : TopCat.Sheaf AddCommGrpCat.{u} Z)
    {W : Opens Z} (h : W = ⊥) : Subsingleton (ToType (G.obj.obj (op W))) :=
  AddCommGrpCat.isZero_iff_subsingleton.1 (G.isTerminalOfEqEmpty h).isZero

/-- **Every abelian sheaf on a discrete space is flasque**: a section over `V ⊆ U` extends by
zero over the open complement `U \ V`. -/
theorem isFlasque_of_discreteTopology {Z : TopCat.{u}} [DiscreteTopology Z]
    (G : TopCat.Sheaf AddCommGrpCat.{u} Z) : G.IsFlasque := by
  refine ⟨fun {A B} i ↦ (AddCommGrpCat.epi_iff_surjective _).2 fun s ↦ ?_⟩
  have hBA : B.unop ≤ A.unop := leOfHom i.unop
  let W : Opens Z := ⟨(A.unop : Set Z) \ B.unop, isOpen_discrete _⟩
  let U : Bool → Opens Z := fun b ↦ cond b B.unop W
  let sf : ∀ b, ToType (G.obj.obj (op (U b))) := fun b ↦ match b with
    | true => s
    | false => 0
  have hUA : ∀ b, U b ≤ A.unop := fun b ↦ match b with
    | true => hBA
    | false => fun x hx ↦ hx.1
  have hdisj : B.unop ⊓ W = ⊥ := by
    ext x; simp [W]
  have hcomp : TopCat.Presheaf.IsCompatible G.obj U sf := by
    intro b b'
    cases b <;> cases b'
    · rfl
    · exact (subsingleton_obj_of_eq_bot G (by rw [inf_comm]; exact hdisj)).elim _ _
    · exact (subsingleton_obj_of_eq_bot G hdisj).elim _ _
    · rfl
  obtain ⟨t, ht, -⟩ := G.existsUnique_gluing' U A.unop (fun b ↦ homOfLE (hUA b))
    (fun x hx ↦ by
      by_cases hxB : x ∈ B.unop
      · exact Opens.mem_iSup.2 ⟨true, hxB⟩
      · exact Opens.mem_iSup.2 ⟨false, ⟨hx, hxB⟩⟩) sf hcomp
  exact ⟨t, ht true⟩

variable {Z : TopCat.{u}} [DiscreteTopology Z] (G : TopCat.Sheaf AddCommGrpCat.{u} Z)

/-- The germs of a global section at all points of `Z`. -/
def sectionsToPiStalk : ToType (G.obj.obj (op ⊤)) →+ ∀ z : Z, ToType (G.presheaf.stalk z) where
  toFun s z := G.presheaf.germ ⊤ z trivial s
  map_zero' := by ext z; simp
  map_add' s t := by ext z; simp

/-- **On a discrete space, a global section is the family of its germs**: the map from global
sections to the product of the stalks is bijective. -/
theorem bijective_sectionsToPiStalk : Function.Bijective (sectionsToPiStalk G) := by
  refine ⟨fun s t hst ↦ TopCat.Presheaf.section_ext G ⊤ s t fun z _ ↦ congrFun hst z,
    fun g ↦ ?_⟩
  choose V hV r hr using fun z ↦ TopCat.Presheaf.exists_germ_eq G.presheaf (g z)
  let U : Z → Opens Z := fun z ↦ ⟨{z}, isOpen_discrete _⟩
  have hUV : ∀ z, U z ≤ V z := fun z x hx ↦ by
    rw [show x = z from hx]; exact hV z
  let sf : ∀ z, ToType (G.obj.obj (op (U z))) := fun z ↦ G.obj.map (homOfLE (hUV z)).op (r z)
  have hcomp : TopCat.Presheaf.IsCompatible G.obj U sf := by
    intro z z'
    by_cases h : z = z'
    · subst h; rfl
    · refine (subsingleton_obj_of_eq_bot G ?_).elim _ _
      ext x
      simp only [U, Opens.coe_inf, Opens.coe_mk, Opens.coe_bot, Set.mem_inter_iff,
        Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl; exact h
  obtain ⟨t, ht, -⟩ := G.existsUnique_gluing' U ⊤ (fun z ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.2 ⟨x, rfl⟩) sf hcomp
  refine ⟨t, funext fun z ↦ ?_⟩
  change G.presheaf.germ ⊤ z trivial t = g z
  have hz : z ∈ U z := Set.mem_singleton z
  rw [← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE le_top : U z ⟶ ⊤) z hz t]
  erw [ht z]
  exact (TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (hUV z)) z hz (r z)).trans (hr z)

/-- **Global sections of an abelian sheaf on a discrete space are the product of its stalks.** -/
def sectionsAddEquivPiStalk : ToType (G.obj.obj (op ⊤)) ≃+ ∀ z : Z, ToType (G.presheaf.stalk z) :=
  AddEquiv.ofBijective _ (bijective_sectionsToPiStalk G)

attribute [local instance] HasDerivedCategory.standard in
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- **The higher right derived global sections of an abelian sheaf on a discrete space
vanish**, the sheaf being flasque. -/
theorem isZero_rightDerived_sections_of_discreteTopology (p : ℕ) (hp : 0 < p) :
    IsZero (((sectionsFunctor Z).rightDerived p).obj G) :=
  Stacks.Cohomology.FlasqueAbelian.isZero_rightDerived_abSections_of_isFlasque (X := Z) ⊤ G
    (isFlasque_of_discreteTopology G) p hp

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

/-- **The higher cohomology of an abelian sheaf on a discrete space vanishes.** -/
theorem subsingleton_sheafH_of_discreteTopology
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u} G p) :=
  AddCommGrpCat.isZero_iff_subsingleton.1
    ((isZero_rightDerived_sections_of_discreteTopology G p hp).of_iso
      (sheafHIsoRightDerivedSections Z G p))

/-- **`H^0` of an abelian sheaf on a discrete space is the product of its stalks.** -/
def sheafHZeroAddEquivPiStalk (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
    Sheaf.H.{u} G 0 ≃+ ∀ z : Z, ToType (TopCat.Presheaf.stalk (X := Z) G.obj z) :=
  (sheafHIsoRightDerivedSections Z G 0 ≪≫
      (sectionsFunctor Z).rightDerivedZeroIsoSelf.app G).addCommGroupIsoToAddEquiv.trans
    (sectionsAddEquivPiStalk G)

end Discrete

/-! ### Proper maps with discrete fibres -/

section DiscreteFibers

variable {X Y : TopCat.{u}} {f : X ⟶ Y}

/-- A finite fibre of a separated map is discrete. -/
theorem discreteTopology_fiber_of_finite (hsep : IsSeparatedMap (f.hom : X → Y)) (y : Y)
    (hfin : (fiber f y).Finite) : DiscreteTopology (fiber f y) := by
  have : T2Space (fiber f y) := ⟨fun a b hab ↦ by
    obtain ⟨s₁, s₂, h₁, h₂, ha, hb, hd⟩ := hsep a b
      ((Set.mem_singleton_iff.1 a.2).trans (Set.mem_singleton_iff.1 b.2).symm)
      (Subtype.coe_injective.ne hab)
    exact ⟨Subtype.val ⁻¹' s₁, Subtype.val ⁻¹' s₂, h₁.preimage continuous_subtype_val,
      h₂.preimage continuous_subtype_val, ha, hb, hd.preimage _⟩⟩
  have : Finite (fiber f y) := hfin.to_subtype
  infer_instance

/-- **For a proper separated map with discrete fibres, `H^n(X, F) ≃ H^n(Y, f_* F)`** for every
abelian sheaf `F` on `X` and every `n`: the higher cohomology of the fibres vanishes. -/
def sheafHAddEquivPushforwardOfDiscreteFibers
    (hf : IsProperMap (f.hom : X → Y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    (hdisc : ∀ y : Y, DiscreteTopology (fiber f y))
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+ Sheaf.H.{u} ((pushforwardSheafFunctor f).obj F) n :=
  (sheafHIsoOfIsZeroHigherDirectImage f F (fun q hq ↦
    isZero_rightDerived_pushforward_of_isZero_fiber hf.isClosedMap
      (fun _ ↦ hf.isCompact_preimage isCompact_singleton) hsep F q fun y ↦
        haveI := hdisc y
        isZero_rightDerived_sections_of_discreteTopology (Z := TopCat.of (fiber f y)) _ q hq)
    n).addCommGroupIsoToAddEquiv

/-- **For a proper separated map with finite fibres, `H^n(X, F) ≃ H^n(Y, f_* F)`** for every
abelian sheaf `F` on `X` and every `n`. -/
def sheafHAddEquivPushforwardOfFiniteFibers
    (hf : IsProperMap (f.hom : X → Y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    (hfin : ∀ y : Y, (fiber f y).Finite)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+ Sheaf.H.{u} ((pushforwardSheafFunctor f).obj F) n :=
  sheafHAddEquivPushforwardOfDiscreteFibers hf hsep
    (fun y ↦ discreteTopology_fiber_of_finite hsep y (hfin y)) F n

/-- **The stalk of a direct image along a closed separated map with a quasi-compact discrete
fibre is the product of the stalks along the fibre**:
`(f_* F)_y ≃ ∏_{x ∈ f⁻¹(y)} (F|_{f⁻¹(y)})_x`. -/
def pushforwardStalkAddEquivPiStalk (y : Y) (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : IsCompact (fiber f y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    [DiscreteTopology (fiber f y)] (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ToType ((sheafStalkFunctor y).obj ((pushforwardSheafFunctor f).obj F)) ≃+
      ∀ x : fiber f y,
        ToType (TopCat.Presheaf.stalk (X := TopCat.of (fiber f y))
          ((restrictionFunctor X (fiber f y)).obj F).obj x) :=
  ((stalkIsoFiberSections y hclosed hcompact hsep).app F).addCommGroupIsoToAddEquiv.trans
    (sectionsAddEquivPiStalk (Z := TopCat.of (fiber f y)) _)

end DiscreteFibers

end TopologicalSpace.ProperBaseChange
