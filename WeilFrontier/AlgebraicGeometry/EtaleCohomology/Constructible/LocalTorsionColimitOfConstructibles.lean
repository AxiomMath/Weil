module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# A torsion étale sheaf is the union of its constructible subsheaves

Let `X` be a Noetherian scheme and `G` a torsion abelian sheaf on the small étale site of `X`,
for instance the abelian sheaf underlying a sheaf of `ℤ/nℤ`-modules with `n ≥ 1`. The
constructible abelian subsheaves of `G` form a directed set under inclusion, and `G` is the
colimit, in the category of abelian sheaves, of the diagram of these subsheaves and their
inclusions.

The proof writes `G` as a filtered colimit `colim Dᵢ` of constructible abelian sheaves (Stacks
03SA (2)). The image of each `Dᵢ ⟶ G` is a constructible subsheaf, because a quotient of a
constructible abelian sheaf on a Noetherian scheme is constructible (Stacks 09BH (2)); so the
constructible subsheaves exhaust `G`. Two constructible subsheaves `A`, `A'` lie in the image of
`A ⊞ A' ⟶ G`, which is constructible for the same reason, so they form a directed set. Finally,
in a Grothendieck abelian category a directed family of subobjects whose supremum is everything
is a colimit diagram (`CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`).

## Main definitions

* `AlgebraicGeometry.constructibleSubobjects`: the constructible subsheaves of an abelian sheaf.
* `AlgebraicGeometry.constructibleSubobjectsDiagram` and
  `AlgebraicGeometry.constructibleSubobjectsCocone`: the diagram of these subsheaves and their
  inclusions, with its cocone to `G`.

## Main results

* `AlgebraicGeometry.isDirectedOrder_constructibleSubobjects`: on a Noetherian scheme they form a
  directed set.
* `AlgebraicGeometry.eq_top_of_forall_constructibleSubobjects_le`: a torsion abelian sheaf on a
  Noetherian scheme is the union of its constructible subsheaves.
* `AlgebraicGeometry.isColimitConstructibleSubobjectsCocone`: a torsion abelian sheaf on a
  Noetherian scheme is the colimit of its constructible subsheaves.
* `AlgebraicGeometry.isColimit_constructibleSubobjectsCocone_zmod`: the statement for the abelian
  sheaf underlying a sheaf of `ℤ/nℤ`-modules.

## Implementation notes

The statement is made for any torsion abelian sheaf, torsion in the local sense of Stacks 0DD7;
the abelian sheaf underlying a sheaf of `ℤ/nℤ`-modules is annihilated by `n`, hence torsion. The
indexing set is the set of subobjects of `G` whose underlying sheaf is constructible, ordered by
inclusion. It is a large type; the colimit statement is first proved on a small copy
(`Shrink`) and transported along the order isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-! ### Instances on the category of abelian sheaves

Instance search for colimits, and for the lattice structure on subobjects, of abelian sheaves on
the small étale site does not terminate within the default budget; they are supplied here from
the Grothendieck abelian structure. -/

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

local instance : HasColimitsOfSize.{u + 1, u + 1}
    (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
  IsGrothendieckAbelian.hasColimits _

local instance : HasLimitsOfSize.{u + 1, u + 1}
    (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
  IsGrothendieckAbelian.hasLimits _

local instance : HasInitial
    (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
  HasZeroObject.hasInitial

local instance : WellPowered.{u + 1}
    (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
  IsGrothendieckAbelian.wellPowered _

local instance (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    CompleteLattice (Subobject G) :=
  Subobject.instCompleteLattice.{u + 1}

/-! ### The constructible subsheaves -/

/-- The constructible subsheaves of an abelian sheaf `G` on the small étale site of `X`: the
subobjects of `G` whose underlying abelian sheaf is constructible. -/
def constructibleSubobjects
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Set (Subobject G) :=
  {A | IsConstructibleAbelianSheaf B X (Subobject.underlying.obj A)}

/-- The diagram of the constructible subsheaves of `G`, indexed by the set of them ordered by
inclusion. -/
def constructibleSubobjectsDiagram
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    constructibleSubobjects B X G ⥤ Sheaf (SmallEtale.topology B X.obj X.property)
      AddCommGrpCat.{u + 1} :=
  (Subtype.mono_coe _).functor ⋙ Subobject.underlying

/-- The cocone of inclusions of the constructible subsheaves of `G` into `G`. -/
def constructibleSubobjectsCocone
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Cocone (constructibleSubobjectsDiagram B X G) where
  pt := G
  ι :=
    { app A := A.1.arrow
      naturality A A' f := by
        simp [constructibleSubobjectsDiagram] }

@[simp]
theorem constructibleSubobjectsCocone_ι_app
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (A : constructibleSubobjects B X G) :
    (constructibleSubobjectsCocone B X G).ι.app A = A.1.arrow :=
  rfl

/-- The zero subsheaf is constructible. -/
theorem bot_mem_constructibleSubobjects
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    ⊥ ∈ constructibleSubobjects B X G :=
  isConstructibleAbelianSheaf_congr B X Subobject.botCoeIsoZero.symm
    (isConstructibleAbelianSheaf_zero B X)

instance (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Nonempty (constructibleSubobjects B X G) :=
  ⟨⟨⊥, bot_mem_constructibleSubobjects B X G⟩⟩

/-- On a Noetherian scheme, the image of a morphism from a constructible abelian sheaf is a
constructible subsheaf. -/
theorem imageSubobject_mem_constructibleSubobjects [IsNoetherian X.obj]
    {G P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (f : P ⟶ G) (hP : IsConstructibleAbelianSheaf B X P) :
    imageSubobject f ∈ constructibleSubobjects B X G :=
  isConstructibleAbelianSheaf_of_epi B X (smallEtaleUnderlyingSetCommutes B X)
    (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X)
    (factorThruImageSubobject f) hP

/-- On a Noetherian scheme, the constructible subsheaves of an abelian sheaf form a directed
set: two of them are contained in the image of the map from their direct sum. -/
instance isDirectedOrder_constructibleSubobjects [IsNoetherian X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsDirectedOrder (constructibleSubobjects B X G) where
  directed A A' := by
    let f := biprod.desc A.1.arrow A'.1.arrow
    have hP : IsConstructibleAbelianSheaf B X
        (Subobject.underlying.obj A.1 ⊞ Subobject.underlying.obj A'.1) :=
      ObjectProperty.prop_biprod
        (fun F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
          IsConstructibleAbelianSheaf B X F) A.2 A'.2
    refine ⟨⟨imageSubobject f, imageSubobject_mem_constructibleSubobjects B X f hP⟩, ?_, ?_⟩
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject f)
        (by simp [f])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject f)
        (by simp [f])

instance isFiltered_constructibleSubobjects [IsNoetherian X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    IsFiltered (constructibleSubobjects B X G) :=
  isFiltered_of_directed_le_nonempty _

/-- On a Noetherian scheme, a torsion abelian sheaf is the union of its constructible
subsheaves: a subobject containing all of them is everything. -/
theorem eq_top_of_forall_constructibleSubobjects_le [IsNoetherian X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) G)
    (M : Subobject G) (hM : ∀ A ∈ constructibleSubobjects B X G, A ≤ M) : M = ⊤ := by
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X G hG
  have hfac (i : I) : M.Factors (ι.app i) := by
    exact Subobject.factors_of_le (ι.app i)
      (hM _ (imageSubobject_mem_constructibleSubobjects B X (ι.app i) (hD i)))
      (by simpa using imageSubobject_factors_comp_self (ι.app i) (𝟙 _))
  let s : Cocone D :=
    { pt := Subobject.underlying.obj M
      ι :=
        { app i := M.factorThru (ι.app i) (hfac i)
          naturality i j g := by
            rw [← cancel_mono M.arrow]
            simp only [Category.assoc, Subobject.factorThru_arrow]
            simp } }
  have hs : hc.desc s ≫ M.arrow = 𝟙 G := by
    refine hc.hom_ext fun i => ?_
    rw [← Category.assoc, hc.fac s i]
    simp [s]
  have : IsSplitEpi M.arrow := ⟨⟨hc.desc s, hs⟩⟩
  have : IsIso M.arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow M

/-- **A torsion étale sheaf is the colimit of its constructible subsheaves.** Let `X` be a
Noetherian scheme and `G` a torsion abelian sheaf on the small étale site of `X`. Then `G`,
with the inclusions, is the colimit of the diagram of its constructible subsheaves (a directed
set, by `AlgebraicGeometry.isDirectedOrder_constructibleSubobjects`). -/
def isColimitConstructibleSubobjectsCocone [IsNoetherian X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) G) :
    IsColimit (constructibleSubobjectsCocone B X G) := by
  let S := constructibleSubobjects B X G
  haveI : Small.{u + 1} (Subobject G) := WellPowered.subobject_small G
  haveI : Small.{u + 1} S := small_subtype _ _
  let e : S ≃ Shrink.{u + 1} S := equivShrink S
  letI : Preorder (Shrink.{u + 1} S) := Preorder.lift e.symm
  let o : Shrink.{u + 1} S ≃o S := { toEquiv := e.symm, map_rel_iff' := Iff.rfl }
  haveI : IsFiltered (Shrink.{u + 1} S) := IsFiltered.of_equivalence o.equivalence.symm
  let F : Shrink.{u + 1} S ⥤ MonoOver G :=
    o.equivalence.functor ⋙ (Subtype.mono_coe _).functor ⋙ Subobject.representative
  let c : Cocone (F ⋙ MonoOver.forget G) :=
    { pt := Over.mk (𝟙 G)
      ι :=
        { app j := Over.homMk (F.obj j).obj.hom
          naturality j j' g := by
            ext1
            simp } }
  haveI : Mono c.pt.hom := by dsimp [c]; infer_instance
  have h : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
    have htop : (⨆ j, Subobject.mk (F.obj j).obj.hom) = ⊤ :=
      eq_top_of_forall_constructibleSubobjects_le B X G hG _ fun A hA =>
        le_iSup_of_le (o.symm ⟨A, hA⟩) (by simp [F])
    rw [htop]
    exact (Subobject.mk_eq_top_of_isIso (𝟙 G))
  have hc := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup F c h
  refine IsColimit.ofWhiskerEquivalence o.equivalence
    (IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _) fun j => ?_))
  exact Category.comp_id _

/-- The abelian sheaf underlying a sheaf of `ℤ/nℤ`-modules, `n ≥ 1`, is torsion. -/
theorem torsionSheafProperty_sheafCompose_forget₂_zmod (n : ℕ) [NeZero n]
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n))) :
    Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property)
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) := by
  intro U x
  refine ⟨⊤, (SmallEtale.topology B X.obj X.property).top_mem U, fun V f _ => ⟨n,
    Nat.pos_of_ne_zero (NeZero.ne n), ?_⟩⟩
  change n • ((M.obj.map f.op) x : M.obj.obj (Opposite.op V)) = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

/-- **[FK, I.4, p. 43]** Let `X` be a Noetherian scheme, `n ≥ 1`, `Λ = ℤ/nℤ` and `M` a sheaf of
`Λ`-modules on the small étale site of `X`, with underlying abelian sheaf `G`. The constructible
abelian subsheaves of `G` form a nonempty directed set under inclusion, and `G` is the colimit,
in the category of abelian sheaves, of the diagram of these subsheaves and their inclusions. -/
@[weil "lem_fk104_lambda_sheaf_is_filtered_colimit_constructible"]
theorem isColimit_constructibleSubobjectsCocone_zmod [IsNoetherian X.obj] (n : ℕ) [NeZero n]
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n))) :
    IsDirectedOrder (constructibleSubobjects B X
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M)) ∧
      Nonempty (constructibleSubobjects B X
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M)) ∧
      Nonempty (IsColimit (constructibleSubobjectsCocone B X
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M))) :=
  ⟨inferInstance, inferInstance, ⟨isColimitConstructibleSubobjectsCocone B X _
    (torsionSheafProperty_sheafCompose_forget₂_zmod B X n M)⟩⟩

end AlgebraicGeometry

end

/-! ### A torsion étale sheaf is the directed union of its constructible subsheaves -/

/-!
# A torsion étale sheaf is the directed union of its constructible subsheaves

Let `X` be a Noetherian scheme and `F` a torsion abelian sheaf on the small étale site of `X`.
The constructible abelian subsheaves of `F` form a directed set under inclusion, and `F` is the
colimit of this directed system: the cocone formed by the inclusions `A ⟶ F` is a colimit cocone.

The proof starts from Stacks 03SA (2), which writes `F` as the colimit of a small filtered
diagram `D` of constructible abelian sheaves. The image of each `D i ⟶ F` is a constructible
subsheaf (Stacks 09BH (2): a quotient of a constructible sheaf on a Noetherian scheme is
constructible). Conversely a constructible subsheaf `A ⊆ F` is a compact object
(Stacks 09Z4), so its inclusion factors through some `D i`, and `A` lies in the image of
`D i ⟶ F`. Hence the images of the `D i` are cofinal among the constructible subsheaves, which
gives both directedness and the colimit property.

## Main definitions

* `AlgebraicGeometry.SmallEtale.ConstructibleSubobject`: the constructible abelian subsheaves of
  an abelian sheaf, ordered by inclusion.
* `AlgebraicGeometry.SmallEtale.constructibleSubobjectCocone`: the cocone of their inclusions.

## Main results

* `AlgebraicGeometry.SmallEtale.isDirected_constructibleSubobject`: for a torsion sheaf on a
  Noetherian scheme the constructible subsheaves form a (nonempty) directed set.
* `AlgebraicGeometry.SmallEtale.nonempty_isColimit_constructibleSubobjectCocone`: the inclusions
  of the constructible subsheaves exhibit a torsion sheaf as their colimit.

## Implementation notes

"The canonical map `colim_{A ∈ S} A ⟶ F` is an isomorphism" is stated as: the cocone of
inclusions is a colimit cocone. This is equivalent, and it does not presuppose the existence of
a colimit over the (large) index `S`. Torsion is `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`,
the local condition, which for a locally Noetherian scheme is equivalent to every group of
sections over a Noetherian separated étale `X`-scheme being torsion.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The constructible abelian subsheaves of an abelian sheaf `F` on the small étale site of `X`,
ordered by inclusion. -/
abbrev ConstructibleSubobject
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
  {A : Subobject F // IsConstructibleAbelianSheaf B X (Subobject.underlying.obj A)}

/-- The diagram of the constructible abelian subsheaves of `F`. -/
abbrev constructibleSubobjectDiagram
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    ConstructibleSubobject B X F ⥤ Sheaf (SmallEtale.topology B X.obj X.property)
      AddCommGrpCat.{u + 1} :=
  (Subtype.mono_coe _).functor ⋙ Subobject.underlying

theorem constructibleSubobjectDiagram_map
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    {A A' : ConstructibleSubobject B X F} (g : A ⟶ A') :
    (constructibleSubobjectDiagram B X F).map g = Subobject.ofLE A.1 A'.1 (leOfHom g) := rfl

/-- The cocone of the inclusions `A ⟶ F` of the constructible abelian subsheaves of `F`. -/
def constructibleSubobjectCocone
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Cocone (constructibleSubobjectDiagram B X F) where
  pt := F
  ι := { app A := A.1.arrow }

@[simp]
theorem constructibleSubobjectCocone_ι_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (A : ConstructibleSubobject B X F) :
    (constructibleSubobjectCocone B X F).ι.app A = A.1.arrow := rfl

section Noetherian

variable [IsNoetherian X.obj]

/-- On a Noetherian scheme every constructible abelian sheaf is a finitely presentable object. -/
private theorem isFinitelyPresentable_of_isConstructible
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : IsConstructibleAbelianSheaf B X G) : IsFinitelyPresentable.{u + 1} G := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have : CompactSpace X.obj := hN.2
  have : IsLocallyNoetherian X.obj := hN.1
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  let := SmallEtale.isGrothendieckAbelian_sheaf_succ B X.obj X.property
  let : ∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
    fun S T g => Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence
      (smallEtaleBaseChange B g) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
    fun T V => Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ
      (SmallEtale.topology B T.obj T.property) V
  exact isFinitelyPresentable_of_isConstructibleAbelianSheaf B X
    (hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B X) G hG

/-- The image of a morphism from a constructible abelian sheaf, as a constructible subsheaf. -/
private def imageConstructibleSubobject
    {G F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (f : G ⟶ F)
    (hG : IsConstructibleAbelianSheaf B X G) : ConstructibleSubobject B X F :=
  ⟨imageSubobject f, isConstructibleAbelianSheaf_of_epi B X (smallEtaleUnderlyingSetCommutes B X)
    (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X)
    (factorThruImageSubobject f) hG⟩

variable {B X}

/-- If `F` is a filtered colimit of constructible sheaves `D i`, every constructible subsheaf of
`F` lies in the image of some `D i ⟶ F`. -/
private theorem exists_le_imageSubobject
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    {ι : D ⟶ (Functor.const I).obj F} (hc : IsColimit (Cocone.mk F ι))
    (A : ConstructibleSubobject B X F) :
    ∃ (i : I) (p : Subobject.underlying.obj A.1 ⟶ D.obj i), p ≫ ι.app i = A.1.arrow := by
  have := isFinitelyPresentable_of_isConstructible B X _ A.2
  exact IsFinitelyPresentable.exists_hom_of_isColimit hc A.1.arrow

/-- **The constructible subsheaves of a torsion sheaf form a directed set.** Let `X` be a
Noetherian scheme and `F` a torsion abelian sheaf on its small étale site. Then the constructible
abelian subsheaves of `F` form a nonempty set, directed under inclusion. -/
@[weil "prop_fk104_torsion_sheaf_is_filtered_colimit_constructible"]
theorem isDirected_constructibleSubobject
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsTorsionSheaf B X.obj X.property F) :
    Nonempty (ConstructibleSubobject B X F) ∧
      IsDirected (ConstructibleSubobject B X F) (· ≤ ·) := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have : CompactSpace X.obj := hN.2
  have : IsLocallyNoetherian X.obj := hN.1
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X F hF
  refine ⟨⟨imageConstructibleSubobject B X (ι.app (IsFiltered.nonempty.some)) (hD _)⟩,
    ⟨fun A₁ A₂ => ?_⟩⟩
  obtain ⟨i₁, p₁, hp₁⟩ := exists_le_imageSubobject hc A₁
  obtain ⟨i₂, p₂, hp₂⟩ := exists_le_imageSubobject hc A₂
  let k := IsFiltered.max i₁ i₂
  refine ⟨imageConstructibleSubobject B X (ι.app k) (hD k), ?_, ?_⟩
  · refine Subobject.le_of_comm (p₁ ≫ D.map (IsFiltered.leftToMax i₁ i₂) ≫
      factorThruImageSubobject (ι.app k)) ?_
    simp only [imageConstructibleSubobject, Category.assoc, imageSubobject_arrow_comp]
    rw [ι.naturality]
    simpa using hp₁
  · refine Subobject.le_of_comm (p₂ ≫ D.map (IsFiltered.rightToMax i₁ i₂) ≫
      factorThruImageSubobject (ι.app k)) ?_
    simp only [imageConstructibleSubobject, Category.assoc, imageSubobject_arrow_comp]
    rw [ι.naturality]
    simpa using hp₂

/-- **A torsion sheaf is the filtered colimit of its constructible subsheaves.** Let `X` be a
Noetherian scheme and `F` a torsion abelian sheaf on its small étale site. Then the inclusions
`A ⟶ F` of the constructible abelian subsheaves `A` of `F` exhibit `F` as the colimit of the
directed system of these subsheaves: the canonical map `colim_A A ⟶ F` is an isomorphism. -/
@[weil "prop_fk104_torsion_sheaf_is_filtered_colimit_constructible"]
theorem nonempty_isColimit_constructibleSubobjectCocone
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsTorsionSheaf B X.obj X.property F) :
    Nonempty (IsColimit (constructibleSubobjectCocone B X F)) := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have : CompactSpace X.obj := hN.2
  have : IsLocallyNoetherian X.obj := hN.1
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X F hF
  let im : I → ConstructibleSubobject B X F :=
    fun i => imageConstructibleSubobject B X (ι.app i) (hD i)
  have him_le {i k : I} (f : i ⟶ k) : im i ≤ im k := by
    have h := imageSubobject_comp_le (D.map f) (ι.app k)
    rw [ι.naturality] at h
    simpa [im, imageConstructibleSubobject] using h
  -- the comparison `D i ⟶ im i`
  let q : ∀ i, D.obj i ⟶ Subobject.underlying.obj (im i).1 :=
    fun i => factorThruImageSubobject (ι.app i)
  have hq (i : I) : q i ≫ (im i).1.arrow = ι.app i := imageSubobject_arrow_comp _
  refine ⟨{ desc := fun s => hc.desc (Cocone.mk s.pt
      { app := fun i => q i ≫ s.ι.app (im i)
        naturality := fun i k f => ?_ })
            fac := fun s A => ?_
            uniq := fun s m hm => ?_ }⟩
  · -- naturality of the induced cocone on `D`
    have hw := s.w (homOfLE (him_le f))
    rw [constructibleSubobjectDiagram_map] at hw
    have h : D.map f ≫ q k = q i ≫ Subobject.ofLE _ _ (him_le f) := by
      rw [← cancel_mono (im k).1.arrow, Category.assoc, Category.assoc, Subobject.ofLE_arrow, hq,
        hq, ι.naturality]
      simp
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [reassoc_of% h, hw]
  · obtain ⟨i, p, hp⟩ := exists_le_imageSubobject hc A
    have hle : A ≤ im i := Subobject.le_of_comm (p ≫ q i) (by rw [Category.assoc, hq, hp])
    have hpq : p ≫ q i = Subobject.ofLE _ _ hle := by
      rw [← cancel_mono (im i).1.arrow, Category.assoc, Subobject.ofLE_arrow, hq, hp]
    have hw := s.w (homOfLE hle)
    rw [constructibleSubobjectDiagram_map] at hw
    rw [constructibleSubobjectCocone_ι_app, ← hp]
    refine (Category.assoc _ _ _).trans ?_
    erw [hc.fac]
    exact ((reassoc_of% hpq) _).trans hw
  · refine hc.hom_ext fun i => ?_
    erw [hc.fac]
    rw [← hq]
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (q i ≫ ·) (hm (im i))

end Noetherian

end AlgebraicGeometry.SmallEtale

end
