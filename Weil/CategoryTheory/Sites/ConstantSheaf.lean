module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful
public import Weil.Attr
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# A sheaf on a connected scheme is constant iff it is the constant sheaf on its global sections

Let `X` be a connected scheme and `F` a sheaf of sets on the small étale site of `X`. Then `F`
is constant if and only if `F ≅ F(X)_X`, the constant sheaf on the set of global sections of `F`.

The proof goes through the global sections of a constant sheaf. The sheafification of the
constant presheaf with value `M` is the sheaf `U ↦ C(|U|, M)` of continuous maps into the
discrete space `M`, i.e. of locally constant maps `|U| → M`; on a connected nonempty `X` these
are the constant maps, so `M_X(X) = M`. Hence the constant sheaf functor is fully faithful (the
unit of its adjunction with the global sections functor is an isomorphism), and a sheaf is in its
essential image exactly when the counit `F(X)_X ⟶ F` is an isomorphism.

## Main results

* `CategoryTheory.Sheaf.isConstant_iff_nonempty_iso_constantSheaf_obj_sections` — on a site with
  a terminal object `T` whose constant sheaf functor has invertible unit, a sheaf `F` is constant
  iff `F ≅ F(T)_T`.
* `AlgebraicGeometry.SmallEtale.bijective_toSheafify_app_final` — on a connected scheme `X`,
  the map `M → M_X(X)` is a bijection.
* `AlgebraicGeometry.SmallEtale.isIso_constantSheafAdj_unit` — hence the unit of the constant
  sheaf adjunction on the small étale site of a connected scheme is an isomorphism.
* `AlgebraicGeometry.SmallEtale.isConstant_iff_nonempty_iso_constantSheaf_sections` — a sheaf of
  sets on the small étale site of a connected scheme `X` is constant iff `F ≅ F(X)_X`.

## Implementation notes

The étale site is the small étale site `AlgebraicGeometry.SmallEtale B X hX` of a big étale site
`B` containing `X`, whose final object `AlgebraicGeometry.SmallEtale.final` is `X` over itself;
"constant" is `CategoryTheory.Sheaf.IsConstant`, membership in the essential image of the
constant sheaf functor (the sheafified constant presheaf). Sheaves of sets take values in
`Type (max (u + 1) v)`, the universes in which sheafification exists on this site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D : Type*} [Category* D]
  [HasWeakSheafify J D]

/-- On a site with terminal object `T` whose constant sheaf functor has invertible unit (i.e. is
fully faithful), a sheaf `F` is constant if and only if it is isomorphic to the constant sheaf on
its sections over `T`. -/
theorem isConstant_iff_nonempty_iso_constantSheaf_obj_sections {T : C} (hT : IsTerminal T)
    [IsIso (constantSheafAdj J D hT).unit] (F : Sheaf J D) :
    F.IsConstant J ↔ Nonempty (F ≅ (constantSheaf J D).obj (F.obj.obj (op T))) := by
  have hff := (constantSheafAdj J D hT).fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  constructor
  · intro h
    rw [isConstant_iff_isIso_counit_app J F hT] at h
    exact ⟨(asIso ((constantSheafAdj J D hT).counit.app F)).symm⟩
  · rintro ⟨e⟩
    exact isConstant_of_iso J e

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map from the constant presheaf with value `M` on the small étale site of `S` to the
presheaf `U ↦ C(|U|, M)`, sending `m` to the constant map with value `m`. -/
def constToContinuousMap (M : Type (max (u + 1) v)) [TopologicalSpace M] :
    (Functor.const (SmallEtale B S hS)ᵒᵖ).obj M ⟶
      (toScheme B S hS).op ⋙ continuousMapPresheaf.{max (u + 1) v, u} M where
  app T := TypeCat.ofHom fun m => ContinuousMap.const _ m
  naturality _ _ _ := by
    ext
    rfl

lemma constToContinuousMap_app_apply (M : Type (max (u + 1) v)) [TopologicalSpace M]
    (T : (SmallEtale B S hS)ᵒᵖ) (m : M) :
    (constToContinuousMap B S hS M).app T m = ContinuousMap.const _ m :=
  rfl

/-- The presheaf `U ↦ C(|U|, M)` is a sheaf on the small étale site. -/
theorem isSheaf_continuousMapPresheaf (M : Type (max (u + 1) v)) [TopologicalSpace M] :
    Presheaf.IsSheaf (topology B S hS)
      ((toScheme B S hS).op ⋙ continuousMapPresheaf.{max (u + 1) v, u} M) := by
  have hG : Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheaf.{max (u + 1) v, u} M) :=
    isSheaf_fpqcTopology_continuousMapPresheaf M
  have hO : Presheaf.IsSheaf (Scheme.fpqcTopology.over (B.obj S hS).obj)
      ((Over.forget _).op ⋙ continuousMapPresheaf.{max (u + 1) v, u} M) :=
    Functor.op_comp_isSheaf_of_isSheaf (Over.forget _) _ Scheme.fpqcTopology _ hG
  exact isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS _ hO

/-- Two values with the same constant map agree locally: on a nonempty object they are equal,
and an empty object is covered by the empty sieve. -/
theorem constToContinuousMap_isLocallyInjective (M : Type (max (u + 1) v))
    [TopologicalSpace M] :
    Presheaf.IsLocallyInjective (topology B S hS) (constToContinuousMap B S hS M) := by
  classical
  have hBot : ∀ {T : SmallEtale B S hS}, IsEmpty ((toScheme B S hS).obj T) →
      (⊥ : Sieve T) ∈ topology B S hS T := fun {_} =>
    openCoverData_bottom (toScheme B S hS) (topology B S hS) (smallEtale_openCoverData B S hS)
  refine ⟨fun {T} (a b : M) hab => ?_⟩
  change (ContinuousMap.const _ a : C((toScheme B S hS).obj T.unop, M)) =
    ContinuousMap.const _ b at hab
  by_cases hT : Nonempty ((toScheme B S hS).obj T.unop)
  · obtain ⟨x⟩ := hT
    have hab' : a = b := by
      simpa using congrArg (fun f => f x) hab
    subst b
    simp
  · by_cases hab' : a = b
    · subst b
      simp
    · have heq : Presheaf.equalizerSieve
          (F := (Functor.const (SmallEtale B S hS)ᵒᵖ).obj M) (X := T) a b = ⊥ := by
        ext Y f
        simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply, iff_false]
        intro hf
        exact hab' (by simpa using hf)
      rw [heq]
      exact hBot (not_nonempty_iff.mp hT)

/-- A continuous map into a discrete space is locally constant, hence locally a constant
section, since an open cover of an étale `S`-scheme is refined by an étale covering. -/
theorem constToContinuousMap_isLocallySurjective (M : Type (max (u + 1) v))
    [TopologicalSpace M] [DiscreteTopology M] :
    Presheaf.IsLocallySurjective (topology B S hS) (constToContinuousMap B S hS M) := by
  classical
  refine ⟨fun {T} s => ?_⟩
  let s₀ : C((toScheme B S hS).obj T, M) := s
  let V : (toScheme B S hS).obj T → ((toScheme B S hS).obj T).Opens := fun x =>
    ⟨s₀ ⁻¹' {s₀ x}, (isOpen_discrete _).preimage s₀.continuous⟩
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover]
    refine le_antisymm le_top fun x _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, rfl⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtale_openCoverData B S hS V hV
  have hle : Sieve.ofArrows W a ≤
      Presheaf.imageSieve (constToContinuousMap B S hS M) s := by
    intro Y f hf
    obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
    apply (Presheaf.imageSieve (constToContinuousMap B S hS M) s).downward_closed
    refine ⟨s₀ (r x), ?_⟩
    change ContinuousMap.const _ (s₀ (r x)) = s₀.comp ((toScheme B S hS).map (a x)).base.hom
    refine ContinuousMap.ext fun y => ?_
    exact (hmaps x y).symm
  exact (topology B S hS).superset_covering hle hcover

variable [ConnectedSpace S]

/-- **`M_X(X) = M`.** On a connected scheme `S`, the map from `M` to the global sections of the
constant sheaf with value `M` on the small étale site is a bijection. -/
theorem bijective_toSheafify_app_final (M : Type (max (u + 1) v)) :
    Function.Bijective ((toSheafify (topology B S hS)
      ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj M)).app (op (final B S hS))) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have := GrothendieckTopology.wEqualsLocallyBijective_type.{max (u + 1) v} (topology B S hS)
  let J := topology B S hS
  let P₀ := (Functor.const (SmallEtale B S hS)ᵒᵖ).obj M
  let α := constToContinuousMap B S hS M
  have hP := isSheaf_continuousMapPresheaf B S hS M
  have := constToContinuousMap_isLocallyInjective B S hS M
  have := constToContinuousMap_isLocallySurjective B S hS M
  have hχ : IsIso (sheafifyLift J α hP) :=
    Presheaf.isIso_of_isLocallyBijective_fac J (toSheafify J P₀) α
      ((presheafToSheaf J _).obj P₀).property hP (toSheafify_sheafifyLift J α hP)
  have hχapp : Function.Bijective ((sheafifyLift J α hP).app (op (final B S hS))) := by
    rw [← isIso_iff_bijective]
    infer_instance
  have hα : Function.Bijective (α.app (op (final B S hS))) := by
    let X := (toScheme B S hS).obj (final B S hS)
    have : ConnectedSpace X := inferInstanceAs (ConnectedSpace S)
    obtain ⟨x₀⟩ := ConnectedSpace.toNonempty (α := X)
    refine ⟨fun (a b : M) hab => ?_, fun f => ?_⟩
    · change (ContinuousMap.const X a : C(X, M)) = ContinuousMap.const X b at hab
      simpa using DFunLike.congr_fun hab x₀
    · let f' : C(X, M) := f
      refine ⟨f' x₀, ?_⟩
      change ContinuousMap.const X (f' x₀) = f'
      refine ContinuousMap.ext fun y => ?_
      exact PreconnectedSpace.constant inferInstance f'.continuous
  have hcomp : (sheafifyLift J α hP).app (op (final B S hS)) ∘
      (toSheafify J P₀).app (op (final B S hS)) = α.app (op (final B S hS)) := by
    funext m
    exact congrArg (fun φ => φ.app (op (final B S hS)) m) (toSheafify_sheafifyLift J α hP)
  rw [← hcomp] at hα
  exact (Function.Bijective.of_comp_iff' hχapp _).mp hα

/-- On a connected scheme the unit `M ⟶ M_X(X)` of the constant sheaf adjunction on the small
étale site is an isomorphism; equivalently, the constant sheaf functor is fully faithful. -/
instance isIso_constantSheafAdj_unit :
    IsIso (constantSheafAdj (topology B S hS) (Type (max (u + 1) v))
      (finalIsTerminal B S hS)).unit := by
  have : ∀ M, IsIso ((constantSheafAdj (topology B S hS) (Type (max (u + 1) v))
      (finalIsTerminal B S hS)).unit.app M) := fun M =>
    (isIso_iff_bijective _).2 (bijective_toSheafify_app_final B S hS M)
  exact NatIso.isIso_of_isIso_app _

/-- **A sheaf on a connected scheme is constant iff it is the constant sheaf on its global
sections.** Let `S` be a connected scheme and `F` a sheaf of sets on its small étale site. Then
`F` is constant if and only if `F ≅ F(S)_S`. -/
@[weil "lem_fk104_constant_iff_iso_global_sections"]
theorem isConstant_iff_nonempty_iso_constantSheaf_sections
    (F : Sheaf (topology B S hS) (Type (max (u + 1) v))) :
    F.IsConstant (topology B S hS) ↔
      Nonempty (F ≅ (constantSheaf (topology B S hS) (Type (max (u + 1) v))).obj
        (F.obj.obj (op (final B S hS)))) :=
  Sheaf.isConstant_iff_nonempty_iso_constantSheaf_obj_sections _ (finalIsTerminal B S hS) F

end AlgebraicGeometry.SmallEtale

end

/-! ### The constant sheaf on a topological space is the sheaf of locally constant maps -/

/-!
# The constant sheaf on a topological space is the sheaf of locally constant maps

Let `X` be a topological space and `M` a set (resp. an abelian group). The constant sheaf `M_X`
is the sheafification of the constant presheaf with value `M`, i.e. Mathlib's
`CategoryTheory.constantSheaf (Opens.grothendieckTopology X)` applied to `M`. We show that it is
the sheaf `V ↦ LocallyConstant V M` of locally constant maps (with pointwise addition when `M` is
an abelian group), restriction being restriction of maps.

The proof: the inclusion of constant maps into locally constant maps is a morphism from the
constant presheaf to a sheaf which is locally injective and locally surjective (a locally
constant map is constant near every point), so the induced morphism from the sheafification is
an isomorphism.

## Main definitions

* `TopCat.locallyConstantSheaf`, `TopCat.locallyConstantSheafAb`: the sheaf of locally constant
  maps into a set, resp. an abelian group.
* `TopCat.constantSheafIsoLocallyConstantSheaf`: `M_X ≅ (V ↦ LocallyConstant V M)`, for a set `M`.
* `TopCat.constantSheafAbIsoLocallyConstantSheafAb`: the same for an abelian group `A`, as sheaves
  of abelian groups.
* `TopCat.constantSheafSectionsEquiv`, `TopCat.constantSheafAbSectionsAddEquiv`: the resulting
  identification of the sections of `M_X` over `V` with `LocallyConstant V M`.

## Main results

* `TopCat.constantSheafSectionsEquiv_toSheafify`, `TopCat.constantSheafSectionsEquiv_map`: the
  identification sends the section given by `m : M` to the constant map `m`, and is compatible with
  restriction (and likewise for the abelian-group version).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

variable (X : TopCat.{u}) (M : Type u)

/-- The presheaf of locally constant maps `V ↦ LocallyConstant V M`. -/
@[simps]
def locallyConstantPresheaf : X.Presheaf (Type u) where
  obj V := LocallyConstant V.unop M
  map {V W} i := ↾fun f => f.comap ⟨_, continuous_inclusion i.unop.le⟩

/-- Being locally constant is a local predicate. -/
def isLocallyConstantLocalPredicate : LocalPredicate (fun _ : X => M) where
  pred {_} f := IsLocallyConstant f
  res {_ _} i _ h := h.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f w := by
    let _ : TopologicalSpace M := ⊥
    have : DiscreteTopology M := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact (continuousLocal X M).locality f fun x => by
      obtain ⟨V, hx, i, h⟩ := w x
      exact ⟨V, hx, i, (IsLocallyConstant.iff_continuous _).1 h⟩

/-- `locallyConstantPresheaf` is the presheaf of functions satisfying the local predicate
`isLocallyConstantLocalPredicate`. -/
def locallyConstantPresheafIsoSubpresheafToTypes :
    locallyConstantPresheaf X M ≅
      subpresheafToTypes (isLocallyConstantLocalPredicate X M).toPrelocalPredicate :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f : LocallyConstant V.unop M => ⟨f, f.isLocallyConstant⟩
      invFun := fun f => (⟨f.1, f.2⟩ : LocallyConstant V.unop M)
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ => rfl)

theorem isSheaf_locallyConstantPresheaf : (locallyConstantPresheaf X M).IsSheaf :=
  (Presheaf.isSheaf_of_iso_iff (locallyConstantPresheafIsoSubpresheafToTypes X M)).2
    (subpresheafToTypes.isSheaf _)

/-- The sheaf of locally constant maps `V ↦ LocallyConstant V M`. -/
abbrev locallyConstantSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
  ⟨locallyConstantPresheaf X M, isSheaf_locallyConstantPresheaf X M⟩

/-- The inclusion of the constant presheaf into the presheaf of locally constant maps. -/
@[simps]
def constToLocallyConstantPresheaf :
    (Functor.const (Opens X)ᵒᵖ).obj M ⟶ locallyConstantPresheaf X M where
  app V := ↾fun m => LocallyConstant.const _ m

theorem isLocallyInjective_constToLocallyConstantPresheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constToLocallyConstantPresheaf X M) where
  equalizerSieve_mem {V} a b h := by
    intro z hz
    refine ⟨V.unop, 𝟙 _, ?_, hz⟩
    have h' : (LocallyConstant.const _ a : LocallyConstant V.unop M) =
        LocallyConstant.const _ b := h
    have := congr($h' ⟨z, hz⟩)
    simpa [Presheaf.equalizerSieve] using this

theorem isLocallySurjective_constToLocallyConstantPresheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constToLocallyConstantPresheaf X M) where
  imageSieve_mem {V} s' := by
    let s : LocallyConstant V M := s'
    intro z hz
    let W : Opens X := ⟨Subtype.val '' (s ⁻¹' {s ⟨z, hz⟩}),
      V.isOpen.isOpenMap_subtype_val _ (s.isLocallyConstant.isOpen_fiber _)⟩
    have hWV : W ≤ V := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    refine ⟨W, homOfLE hWV, ⟨s ⟨z, hz⟩, ?_⟩, ⟨⟨z, hz⟩, rfl, rfl⟩⟩
    refine LocallyConstant.ext fun ⟨y, hy⟩ => ?_
    obtain ⟨y', hy', rfl⟩ := hy
    exact hy'.symm

/-- The comparison map from the constant sheaf `M_X` (the sheafification of the constant
presheaf) to the sheaf of locally constant maps, induced by the inclusion of constant maps. -/
noncomputable def constantSheafToLocallyConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj M ⟶ locallyConstantSheaf X M :=
  Sheaf.homEquiv.symm (sheafifyLift _ (constToLocallyConstantPresheaf X M)
    (isSheaf_locallyConstantPresheaf X M))

@[reassoc (attr := simp)]
lemma toSheafify_comp_constantSheafToLocallyConstantSheaf_hom :
    toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj M) ≫
        (constantSheafToLocallyConstantSheaf X M).hom =
      constToLocallyConstantPresheaf X M :=
  toSheafify_sheafifyLift _ _ _

instance : IsIso (constantSheafToLocallyConstantSheaf X M) := by
  have : (Opens.grothendieckTopology X).HasSheafCompose (forget (Type u)) :=
    hasSheafCompose_of_preservesMulticospan _ _
  refine (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso _).1 ?_
  have fac := toSheafify_comp_constantSheafToLocallyConstantSheaf_hom X M
  have hi := isLocallyInjective_constToLocallyConstantPresheaf X M
  have hs := isLocallySurjective_constToLocallyConstantPresheaf X M
  have ht := ((Opens.grothendieckTopology X).W_toSheafify
    ((Functor.const (Opens X)ᵒᵖ).obj M)).isLocallySurjective
  exact ⟨@Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      _ _ (Opens.grothendieckTopology X) _ _ _ _ _ _ _ _ _ _ _ _ fac hi ht,
    @Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      _ _ (Opens.grothendieckTopology X) _ _ _ _ _ _ _ _ _ _ _ _ fac hs⟩

/-- The constant sheaf `M_X` on a topological space `X` is the sheaf of locally constant maps:
`M_X(V) = LocallyConstant V M`, with restriction of maps. -/
@[weil "def_fk111_space_constant_sheaf"]
noncomputable def constantSheafIsoLocallyConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj M ≅ locallyConstantSheaf X M :=
  asIso (constantSheafToLocallyConstantSheaf X M)

/-- The sections of the constant sheaf `M_X` over `V` are the locally constant maps `V → M`. -/
noncomputable def constantSheafSectionsEquiv (V : Opens X) :
    ((constantSheaf (Opens.grothendieckTopology X) (Type u)).obj M).obj.obj (op V) ≃
      LocallyConstant V M :=
  (((sheafToPresheaf _ _).mapIso (constantSheafIsoLocallyConstantSheaf X M)).app (op V)).toEquiv

/-- Under `constantSheafSectionsEquiv`, the section of `M_X` given by `m : M` is the constant
map with value `m`. -/
@[simp]
lemma constantSheafSectionsEquiv_toSheafify (V : Opens X) (m : M) :
    constantSheafSectionsEquiv X M V
        ((toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj M)).app
          (op V) m) =
      LocallyConstant.const V m :=
  congr($(toSheafify_comp_constantSheafToLocallyConstantSheaf_hom X M).app (op V) m)

/-- `constantSheafSectionsEquiv` is compatible with restriction: restricting a section of `M_X`
from `V` to `W ≤ V` corresponds to restricting the locally constant map. -/
lemma constantSheafSectionsEquiv_map {V W : Opens X} (h : W ≤ V)
    (s : ((constantSheaf (Opens.grothendieckTopology X) (Type u)).obj M).obj.obj (op V)) :
    constantSheafSectionsEquiv X M W
        (((constantSheaf (Opens.grothendieckTopology X) (Type u)).obj M).obj.map
          (homOfLE h).op s) =
      (constantSheafSectionsEquiv X M V s).comap ⟨_, continuous_inclusion h⟩ :=
  congr($((constantSheafToLocallyConstantSheaf X M).hom.naturality (homOfLE h).op) s)

section AddCommGroup

variable (A : Type u) [AddCommGroup A]

/-- The presheaf of abelian groups `V ↦ LocallyConstant V A`, with pointwise addition. -/
@[simps]
def locallyConstantPresheafAb : X.Presheaf AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (LocallyConstant V.unop A)
  map {V W} i := AddCommGrpCat.ofHom
    (LocallyConstant.comapAddMonoidHom ⟨_, continuous_inclusion i.unop.le⟩)

/-- The underlying presheaf of sets of `locallyConstantPresheafAb` is
`locallyConstantPresheaf`. -/
def locallyConstantPresheafAbCompForgetIso :
    locallyConstantPresheafAb X A ⋙ forget AddCommGrpCat.{u} ≅ locallyConstantPresheaf X A :=
  Iso.refl _

theorem isSheaf_locallyConstantPresheafAb :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (locallyConstantPresheafAb X A) :=
  CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
    ((CategoryTheory.Presheaf.isSheaf_of_iso_iff (locallyConstantPresheafAbCompForgetIso X A)).2
      (isSheaf_locallyConstantPresheaf X A))

/-- The sheaf of abelian groups `V ↦ LocallyConstant V A`. -/
abbrev locallyConstantSheafAb :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨locallyConstantPresheafAb X A, isSheaf_locallyConstantPresheafAb X A⟩

/-- The inclusion of the constant presheaf of abelian groups into the presheaf of locally
constant maps. -/
@[simps]
def constToLocallyConstantPresheafAb :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A) ⟶ locallyConstantPresheafAb X A where
  app V := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom)

theorem isLocallyInjective_constToLocallyConstantPresheafAb :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constToLocallyConstantPresheafAb X A) where
  equalizerSieve_mem {V} a b h := by
    intro z hz
    refine ⟨V.unop, 𝟙 _, ?_, hz⟩
    have h' : (LocallyConstant.const _ a : LocallyConstant V.unop A) =
        LocallyConstant.const _ b := h
    have := congr($h' ⟨z, hz⟩)
    simpa [Presheaf.equalizerSieve] using this

theorem isLocallySurjective_constToLocallyConstantPresheafAb :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constToLocallyConstantPresheafAb X A) where
  imageSieve_mem {V} s' := by
    let s : LocallyConstant V A := s'
    intro z hz
    let W : Opens X := ⟨Subtype.val '' (s ⁻¹' {s ⟨z, hz⟩}),
      V.isOpen.isOpenMap_subtype_val _ (s.isLocallyConstant.isOpen_fiber _)⟩
    have hWV : W ≤ V := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    refine ⟨W, homOfLE hWV, ⟨s ⟨z, hz⟩, ?_⟩, ⟨⟨z, hz⟩, rfl, rfl⟩⟩
    refine LocallyConstant.ext fun ⟨y, hy⟩ => ?_
    obtain ⟨y', hy', rfl⟩ := hy
    exact hy'.symm

/-- The comparison map from the constant sheaf of abelian groups `A_X` to the sheaf of locally
constant maps, induced by the inclusion of constant maps. -/
noncomputable def constantSheafToLocallyConstantSheafAb :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of A) ⟶
      locallyConstantSheafAb X A :=
  Sheaf.homEquiv.symm (sheafifyLift _ (constToLocallyConstantPresheafAb X A)
    (isSheaf_locallyConstantPresheafAb X A))

@[reassoc (attr := simp)]
lemma toSheafify_comp_constantSheafToLocallyConstantSheafAb_hom :
    toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A)) ≫
        (constantSheafToLocallyConstantSheafAb X A).hom =
      constToLocallyConstantPresheafAb X A :=
  toSheafify_sheafifyLift _ _ _

instance : IsIso (constantSheafToLocallyConstantSheafAb X A) := by
  refine (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso _).1 ?_
  have fac := toSheafify_comp_constantSheafToLocallyConstantSheafAb_hom X A
  have hi := isLocallyInjective_constToLocallyConstantPresheafAb X A
  have hs := isLocallySurjective_constToLocallyConstantPresheafAb X A
  have ht := ((Opens.grothendieckTopology X).W_toSheafify
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))).isLocallySurjective
  exact ⟨@Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      _ _ (Opens.grothendieckTopology X) _ _ _ _ _ _ _ _ _ _ _ _ fac hi ht,
    @Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      _ _ (Opens.grothendieckTopology X) _ _ _ _ _ _ _ _ _ _ _ _ fac hs⟩

/-- The constant sheaf of abelian groups `A_X` on a topological space `X` is the sheaf of locally
constant maps: `A_X(V) = LocallyConstant V A` with pointwise addition, and restriction of maps. -/
@[weil "def_fk111_space_constant_sheaf"]
noncomputable def constantSheafAbIsoLocallyConstantSheafAb :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of A) ≅
      locallyConstantSheafAb X A :=
  asIso (constantSheafToLocallyConstantSheafAb X A)

/-- The sections of the constant sheaf of abelian groups `A_X` over `V` are the locally constant
maps `V → A`, with pointwise addition. -/
noncomputable def constantSheafAbSectionsAddEquiv (V : Opens X) :
    ToType (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).obj.obj (op V)) ≃+ LocallyConstant V A :=
  (((sheafToPresheaf _ _).mapIso (constantSheafAbIsoLocallyConstantSheafAb X A)).app
    (op V)).addCommGroupIsoToAddEquiv

/-- Under `constantSheafAbSectionsAddEquiv`, the section of `A_X` given by `a : A` is the
constant map with value `a`. -/
@[simp]
lemma constantSheafAbSectionsAddEquiv_toSheafify (V : Opens X) (a : A) :
    constantSheafAbSectionsAddEquiv X A V
        ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))).app (op V) a) =
      LocallyConstant.const V a :=
  congr($(toSheafify_comp_constantSheafToLocallyConstantSheafAb_hom X A).app (op V) a)

/-- `constantSheafAbSectionsAddEquiv` is compatible with restriction. -/
lemma constantSheafAbSectionsAddEquiv_map {V W : Opens X} (h : W ≤ V)
    (s : ToType (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).obj.obj (op V))) :
    constantSheafAbSectionsAddEquiv X A W
        (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of A)).obj.map (homOfLE h).op s) =
      (constantSheafAbSectionsAddEquiv X A V s).comap ⟨_, continuous_inclusion h⟩ :=
  congr($((constantSheafToLocallyConstantSheafAb X A).hom.naturality (homOfLE h).op) s)

end AddCommGroup

end TopCat
