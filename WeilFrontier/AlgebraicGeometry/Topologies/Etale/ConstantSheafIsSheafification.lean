module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import WeilFrontier.CategoryTheory.Sites.IsSheafFor

/-!
# The constant sheaf is the sheafification of the constant presheaf

Let `F` be a set (resp. an abelian group). On the étale category `Et(S)` of noetherian separated
étale `S`-schemes, the constant presheaf `C_F` (value `F`, all restriction maps the identity)
maps to the presheaf `F_S` of locally constant maps `|U| → F` by sending `a ∈ F` to the
constant map with value `a`. Since `F_S` is a sheaf, this morphism `c` induces a morphism from
the sheafification `Ĉ_F` to `F_S`; it is an isomorphism.

The morphism `c` is locally injective: two elements of `F` whose constant maps agree on `U`
are equal as soon as `U` has a point, and the empty scheme is covered by the empty family. It is
locally surjective: a locally constant map `k` on `U` is constant on an affine open
neighbourhood of every point, and these neighbourhoods are objects of `Et(S)` covering `U`.
A locally bijective morphism into a sheaf is a sheafification.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.constToLocallyConstantPresheaf` — the
  morphism `c : C_F ⟶ F_S` of presheaves of sets, and `constToLocallyConstantPresheafAb` its
  version for abelian groups.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isSheaf_locallyConstantPresheaf` and
  `isSheaf_locallyConstantPresheafAb` — `F_S` is a sheaf for the topology of `Et(S)`.
* `isIso_sheafifyLift_constToLocallyConstantPresheaf` (in the namespace
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale`) — the morphism `Ĉ_F ⟶ F_S` induced by `c`
  is an isomorphism (sets), and
  `isIso_sheafifyLift_constToLocallyConstantPresheafAb` the same for abelian groups.

## Implementation notes

The topology of `Et(S)` is `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology`, whose
covering sieves contain the jointly surjective ones. The sheafification is Mathlib's
`CategoryTheory.sheafify`, and the induced morphism is `CategoryTheory.sheafifyLift`. The
results are stated for coefficients in any universe in which the sheafification exists and
identifies the morphisms inverted by it with the locally bijective ones
(`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`); since `Et(S)` has objects in
`Type (u + 1)`, Mathlib provides both for `Type (u + 1)` and `AddCommGrpCat.{u + 1}`. As in
FK, the base `S` is assumed (locally) noetherian, which makes the covering sieves of `Et(S)`
exactly the jointly surjective ones.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Open neighbourhoods in `Et(S)` -/

/-- Every open neighbourhood `O` of a point `x` of an object `U` of `Et(S)` contains the image
of a morphism of `Et(S)` (an affine open immersion) whose image contains `x`. -/
theorem exists_hom_mem_range_subset (U : SmallNoetherianSeparatedEtale B S hS)
    {x : (toScheme B S hS).obj U} {O : ((toScheme B S hS).obj U).Opens} (hx : x ∈ O) :
    ∃ (V : SmallNoetherianSeparatedEtale B S hS) (f : V ⟶ U),
      x ∈ Set.range ((toScheme B S hS).map f) ∧
        Set.range ((toScheme B S hS).map f) ⊆ (O : Set ((toScheme B S hS).obj U)) := by
  obtain ⟨R, j, _, hj, hjO⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ structureMorphism U)).trans_lt hS
  have : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian j
  have : IsNoetherian (Spec R) := {}
  exact ⟨mk (Spec R) hR (j ≫ structureMorphism U),
    ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk j) rfl)),
    hj, hjO⟩

/-! ### `F_S` is a sheaf for the topology of `Et(S)` -/

/-- The presheaf of sets `F_S` is a sheaf for the topology of `Et(S)`. -/
theorem isSheaf_locallyConstantPresheaf [IsLocallyNoetherian S] (F : Type w) :
    Presheaf.IsSheaf (topology B S hS) (locallyConstantPresheaf B S hS F) :=
  (isSheaf_iff_isSheaf_of_type _ _).mpr fun _ _ hR ↦
    locallyConstantPresheaf_isSheafFor F _ (((mem_topology_iff B S hS _).mp hR))

/-- The presheaf of abelian groups `F_S` is a sheaf for the topology of `Et(S)`. -/
theorem isSheaf_locallyConstantPresheafAb [IsLocallyNoetherian S] (F : Type w) [AddCommGroup F] :
    Presheaf.IsSheaf (topology B S hS) (locallyConstantPresheafAb B S hS F) :=
  (Presheaf.isSheaf_iff_isSheaf_forget_addCommGrpCat _ _).mpr fun _ _ hR ↦
    locallyConstantPresheafAb_isSheafFor F _ (((mem_topology_iff B S hS _).mp hR))

/-! ### The morphism `c : C_F ⟶ F_S` -/

variable (B S hS) in
/-- **The morphism `c : C_F ⟶ F_S`** for a set `F`: it sends `a ∈ F = C_F(U)` to the constant
map `|U| → F` with value `a`. -/
@[weil "lem_fk102_constant_sheaf_is_sheafification"]
def constToLocallyConstantPresheaf (F : Type (max u w)) :
    (Functor.const (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ).obj F ⟶
      locallyConstantPresheaf.{max u w} B S hS F where
  app _ := TypeCat.ofHom fun a ↦ LocallyConstant.const _ a
  naturality _ _ _ := rfl

@[simp]
lemma constToLocallyConstantPresheaf_app_apply (F : Type (max u w))
    (U : (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ) (a : F) (x : (toScheme B S hS).obj U.unop) :
    (show LocallyConstant ((toScheme B S hS).obj U.unop) F from
      (constToLocallyConstantPresheaf B S hS F).app U a) x = a :=
  rfl

variable (B S hS) in
/-- **The morphism `c : C_F ⟶ F_S`** for an abelian group `F`: it sends `a ∈ F = C_F(U)` to the
constant map `|U| → F` with value `a`. -/
@[weil "lem_fk102_constant_sheaf_is_sheafification"]
def constToLocallyConstantPresheafAb (F : Type (max u w)) [AddCommGroup F] :
    (Functor.const (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of F) ⟶
      locallyConstantPresheafAb.{max u w} B S hS F where
  app _ := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom)
  naturality _ _ _ := rfl

@[simp]
lemma constToLocallyConstantPresheafAb_app_apply (F : Type (max u w)) [AddCommGroup F]
    (U : (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ) (a : F) (x : (toScheme B S hS).obj U.unop) :
    (show LocallyConstant ((toScheme B S hS).obj U.unop) F from
      (constToLocallyConstantPresheafAb B S hS F).app U a) x = a :=
  rfl

/-! ### `c` is locally bijective -/

/-- The morphism `c : C_F ⟶ F_S` is locally injective. -/
theorem isLocallyInjective_constToLocallyConstantPresheaf
    [IsLocallyNoetherian S] (F : Type (max u w)) :
    Presheaf.IsLocallyInjective (topology B S hS) (constToLocallyConstantPresheaf B S hS F) where
  equalizerSieve_mem {U} a b hab := by
    refine (mem_topology_iff B S hS _).mpr fun x ↦ ⟨U.unop, 𝟙 _, ?_, x, by simp⟩
    have : a = b := congrArg (fun k : LocallyConstant ((toScheme B S hS).obj U.unop) F ↦ k x) hab
    subst this
    simp [Presheaf.equalizerSieve]

/-- The morphism `c : C_F ⟶ F_S` is locally surjective. -/
theorem isLocallySurjective_constToLocallyConstantPresheaf
    [IsLocallyNoetherian S] (F : Type (max u w)) :
    Presheaf.IsLocallySurjective (topology B S hS)
      (constToLocallyConstantPresheaf B S hS F) where
  imageSieve_mem {U} k := by
    let k₀ : LocallyConstant ((toScheme B S hS).obj U) F := k
    refine (mem_topology_iff B S hS _).mpr fun x ↦ ?_
    let O : ((toScheme B S hS).obj U).Opens :=
      ⟨k₀ ⁻¹' {k₀ x}, k₀.isLocallyConstant.isOpen_fiber _⟩
    obtain ⟨V, f, hx, hfO⟩ := exists_hom_mem_range_subset U (O := O) rfl
    refine ⟨V, f, ⟨k₀ x, ?_⟩, hx⟩
    apply LocallyConstant.ext
    intro y
    exact (hfO ⟨y, rfl⟩).symm

/-- The morphism `c : C_F ⟶ F_S` of presheaves of abelian groups is locally injective. -/
theorem isLocallyInjective_constToLocallyConstantPresheafAb
    [IsLocallyNoetherian S] (F : Type (max u w))
    [AddCommGroup F] :
    Presheaf.IsLocallyInjective (topology B S hS)
      (constToLocallyConstantPresheafAb B S hS F) where
  equalizerSieve_mem {U} a b hab := by
    refine (mem_topology_iff B S hS _).mpr fun x ↦ ⟨U.unop, 𝟙 _, ?_, x, by simp⟩
    have : a = b := congrArg (fun k : LocallyConstant ((toScheme B S hS).obj U.unop) F ↦ k x) hab
    subst this
    simp [Presheaf.equalizerSieve]

/-- The morphism `c : C_F ⟶ F_S` of presheaves of abelian groups is locally surjective. -/
theorem isLocallySurjective_constToLocallyConstantPresheafAb
    [IsLocallyNoetherian S] (F : Type (max u w))
    [AddCommGroup F] :
    Presheaf.IsLocallySurjective (topology B S hS)
      (constToLocallyConstantPresheafAb B S hS F) where
  imageSieve_mem {U} k := by
    let k₀ : LocallyConstant ((toScheme B S hS).obj U) F := k
    refine (mem_topology_iff B S hS _).mpr fun x ↦ ?_
    let O : ((toScheme B S hS).obj U).Opens :=
      ⟨k₀ ⁻¹' {k₀ x}, k₀.isLocallyConstant.isOpen_fiber _⟩
    obtain ⟨V, f, hx, hfO⟩ := exists_hom_mem_range_subset U (O := O) rfl
    refine ⟨V, f, ⟨k₀ x, ?_⟩, hx⟩
    apply LocallyConstant.ext
    intro y
    exact (hfO ⟨y, rfl⟩).symm

/-! ### The sheafification of `C_F` is `F_S` -/

/-- A locally bijective morphism `c : P ⟶ Q` into a sheaf `Q` induces an isomorphism from the
sheafification of `P` to `Q`. -/
theorem isIso_sheafifyLift_of_isLocallyInjective_of_isLocallySurjective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasWeakSheafify J A]
    [J.WEqualsLocallyBijective A] {P Q : Cᵒᵖ ⥤ A} (c : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (hinj : Presheaf.IsLocallyInjective J c) (hsurj : Presheaf.IsLocallySurjective J c) :
    IsIso (sheafifyLift J c hQ) := by
  have hW : J.W c := (J.W_iff_isLocallyBijective c).mpr ⟨hinj, hsurj⟩
  have : IsIso ((presheafToSheaf J A).map c) := by rwa [← J.W_iff]
  have : IsIso (sheafifyMap J c) :=
    (sheafToPresheaf J A).map_isIso ((presheafToSheaf J A).map c)
  have : IsIso (sheafifyLift J (𝟙 Q) hQ) :=
    ⟨⟨toSheafify J Q, sheafifyLift_id_toSheafify hQ, toSheafify_sheafifyLift J (𝟙 Q) hQ⟩⟩
  rw [← Category.comp_id c, ← sheafifyMap_sheafifyLift]
  infer_instance

/-- **The constant sheaf is the sheafification of the constant presheaf** (sets). For a set `F`,
the morphism from the sheafification `Ĉ_F` of the constant presheaf to the sheaf `F_S` of
locally constant maps induced by `c : C_F ⟶ F_S` is an isomorphism. -/
@[weil "lem_fk102_constant_sheaf_is_sheafification"]
theorem isIso_sheafifyLift_constToLocallyConstantPresheaf
    [IsLocallyNoetherian S] (F : Type (max u w))
    [HasWeakSheafify (topology B S hS) (Type (max u w))]
    [(topology B S hS).WEqualsLocallyBijective (Type (max u w))] :
    IsIso (sheafifyLift (topology B S hS) (constToLocallyConstantPresheaf B S hS F)
      (isSheaf_locallyConstantPresheaf F)) :=
  isIso_sheafifyLift_of_isLocallyInjective_of_isLocallySurjective _ _
    (isLocallyInjective_constToLocallyConstantPresheaf F)
    (isLocallySurjective_constToLocallyConstantPresheaf F)

/-- **The constant sheaf is the sheafification of the constant presheaf** (abelian groups). For
an abelian group `F`, the morphism from the sheafification `Ĉ_F` of the constant presheaf to the
sheaf `F_S` of locally constant maps induced by `c : C_F ⟶ F_S` is an isomorphism. -/
@[weil "lem_fk102_constant_sheaf_is_sheafification"]
theorem isIso_sheafifyLift_constToLocallyConstantPresheafAb
    [IsLocallyNoetherian S] (F : Type (max u w))
    [AddCommGroup F] [HasWeakSheafify (topology B S hS) AddCommGrpCat.{max u w}]
    [(topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{max u w}] :
    IsIso (sheafifyLift (topology B S hS) (constToLocallyConstantPresheafAb B S hS F)
      (isSheaf_locallyConstantPresheafAb F)) :=
  isIso_sheafifyLift_of_isLocallyInjective_of_isLocallySurjective _ _
    (isLocallyInjective_constToLocallyConstantPresheafAb F)
    (isLocallySurjective_constToLocallyConstantPresheafAb F)

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
