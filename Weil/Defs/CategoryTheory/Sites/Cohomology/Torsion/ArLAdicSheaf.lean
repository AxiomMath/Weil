module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.LAdicSheaves
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.ArCategorySheaves
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# A–R `l`-adic sheaves

Let `X` be a scheme, `P_X` the category of projective systems of `l`-torsion sheaves on the small
étale site of `X`, and `AR_X` its Artin–Rees category. An object `F` of `P_X` is an
*A–R `l`-adic sheaf* if it is isomorphic in `AR_X` to an `l`-adic sheaf: there are an object `G`
of `P_X` which is an `l`-adic sheaf and an isomorphism `F ≅ G` of `AR_X`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.toAr`: the canonical functor
  `P_X ⥤ AR_X`, the identity on objects, sending `f : F ⟶ G` to the class `[0, f ∘ ε_0^F]`.
* `AlgebraicGeometry.SmallEtale.IsArLAdicSheaf`: the A–R `l`-adic sheaves, as a property of the
  objects of the A–R category `AR_X`.

## Main results

* `AlgebraicGeometry.SmallEtale.IsLAdicSheaf.isArLAdicSheaf`: an `l`-adic sheaf is an A–R `l`-adic
  sheaf.
* `AlgebraicGeometry.SmallEtale.IsArLAdicSheaf.isClosedUnderIsomorphisms`: being an A–R `l`-adic
  sheaf is invariant under isomorphisms of `AR_X`; `IsArLAdicSheaf.of_iso` for isomorphisms of
  `P_X`.
* `AlgebraicGeometry.SmallEtale.isArLAdicSheaf_iff_exists_lAdicSheaf`: `F` is an A–R `l`-adic
  sheaf if and only if it is isomorphic in `AR_X` to the projective system underlying an `l`-adic
  sheaf `AlgebraicGeometry.SmallEtale.LAdicSheaf` (Stacks, Tag 03UM).

## Implementation notes

The predicate is stated on the objects of the A–R category, as an `ObjectProperty`, so that the
full subcategory of the A–R `l`-adic sheaves is `ObjectProperty.FullSubcategory IsArLAdicSheaf`;
an object `F` of `P_X` is A–R `l`-adic when `IsArLAdicSheaf (ArLTorsionProjectiveSystem.of F)`
holds (`isArLAdicSheaf_of_iff`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

namespace LTorsionProjectiveSystem

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (l : ℕ)

/-- The canonical functor from the category `P_S` of projective systems of `l`-torsion sheaves
to its A–R category `AR_S`: the identity on objects, sending `f : F ⟶ G` to the class
`[0, f ∘ ε_0^F]`. -/
def toAr : LTorsionProjectiveSystem.{w} B S hS l ⥤ ArLTorsionProjectiveSystem.{w} B S hS l where
  obj F := .of F
  map {F G} f :=
    ArLTorsionProjectiveSystem.homMk (F := F) (G := G) 0 ((shiftι B S hS l 0).app F ≫ f)
  map_id F := by
    rw [ArLTorsionProjectiveSystem.id_eq]
    exact congrArg _ (Category.comp_id _)
  map_comp {F G H} f g := by
    change _ = ArLTorsionProjectiveSystem.homMk (F := F) (G := G) 0 _ ≫
      ArLTorsionProjectiveSystem.homMk (F := G) (G := H) 0 _
    rw [ArLTorsionProjectiveSystem.homMk_comp_homMk, Functor.map_comp, Category.assoc,
      shiftι_naturality_assoc, shiftShift_comp_shift_map_shiftι_zero_assoc]
    exact (ArLTorsionProjectiveSystem.homMk_shiftMap_comp (Nat.le_add_left 0 0) _).symm

variable {B S hS l}

@[simp]
lemma toAr_obj (F : LTorsionProjectiveSystem.{w} B S hS l) :
    (toAr B S hS l).obj F = ArLTorsionProjectiveSystem.of F :=
  rfl

lemma toAr_map {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G) :
    (toAr B S hS l).map f =
      ArLTorsionProjectiveSystem.homMk (F := F) (G := G) 0 ((shiftι B S hS l 0).app F ≫ f) :=
  rfl

end LTorsionProjectiveSystem

section Predicate

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (l : ℕ)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{w}]

/-- **A–R `l`-adic sheaves.** An object `F` of the A–R category `AR_X` of projective systems of
`l`-torsion sheaves on the small étale site of `X` is an *A–R `l`-adic sheaf* if it is isomorphic
in `AR_X` to an `l`-adic sheaf: there is an object `G` of `P_X` which is an `l`-adic sheaf
(`AlgebraicGeometry.SmallEtale.IsLAdicSheaf`) with `F ≅ G` in `AR_X`. -/
@[weil "def_fk112_ar_l_adic_sheaf"]
def IsArLAdicSheaf : ObjectProperty (ArLTorsionProjectiveSystem.{w} B X.obj X.property l) :=
  fun F ↦ ∃ G : LTorsionProjectiveSystem.{w} B X.obj X.property l,
    IsLAdicSheaf B X l G ∧ Nonempty (F ≅ ArLTorsionProjectiveSystem.of G)

variable {B X l}

lemma isArLAdicSheaf_iff (F : ArLTorsionProjectiveSystem.{w} B X.obj X.property l) :
    IsArLAdicSheaf B X l F ↔ ∃ G : LTorsionProjectiveSystem.{w} B X.obj X.property l,
      IsLAdicSheaf B X l G ∧ Nonempty (F ≅ ArLTorsionProjectiveSystem.of G) :=
  Iff.rfl

/-- An object `F` of `P_X` is an A–R `l`-adic sheaf if and only if it is isomorphic in `AR_X` to
an `l`-adic sheaf. -/
lemma isArLAdicSheaf_of_iff (F : LTorsionProjectiveSystem.{w} B X.obj X.property l) :
    IsArLAdicSheaf B X l (ArLTorsionProjectiveSystem.of F) ↔
      ∃ G : LTorsionProjectiveSystem.{w} B X.obj X.property l, IsLAdicSheaf B X l G ∧
        Nonempty (ArLTorsionProjectiveSystem.of F ≅ ArLTorsionProjectiveSystem.of G) :=
  Iff.rfl

/-- An object of `AR_X` isomorphic to an `l`-adic sheaf is an A–R `l`-adic sheaf. -/
lemma IsLAdicSheaf.isArLAdicSheaf_of_iso
    {F : ArLTorsionProjectiveSystem.{w} B X.obj X.property l}
    {G : LTorsionProjectiveSystem.{w} B X.obj X.property l}
    (e : F ≅ ArLTorsionProjectiveSystem.of G) (hG : IsLAdicSheaf B X l G) :
    IsArLAdicSheaf B X l F :=
  ⟨G, hG, ⟨e⟩⟩

/-- An `l`-adic sheaf is an A–R `l`-adic sheaf. -/
lemma IsLAdicSheaf.isArLAdicSheaf {G : LTorsionProjectiveSystem.{w} B X.obj X.property l}
    (hG : IsLAdicSheaf B X l G) : IsArLAdicSheaf B X l (ArLTorsionProjectiveSystem.of G) :=
  hG.isArLAdicSheaf_of_iso (Iso.refl _)

namespace IsArLAdicSheaf

variable {F F' : ArLTorsionProjectiveSystem.{w} B X.obj X.property l}

/-- An `l`-adic sheaf isomorphic in `AR_X` to an A–R `l`-adic sheaf `F`. -/
def lAdicSheaf (hF : IsArLAdicSheaf B X l F) : LTorsionProjectiveSystem.{w} B X.obj X.property l :=
  hF.choose

lemma isLAdicSheaf_lAdicSheaf (hF : IsArLAdicSheaf B X l F) :
    IsLAdicSheaf B X l hF.lAdicSheaf :=
  hF.choose_spec.1

/-- The isomorphism `F ≅ hF.lAdicSheaf` of `AR_X`. -/
def arIso (hF : IsArLAdicSheaf B X l F) : F ≅ ArLTorsionProjectiveSystem.of hF.lAdicSheaf :=
  hF.choose_spec.2.some

instance isClosedUnderIsomorphisms :
    (IsArLAdicSheaf.{w} B X l).IsClosedUnderIsomorphisms where
  of_iso e hF := hF.isLAdicSheaf_lAdicSheaf.isArLAdicSheaf_of_iso (e.symm ≪≫ hF.arIso)

/-- Being an A–R `l`-adic sheaf is invariant under isomorphisms of `AR_X`. -/
lemma of_arIso (e : F ≅ F') (hF : IsArLAdicSheaf B X l F) : IsArLAdicSheaf B X l F' :=
  ObjectProperty.prop_of_iso _ e hF

/-- Being an A–R `l`-adic sheaf is invariant under isomorphisms of `P_X`. -/
lemma of_iso {G G' : LTorsionProjectiveSystem.{w} B X.obj X.property l} (e : G ≅ G')
    (hG : IsArLAdicSheaf B X l (ArLTorsionProjectiveSystem.of G)) :
    IsArLAdicSheaf B X l (ArLTorsionProjectiveSystem.of G') :=
  of_arIso ((LTorsionProjectiveSystem.toAr B X.obj X.property l).mapIso e) hG

end IsArLAdicSheaf

/-- Objects isomorphic in `AR_X` are simultaneously A–R `l`-adic sheaves. -/
lemma isArLAdicSheaf_congr {F F' : ArLTorsionProjectiveSystem.{w} B X.obj X.property l}
    (e : F ≅ F') : IsArLAdicSheaf B X l F ↔ IsArLAdicSheaf B X l F' :=
  ObjectProperty.prop_iff_of_iso _ e

end Predicate

section Embedding

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {l : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))]
  [Fact l.Prime] [IsNoetherian X.obj]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **A–R `l`-adic sheaves via the `l`-adic sheaves of Stacks.** An object `F` of `AR_X` is an
A–R `l`-adic sheaf if and only if it is isomorphic in `AR_X` to the projective system of
`l`-torsion sheaves underlying an `l`-adic sheaf `AlgebraicGeometry.SmallEtale.LAdicSheaf`. -/
@[weil "def_fk112_ar_l_adic_sheaf"]
theorem isArLAdicSheaf_iff_exists_lAdicSheaf
    (F : ArLTorsionProjectiveSystem.{u + 1} B X.obj X.property l) :
    IsArLAdicSheaf B X l F ↔ ∃ G : LAdicSheaf.{u, u + 1} B X l,
      Nonempty (F ≅ ArLTorsionProjectiveSystem.of
        ((LAdicSheaf.toLTorsionProjectiveSystem B X l).obj G)) := by
  constructor
  · rintro ⟨G, hG, ⟨e⟩⟩
    obtain ⟨G', ⟨e'⟩⟩ := (isLAdicSheaf_iff_mem_essImage B X l G).1 hG
    exact ⟨G', ⟨e ≪≫ (LTorsionProjectiveSystem.toAr B X.obj X.property l).mapIso e'.symm⟩⟩
  · rintro ⟨G, ⟨e⟩⟩
    exact (LAdicSheaf.isLAdicSheaf_toLTorsionProjectiveSystem_obj B X l G).isArLAdicSheaf_of_iso e

end Embedding

end AlgebraicGeometry.SmallEtale

end
