module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.LTorsionProjectiveSystem
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Transition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.UnderlyingTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ZModConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ZModForgetConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct

/-!
# `l`-adic sheaves

Let `X` be a Noetherian scheme and `l` a prime. Following Freitag–Kiehl, an object
`F = (F_n, u_n)_{n ∈ ℤ}` of the category `P_X` of projective systems of `l`-torsion sheaves on the
small étale site of `X` is an *`l`-adic sheaf* if every `F_n` is constructible, `F_n = 0` for
`n < 0`, `l^{n+1} F_n = 0` for `n ≥ 0`, and for every `n ≥ 0` the transition map
`u_{n+1} : F_{n+1} ⟶ F_n` induces an isomorphism `F_{n+1} ⊗ Λ_n = F_{n+1}/l^{n+1}F_{n+1} ≅ F_n`,
where `Λ_n = ℤ/l^{n+1}ℤ`.

The library's `l`-adic sheaves are those of Stacks, Tag 03UM,
`AlgebraicGeometry.SmallEtale.LAdicSheaf`: `ℕ`-indexed systems of constructible sheaves of
`Λ_n`-modules whose transition maps induce isomorphisms after reduction of scalars. Forgetting the
module structures and extending by zero in negative degrees turns such a system into an object of
`P_X`; this file shows that this identifies `AlgebraicGeometry.SmallEtale.LAdicSheaf` with the full
subcategory of `P_X` of the `l`-adic sheaves in the sense above.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsLAdicSheaf`: the `l`-adic sheaves among the objects of `P_X`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.toLTorsionProjectiveSystem`: the projective system of
  `l`-torsion sheaves underlying an `l`-adic sheaf, as a fully faithful functor into `P_X`.
* `AlgebraicGeometry.SmallEtale.lAdicSheafEquivIsLAdicSheaf`: the equivalence between
  `AlgebraicGeometry.SmallEtale.LAdicSheaf` and the full subcategory of `P_X` of the `l`-adic
  sheaves.
* `CategoryTheory.Functor.extendByZero`: extension by zero of an `ℕ`-indexed inverse system to a
  `ℤ`-indexed one, a fully faithful functor.

## Main results

* `AlgebraicGeometry.SmallEtale.isLAdicSheaf_iff_mem_essImage`: an object of `P_X` is an `l`-adic
  sheaf if and only if it is isomorphic to the projective system underlying an
  `AlgebraicGeometry.SmallEtale.LAdicSheaf`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.isLAdicSheaf_toLTorsionProjectiveSystem_obj` and
  `AlgebraicGeometry.SmallEtale.IsLAdicSheaf.toLTorsionProjectiveSystemObjIso`: the two directions.

## Implementation notes

The condition `l^{n+1} F_n = 0` is what makes `F_n` a sheaf of `Λ_n`-modules, uniquely, and every
morphism of abelian sheaves between such sheaves is `Λ_n`-linear; this is why forgetting the module
structures is fully faithful. The isomorphism `F_{n+1} ⊗_{Λ_{n+1}} Λ_n ≅ F_n` is stated in `P_X` as
the condition that `u_{n+1}` is a cokernel of multiplication by `l^{n+1}` on `F_{n+1}`.
Constructible sheaves of `Λ_n`-modules and constructible abelian sheaves killed by `l^{n+1}`
correspond (Stacks, Tag 03RW, parts (2) and (3)).

The site is the small étale site `AlgebraicGeometry.SmallEtale` of `X` inside a big étale site, and
the sheaves take values in the universe `u + 1` in which the levels of
`AlgebraicGeometry.SmallEtale.LAdicSheaf` live.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The objects of the sequence `0, G₀, G₁, …` obtained by putting a zero object in front of a
sequence `G`. -/
def zeroConsObj (G : ℕᵒᵖ ⥤ C) : ℕ → C
  | 0 => 0
  | k + 1 => G.obj (op k)

/-- The transition maps of the sequence `0, G₀, G₁, …`. -/
def zeroConsMap (G : ℕᵒᵖ ⥤ C) : ∀ k, zeroConsObj G (k + 1) ⟶ zeroConsObj G k
  | 0 => 0
  | k + 1 => G.map (homOfLE (Nat.le_add_right k 1)).op

/-- The inverse system `0 ← G₀ ← G₁ ← ⋯` obtained by putting a zero object in front of `G`. -/
def zeroCons (G : ℕᵒᵖ ⥤ C) : ℕᵒᵖ ⥤ C := ofOpSequence (zeroConsMap G)

theorem zeroCons_map_homOfLE_succ (G : ℕᵒᵖ ⥤ C) (k : ℕ) :
    (zeroCons G).map (homOfLE (Nat.le_add_right k 1)).op = zeroConsMap G k :=
  ofOpSequence_map_homOfLE_succ _ k

theorem isZero_zeroCons_obj_zero (G : ℕᵒᵖ ⥤ C) : IsZero ((zeroCons G).obj (op 0)) :=
  isZero_zero C

theorem zeroCons_map_succ (G : ℕᵒᵖ ⥤ C) {a b : ℕ} (h : a ≤ b) :
    (zeroCons G).map (homOfLE (Nat.succ_le_succ h)).op = G.map (homOfLE h).op := by
  induction b, h using Nat.le_induction with
  | base => exact ((zeroCons G).map_id _).trans (G.map_id _).symm
  | succ b hab ih =>
    have e1 : (homOfLE (Nat.succ_le_succ (hab.trans (Nat.le_succ b))) : a + 1 ⟶ b + 1 + 1) =
        homOfLE (Nat.succ_le_succ hab) ≫ homOfLE (Nat.le_add_right (b + 1) 1) := rfl
    have e2 : (homOfLE (hab.trans (Nat.le_succ b)) : a ⟶ b + 1) =
        homOfLE hab ≫ homOfLE (Nat.le_add_right b 1) := rfl
    rw [e1, e2, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ih,
      zeroCons_map_homOfLE_succ]
    rfl

/-- The components of the map `0 ← G₀ ← ⋯` to `0 ← G'₀ ← ⋯` induced by `η : G ⟶ G'`. -/
def zeroConsApp {G G' : ℕᵒᵖ ⥤ C} (η : G ⟶ G') : ∀ k, zeroConsObj G k ⟶ zeroConsObj G' k
  | 0 => 0
  | k + 1 => η.app (op k)

/-- The map `0 ← G₀ ← ⋯` to `0 ← G'₀ ← ⋯` induced by `η : G ⟶ G'`. -/
def zeroConsHom {G G' : ℕᵒᵖ ⥤ C} (η : G ⟶ G') : zeroCons G ⟶ zeroCons G' :=
  NatTrans.ofOpSequence (zeroConsApp η) (by
    intro k
    cases k with
    | zero =>
      rw [zeroCons_map_homOfLE_succ, zeroCons_map_homOfLE_succ]
      exact (isZero_zero C).eq_of_tgt _ _
    | succ k =>
      rw [zeroCons_map_homOfLE_succ, zeroCons_map_homOfLE_succ]
      exact η.naturality _)

theorem zeroConsHom_app_succ {G G' : ℕᵒᵖ ⥤ C} (η : G ⟶ G') (k : ℕ) :
    (zeroConsHom η).app (op (k + 1)) = η.app (op k) := rfl

/-- Putting a zero object in front of an inverse system, as a functor. -/
def zeroConsFunctor : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C) where
  obj := zeroCons
  map := zeroConsHom
  map_id G := by
    ext ⟨k⟩
    cases k with
    | zero => exact (isZero_zeroCons_obj_zero G).eq_of_src _ _
    | succ k => rfl
  map_comp {G _ _} η θ := by
    ext ⟨k⟩
    cases k with
    | zero => exact (isZero_zeroCons_obj_zero G).eq_of_src _ _
    | succ k => rfl

end CategoryTheory.Functor

namespace Int

/-- The monotone map `n ↦ (n + 1).toNat`, as a functor `ℤ ⥤ ℕ`. -/
def succToNatFunctor : ℤ ⥤ ℕ :=
  Monotone.functor (f := fun n : ℤ ↦ (n + 1).toNat) (fun _ _ h ↦ Int.toNat_le_toNat (by omega))

end Int

namespace Nat

/-- The inclusion `ℕ ⥤ ℤ`. -/
def castFunctor : ℕ ⥤ ℤ :=
  Monotone.functor (f := fun n : ℕ ↦ (n : ℤ)) (fun _ _ h ↦ Int.ofNat_le.mpr h)

end Nat

namespace CategoryTheory.Functor

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- **Extension by zero** of an `ℕ`-indexed inverse system to a `ℤ`-indexed one: the system
`(G_n)_{n ∈ ℤ}` with `G_n = 0` for `n < 0`. -/
def extendByZero : (ℕᵒᵖ ⥤ C) ⥤ (ℤᵒᵖ ⥤ C) :=
  zeroConsFunctor ⋙ (whiskeringLeft _ _ C).obj Int.succToNatFunctor.op

/-- Restriction of a `ℤ`-indexed inverse system to the indices `n ≥ 0`. -/
def restrictNat : (ℤᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C) :=
  (whiskeringLeft _ _ C).obj Nat.castFunctor.op

variable {C}

theorem extendByZero_obj_obj_natCast (G : ℕᵒᵖ ⥤ C) (k : ℕ) :
    ((extendByZero C).obj G).obj (op (k : ℤ)) = G.obj (op k) := rfl

theorem extendByZero_map_natCast (G : ℕᵒᵖ ⥤ C) {a b : ℕ} (h : a ≤ b) :
    ((extendByZero C).obj G).map (homOfLE (Int.ofNat_le.mpr h : (a : ℤ) ≤ b)).op =
      G.map (homOfLE h).op :=
  zeroCons_map_succ G h

theorem extendByZero_map_app_natCast {G G' : ℕᵒᵖ ⥤ C} (η : G ⟶ G') (k : ℕ) :
    ((extendByZero C).map η).app (op (k : ℤ)) = η.app (op k) := rfl

theorem isZero_extendByZero_obj_obj (G : ℕᵒᵖ ⥤ C) {n : ℤ} (hn : n < 0) :
    IsZero (((extendByZero C).obj G).obj (op n)) := by
  have h : (n + 1).toNat = 0 := by omega
  change IsZero ((zeroCons G).obj (op (n + 1).toNat))
  rw [h]
  exact isZero_zeroCons_obj_zero G

/-- Extending by zero and then restricting to the indices `n ≥ 0` gives back the system. -/
def extendByZeroCompRestrictNatIso : extendByZero C ⋙ restrictNat C ≅ 𝟭 (ℕᵒᵖ ⥤ C) :=
  NatIso.ofComponents
    (fun G ↦ NatIso.ofComponents (fun k ↦ Iso.refl (G.obj k)) (by
      rintro ⟨a⟩ ⟨b⟩ f
      have h : b ≤ a := leOfHom f.unop
      have hf : f = (homOfLE h).op := rfl
      rw [hf]
      exact (Category.comp_id _).trans
        ((extendByZero_map_natCast G h).trans (Category.id_comp _).symm)))
    (fun {G G'} η ↦ by
      ext k
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

instance extendByZero_faithful : (extendByZero C).Faithful :=
  Functor.Faithful.of_comp_iso extendByZeroCompRestrictNatIso

/-- The preimage of a map of extended systems: its components at the indices `n ≥ 0`. -/
def extendByZeroPreimage {G G' : ℕᵒᵖ ⥤ C}
    (η : (extendByZero C).obj G ⟶ (extendByZero C).obj G') : G ⟶ G' :=
  NatTrans.ofOpSequence (fun k ↦ η.app (op (k : ℤ))) (fun k ↦ by
    have h := η.naturality (homOfLE (Int.ofNat_le.mpr (Nat.le_add_right k 1))).op
    rwa [extendByZero_map_natCast, extendByZero_map_natCast] at h)

instance extendByZero_full : (extendByZero C).Full where
  map_surjective {G G'} η := by
    refine ⟨extendByZeroPreimage η, ?_⟩
    ext ⟨n⟩
    rcases lt_or_ge n 0 with hn | hn
    · exact (isZero_extendByZero_obj_obj G' hn).eq_of_tgt _ _
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rfl

/-- Extension by zero is fully faithful. -/
def extendByZeroFullyFaithful : (extendByZero C).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- A `ℤ`-indexed system vanishing in negative degrees is the extension by zero of its
restriction to the indices `n ≥ 0`. -/
def extendByZeroRestrictNatIso (Φ : ℤᵒᵖ ⥤ C) (hΦ : ∀ n : ℤ, n < 0 → IsZero (Φ.obj (op n))) :
    (extendByZero C).obj ((restrictNat C).obj Φ) ≅ Φ :=
  NatIso.ofComponents
    (fun n ↦ match n with
      | op (Int.ofNat k) => Iso.refl _
      | op (Int.negSucc k) =>
        (isZero_extendByZero_obj_obj _ (Int.negSucc_lt_zero k)).iso
          (hΦ _ (Int.negSucc_lt_zero k)))
    (by
      rintro ⟨m⟩ ⟨n⟩ f
      rcases lt_or_ge n 0 with hn | hn
      · exact (hΦ n hn).eq_of_tgt _ _
      · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (hn.trans (leOfHom f.unop))
        have hab : a ≤ b := Int.ofNat_le.mp (leOfHom f.unop)
        have hf : f = (homOfLE (Int.ofNat_le.mpr hab)).op := rfl
        rw [hf]
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        exact (Category.comp_id _).trans
          ((extendByZero_map_natCast _ hab).trans (Category.id_comp _).symm))

end CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]

/-- If `r` kills the target of `π`, then `r` times the identity of the source composed with
`π` vanishes. -/
theorem nsmul_id_comp_eq_zero {A Q : C} (π : A ⟶ Q) (r : ℕ) (h : r • 𝟙 Q = 0) :
    (r • 𝟙 A) ≫ π = 0 := by
  rw [Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id π, ← Preadditive.comp_nsmul,
    h, comp_zero]

/-- Being a cokernel of `r` times the identity transports along isomorphisms of the source and
the target. -/
def isColimitCokernelCoforkNsmulOfIso (r : ℕ) {A Q A' Q' : C} {π : A ⟶ Q}
    {w : (r • 𝟙 A) ≫ π = 0} (hπ : IsColimit (CokernelCofork.ofπ π w)) (e : A' ≅ A)
    (e' : Q ≅ Q') (π' : A' ⟶ Q') (hπ' : π' = e.hom ≫ π ≫ e'.hom)
    (w' : (r • 𝟙 A') ≫ π' = 0) : IsColimit (CokernelCofork.ofπ π' w') := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g hg ↦ e'.inv ≫ hπ.desc (CokernelCofork.ofπ (e.inv ≫ g) ?_)) ?_ ?_
  · simp only [Preadditive.nsmul_comp, Category.id_comp] at hg ⊢
    rw [← Preadditive.comp_nsmul, hg, comp_zero]
  · intro Z g hg
    have h := hπ.fac (CokernelCofork.ofπ (e.inv ≫ g) (by
      simp only [Preadditive.nsmul_comp, Category.id_comp] at hg ⊢
      rw [← Preadditive.comp_nsmul, hg, comp_zero])) WalkingParallelPair.one
    simp only [Cofork.ofπ_pt, Cofork.ofπ_ι_app] at h
    rw [hπ', Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, h, Iso.hom_inv_id_assoc]
  · intro Z g hg m hm
    rw [Iso.eq_inv_comp]
    apply Cofork.IsColimit.hom_ext hπ
    have h := hπ.fac (CokernelCofork.ofπ (e.inv ≫ g) (by
      simp only [Preadditive.nsmul_comp, Category.id_comp] at hg ⊢
      rw [← Preadditive.comp_nsmul, hg, comp_zero])) WalkingParallelPair.one
    simp only [Cofork.ofπ_pt, Cofork.ofπ_ι_app] at h
    simp only [Cofork.π_ofπ]
    rw [h, ← hm, hπ']
    simp

/-- Being a cokernel cofork depends on the morphism only through its value. -/
def isColimitCokernelCoforkOfMorphismEq {A B Q : C} {f f' : A ⟶ B} (hf : f = f') {π : B ⟶ Q}
    {w : f ≫ π = 0} (w' : f' ≫ π = 0) (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ π w') := by
  subst hf
  exact h

/-- Being killed by `r` is invariant under isomorphism. -/
private theorem nsmul_id_eq_zero_of_iso {A A' : C} (e : A ≅ A') {r : ℕ} (h : r • 𝟙 A = 0) :
    r • 𝟙 A' = 0 := by
  have : r • 𝟙 A' = e.inv ≫ (r • 𝟙 A) ≫ e.hom := by
    simp
  rw [this, h, zero_comp, comp_zero]

/-- A morphism between the targets of two cokernels of the same morphism, compatible with the
projections, is an isomorphism. -/
theorem isIso_of_isColimit_cokernelCofork {A B Q Q' : C} {f : A ⟶ B} {π : B ⟶ Q} {π' : B ⟶ Q'}
    {w : f ≫ π = 0} {w' : f ≫ π' = 0} (hπ : IsColimit (CokernelCofork.ofπ π w))
    (hπ' : IsColimit (CokernelCofork.ofπ π' w')) (φ : Q ⟶ Q') (hφ : π ≫ φ = π') : IsIso φ := by
  have hψ := hπ'.fac (CokernelCofork.ofπ π w) WalkingParallelPair.one
  simp only [Cofork.ofπ_pt, Cofork.ofπ_ι_app] at hψ
  refine ⟨hπ'.desc (CokernelCofork.ofπ π w), ?_, ?_⟩
  · apply Cofork.IsColimit.hom_ext hπ
    simp only [Cofork.π_ofπ]
    rw [← Category.assoc, hφ, hψ]; exact (Category.comp_id _).symm
  · apply Cofork.IsColimit.hom_ext hπ'
    simp only [Cofork.π_ofπ]
    rw [← Category.assoc, hψ, hφ]; exact (Category.comp_id _).symm

end CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

section Predicate

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (l : ℕ)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{w}]

/-- **`l`-adic sheaves** as objects of the category `P_X` of projective systems of `l`-torsion
sheaves. An object `F = (F_n, u_n)_{n ∈ ℤ}` of `P_X` is an `l`-adic sheaf if every `F_n` is
constructible, `F_n = 0` for `n < 0`, `l^{n+1} F_n = 0` for `n ≥ 0`, and for every `n ≥ 0` the
transition map `u_{n+1} : F_{n+1} ⟶ F_n` induces an isomorphism
`F_{n+1}/l^{n+1}F_{n+1} ≅ F_n`, i.e. exhibits `F_n` as the cokernel of `l^{n+1}` on `F_{n+1}`. -/
@[weil "def_fk112_l_adic_sheaf"]
structure IsLAdicSheaf (F : LTorsionProjectiveSystem.{w} B X.obj X.property l) : Prop where
  /-- Every member `F_n` is constructible. -/
  isConstructible (n : ℤ) : IsConstructibleAbelianSheaf B X (F.obj.obj (op n))
  /-- `F_n = 0` for `n < 0`. -/
  isZero_of_neg (n : ℤ) (hn : n < 0) : IsZero (F.obj.obj (op n))
  /-- `l^{n+1} F_n = 0` for `n ≥ 0`. -/
  nsmul_id_eq_zero (n : ℕ) : (l ^ (n + 1)) • 𝟙 (F.obj.obj (op (n : ℤ))) = 0
  /-- The transition map `F_{n+1} ⟶ F_n` exhibits `F_n` as `F_{n+1}/l^{n+1}F_{n+1}`. -/
  isColimit (n : ℕ) : Nonempty (IsColimit (CokernelCofork.ofπ
    (F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op)
    (nsmul_id_comp_eq_zero _ _ (nsmul_id_eq_zero n))))

end Predicate

section Torsion

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An abelian sheaf killed by a power of `l` is an `l`-torsion sheaf. -/
theorem isLTorsionSheaf_of_pow_nsmul_id_eq_zero {l v : ℕ}
    {F : Sheaf (topology B S hS) AddCommGrpCat.{w}} (h : (l ^ v) • 𝟙 F = 0) :
    IsLTorsionSheaf.{w} B S hS l F := by
  intro U x
  refine ⟨⊤, (topology B S hS).top_mem U, fun V f _ ↦ ⟨v, ?_⟩⟩
  have := congrArg (fun g : F ⟶ F ↦ (g.hom.app (op V)).hom (F.obj.map f.op x)) h
  simpa [abelianSheaf_nsmul_app] using this

/-- A zero abelian sheaf is an `l`-torsion sheaf. -/
theorem isLTorsionSheaf_of_isZero {l : ℕ} {F : Sheaf (topology B S hS) AddCommGrpCat.{w}}
    (h : IsZero F) : IsLTorsionSheaf.{w} B S hS l F :=
  isLTorsionSheaf_of_pow_nsmul_id_eq_zero (v := 0) (h.eq_of_src _ _)

end Torsion

section Embedding

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (l : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))]
variable [Fact l.Prime] [IsNoetherian X.obj]

omit [Fact l.Prime] [IsNoetherian X.obj] in
/-- The underlying abelian sheaf of a sheaf of `ℤ/l^{n+1}ℤ`-modules is killed by `l^{n+1}`. -/
theorem nsmul_id_underlyingLevelFunctor_obj (n : ℕ) (M : FiniteLevelSheaf.{u, u + 1} B X l n) :
    (l ^ (n + 1)) • 𝟙 ((underlyingLevelFunctor B X l n).obj M) = 0 := by
  have := underlyingLevelFunctor_additive B X l n
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul, zmodSheaf_nsmul_id,
    CategoryTheory.Functor.map_zero]

namespace LAdicSheaf

/-- The `ℤ`-indexed projective system of abelian sheaves underlying an `l`-adic sheaf: its
member of index `n ≥ 0` is the underlying abelian sheaf of the level `n`, and its members of
negative index are zero. -/
def toProjectiveSystemFunctor : LAdicSheaf.{u, u + 1} B X l ⥤
    (ℤᵒᵖ ⥤ Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
  LAdicSheaf.underlyingLAdicFunctor B X l ⋙ Functor.extendByZero _

theorem toProjectiveSystemFunctor_obj_obj_natCast (F : LAdicSheaf.{u, u + 1} B X l) (n : ℕ) :
    ((toProjectiveSystemFunctor B X l).obj F).obj (op (n : ℤ)) =
      (underlyingLevelFunctor B X l n).obj (F.level n) := rfl

theorem toProjectiveSystemFunctor_obj_map_succ (F : LAdicSheaf.{u, u + 1} B X l) (n : ℕ) :
    ((toProjectiveSystemFunctor B X l).obj F).map
        (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op =
      (underlyingLevelFunctor B X l (n + 1)).map (F.transition n) := by
  refine (Functor.extendByZero_map_natCast (LAdicSheaf.underlyingLAdicTower B X l F)
    (Nat.le_add_right n 1)).trans ?_
  exact Functor.ofOpSequence_map_homOfLE_succ _ n

theorem toProjectiveSystemFunctor_map_app_natCast {F G : LAdicSheaf.{u, u + 1} B X l}
    (f : F ⟶ G) (n : ℕ) :
    ((toProjectiveSystemFunctor B X l).map f).app (op (n : ℤ)) =
      (underlyingLevelFunctor B X l n).map (f.app n) := rfl

theorem isZero_toProjectiveSystemFunctor_obj_obj (F : LAdicSheaf.{u, u + 1} B X l) {n : ℤ}
    (hn : n < 0) : IsZero (((toProjectiveSystemFunctor B X l).obj F).obj (op n)) :=
  Functor.isZero_extendByZero_obj_obj _ hn

theorem nsmul_id_toProjectiveSystemFunctor_obj_obj (F : LAdicSheaf.{u, u + 1} B X l) (n : ℕ) :
    (l ^ (n + 1)) • 𝟙 (((toProjectiveSystemFunctor B X l).obj F).obj (op (n : ℤ))) = 0 :=
  nsmul_id_underlyingLevelFunctor_obj B X l n (F.level n)

theorem isLTorsionSheaf_toProjectiveSystemFunctor_obj_obj (F : LAdicSheaf.{u, u + 1} B X l)
    (n : ℤ) : IsLTorsionSheaf.{u + 1} B X.obj X.property l
      (((toProjectiveSystemFunctor B X l).obj F).obj (op n)) := by
  rcases lt_or_ge n 0 with hn | hn
  · exact isLTorsionSheaf_of_isZero (isZero_toProjectiveSystemFunctor_obj_obj B X l F hn)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact isLTorsionSheaf_of_pow_nsmul_id_eq_zero
      (nsmul_id_toProjectiveSystemFunctor_obj_obj B X l F k)

/-- **An `l`-adic sheaf as an object of `P_X`.** The functor sending an `l`-adic sheaf
`(F_n)_{n ≥ 0}` to the projective system of `l`-torsion sheaves `(F_n, u_n)_{n ∈ ℤ}` of its
underlying abelian sheaves, with `F_n = 0` for `n < 0`. -/
@[weil "def_fk112_l_adic_sheaf"]
def toLTorsionProjectiveSystem :
    LAdicSheaf.{u, u + 1} B X l ⥤ LTorsionProjectiveSystem.{u + 1} B X.obj X.property l :=
  ObjectProperty.lift _ (toProjectiveSystemFunctor B X l) (fun F ↦
    ⟨isLTorsionSheaf_toProjectiveSystemFunctor_obj_obj B X l F,
      0, fun _ hn ↦ isZero_toProjectiveSystemFunctor_obj_obj B X l F hn⟩)

instance toProjectiveSystemFunctor_faithful : (toProjectiveSystemFunctor B X l).Faithful := by
  have := Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdicFunctor_faithful B X l
  exact Functor.Faithful.comp _ _

instance toProjectiveSystemFunctor_full : (toProjectiveSystemFunctor B X l).Full := by
  have := Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdicFunctor_full B X l
  exact Functor.Full.comp _ _

instance toLTorsionProjectiveSystem_faithful : (toLTorsionProjectiveSystem B X l).Faithful :=
  Functor.Faithful.of_comp_iso (G := ObjectProperty.ι _)
    (Iso.refl (toProjectiveSystemFunctor B X l))

instance toLTorsionProjectiveSystem_full : (toLTorsionProjectiveSystem B X l).Full :=
  Functor.Full.of_comp_faithful_iso (G := ObjectProperty.ι _)
    (Iso.refl (toProjectiveSystemFunctor B X l))

/-- The embedding of `l`-adic sheaves into `P_X` is fully faithful: morphisms of `l`-adic
sheaves are exactly the morphisms of the underlying projective systems. -/
def toLTorsionProjectiveSystemFullyFaithful : (toLTorsionProjectiveSystem B X l).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

theorem neZero_pow (n : ℕ) : NeZero (l ^ (n + 1)) :=
  ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

include l in
omit [IsNoetherian X.obj] in
/-- A zero abelian sheaf is constructible. -/
theorem isConstructibleAbelianSheaf_of_isZero
    {F : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1}} (hF : IsZero F) :
    IsConstructibleAbelianSheaf B X F := by
  have := neZero_pow l 0
  have h0 : IsConstructibleModuleSheaf B X (ZMod (l ^ (0 + 1)))
      (0 : FiniteLevelSheaf.{u, u + 1} B X l 0) := by
    have := isWeakSerreClass_constructible B X l 0
    exact ObjectProperty.prop_zero _
  have h1 := isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_zmod.{u, 0} B
    (l ^ (0 + 1)) X _ h0
  have := underlyingLevelFunctor_additive B X l 0
  exact isConstructibleFiniteSheaf_congr B X
    (((underlyingLevelFunctor B X l 0).map_isZero (isZero_zero _)).iso hF) h1

/-- **An `l`-adic sheaf is an `l`-adic sheaf in the sense of `P_X`**: the projective system
underlying an `l`-adic sheaf has constructible members, vanishes in negative degrees, has
`l^{n+1}F_n = 0`, and its transition maps induce `F_{n+1}/l^{n+1}F_{n+1} ≅ F_n`. -/
theorem isLAdicSheaf_toLTorsionProjectiveSystem_obj (F : LAdicSheaf.{u, u + 1} B X l) :
    IsLAdicSheaf B X l ((toLTorsionProjectiveSystem B X l).obj F) where
  isConstructible n := by
    rcases lt_or_ge n 0 with hn | hn
    · exact isConstructibleAbelianSheaf_of_isZero B X l
        (isZero_toProjectiveSystemFunctor_obj_obj B X l F hn)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      have := neZero_pow l k
      exact isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_zmod.{u, 0} B
        (l ^ (k + 1)) X (F.level k) (F.constructible k)
  isZero_of_neg n hn := isZero_toProjectiveSystemFunctor_obj_obj B X l F hn
  nsmul_id_eq_zero n := nsmul_id_toProjectiveSystemFunctor_obj_obj B X l F n
  isColimit n := by
    let G := underlyingLevelFunctor B X l (n + 1)
    have := underlyingLevelFunctor_additive B X l (n + 1)
    have := underlyingLevelFunctor_isLeftAdjoint B X l (n + 1)
    have hc := CokernelCofork.mapIsColimit _
      (Stacks.EtaleCohomology.LAdicSheaf.transition_isCokernel F n) G
    have hc' := isColimitCokernelCoforkOfMorphismEq (w := (CokernelCofork.ofπ _
        (Stacks.EtaleCohomology.LAdicSheaf.transition_condition F n)).map_condition G)
      (show G.map ((l ^ (n + 1)) • 𝟙 (F.level (n + 1))) = (l ^ (n + 1)) • 𝟙 (G.obj _) by
        rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id])
      (nsmul_id_comp_eq_zero _ _ (nsmul_id_toProjectiveSystemFunctor_obj_obj B X l F n)) hc
    have hπ : ((toLTorsionProjectiveSystem B X l).obj F).obj.map
        (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op = G.map (F.transition n) :=
      toProjectiveSystemFunctor_obj_map_succ B X l F n
    exact ⟨isColimitCokernelCoforkNsmulOfIso _ hc' (Iso.refl _) (Iso.refl _) _
      (by rw [hπ, Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl) _⟩

end LAdicSheaf

namespace IsLAdicSheaf

variable {B X l} {F : LTorsionProjectiveSystem.{u + 1} B X.obj X.property l}

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))] [Fact l.Prime] [IsNoetherian X.obj] in
/-- The sections of the member `F_n` of an `l`-adic sheaf are killed by `l^{n+1}`. -/
theorem pow_nsmul_eq_zero (hF : IsLAdicSheaf B X l F) (n : ℕ)
    (U : (SmallEtale B X.obj X.property)ᵒᵖ) (x : (F.obj.obj (op (n : ℤ))).obj.obj U) :
    (l ^ (n + 1)) • x = 0 := by
  have := congrArg (fun g ↦ (g.hom.app U).hom x) (hF.nsmul_id_eq_zero n)
  simpa [abelianSheaf_nsmul_app] using this

/-- The level `n` of the `l`-adic sheaf attached to an `l`-adic object of `P_X`: the member
`F_n`, as a sheaf of `ℤ/l^{n+1}ℤ`-modules. -/
def level (hF : IsLAdicSheaf B X l F) (n : ℕ) : FiniteLevelSheaf.{u, u + 1} B X l n :=
  zmodSheafOfAnnihilated.{u + 1, u + 1, u} (topology B X.obj X.property) (l ^ (n + 1))
    (F.obj.obj (op (n : ℤ)))
    (hF.pow_nsmul_eq_zero n)

/-- The underlying abelian sheaf of `IsLAdicSheaf.level` is the member `F_n`. -/
def levelIso (hF : IsLAdicSheaf B X l F) (n : ℕ) :
    (underlyingLevelFunctor B X l n).obj (hF.level n) ≅ F.obj.obj (op (n : ℤ)) :=
  zmodSheafOfAnnihilatedIso.{u + 1, u + 1, u} (topology B X.obj X.property) (l ^ (n + 1)) _
    (hF.pow_nsmul_eq_zero n)

/-- The transition maps of the `l`-adic sheaf attached to an `l`-adic object of `P_X`. -/
def transition (hF : IsLAdicSheaf B X l F) (n : ℕ) :
    hF.level (n + 1) ⟶ (hF.level n).restrictScalars B X l n :=
  have := underlyingLevelFunctor_full B X l (n + 1)
  (underlyingLevelFunctor B X l (n + 1)).preimage
    ((hF.levelIso (n + 1)).hom ≫ F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op ≫
      (hF.levelIso n).inv)

omit [Fact l.Prime] [IsNoetherian X.obj] in
theorem map_transition (hF : IsLAdicSheaf B X l F) (n : ℕ) :
    (underlyingLevelFunctor B X l (n + 1)).map (hF.transition n) =
      (hF.levelIso (n + 1)).hom ≫ F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op ≫
        (hF.levelIso n).inv := by
  have := underlyingLevelFunctor_full B X l (n + 1)
  exact (underlyingLevelFunctor B X l (n + 1)).map_preimage _

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))] [Fact l.Prime] [IsNoetherian X.obj] in
theorem isConstructibleModuleSheaf_level (hF : IsLAdicSheaf B X l F) (n : ℕ) :
    IsConstructibleModuleSheaf B X (ZMod (l ^ (n + 1))) (hF.level n) :=
  isConstructibleModuleSheaf_zmod_of_isConstructibleAbelianSheaf.{u, 0} B (l ^ (n + 1)) X
    (hF.level n) (isConstructibleFiniteSheaf_congr B X (hF.levelIso n).symm
      (hF.isConstructible n))

omit [Fact l.Prime] [IsNoetherian X.obj] in
theorem isIso_scalarReductionMap_transition (hF : IsLAdicSheaf B X l F) (n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X l n (hF.level (n + 1)) (hF.level n)
      (hF.transition n)) := by
  let r := FiniteLevelSheaf.scalarReductionMap B X l n (hF.level (n + 1)) (hF.level n)
    (hF.transition n)
  let adj := scalarAdjunction B X l n
  let G := underlyingLevelFunctor B X l (n + 1)
  have := underlyingLevelFunctor_additive B X l (n + 1)
  have := underlyingLevelFunctor_isLeftAdjoint B X l (n + 1)
  have ht : hF.transition n =
      adj.unit.app (hF.level (n + 1)) ≫ (restrictScalarsFunctor B X l n).map r :=
    (FiniteLevelSheaf.scalarReductionMap_comp B X l n _ _ _).symm.trans
      (adj.homEquiv_unit _ _ r)
  have hG : G.map ((l ^ (n + 1)) • 𝟙 (hF.level (n + 1))) = (l ^ (n + 1)) • 𝟙 (G.obj _) := by
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  -- the image of the unit of the scalar adjunction is a cokernel of `l^{n+1}`
  have h₁ := isColimitCokernelCoforkOfMorphismEq hG (w := (CokernelCofork.ofπ _
      (scalarAdjunction_unit_condition B X l n (hF.level (n + 1)))).map_condition G)
    (by rw [← hG]; exact (CokernelCofork.ofπ _
      (scalarAdjunction_unit_condition B X l n (hF.level (n + 1)))).map_condition G)
    (CokernelCofork.mapIsColimit _ (scalarAdjunction_unit_isCokernel B X l n _) G)
  -- the image of the transition map is a cokernel of `l^{n+1}`, by hypothesis
  obtain ⟨hc⟩ := hF.isColimit n
  have h₂ := isColimitCokernelCoforkNsmulOfIso _ hc (hF.levelIso (n + 1)) (hF.levelIso n).symm
    (G.map (hF.transition n)) (by rw [map_transition]; rfl)
    (nsmul_id_comp_eq_zero _ _ (nsmul_id_underlyingLevelFunctor_obj B X l n (hF.level n)))
  have hφ : G.map (adj.unit.app (hF.level (n + 1))) ≫
      G.map ((restrictScalarsFunctor B X l n).map r) = G.map (hF.transition n) := by
    rw [← CategoryTheory.Functor.map_comp, ← ht]
  have hiso := isIso_of_isColimit_cokernelCofork h₁ h₂ _ hφ
  have := underlyingLevelFunctor_full B X l n
  have : IsIso ((underlyingLevelFunctor B X l n).map r) := hiso
  exact isIso_of_fully_faithful (underlyingLevelFunctor B X l n) r

/-- The `l`-adic sheaf attached to an `l`-adic object of `P_X`: its levels are the members
`F_n`, `n ≥ 0`, as sheaves of `ℤ/l^{n+1}ℤ`-modules. -/
def toLAdicSheaf (hF : IsLAdicSheaf B X l F) : LAdicSheaf.{u, u + 1} B X l where
  level := hF.level
  constructible := hF.isConstructibleModuleSheaf_level
  transition := hF.transition
  reduction_isIso := hF.isIso_scalarReductionMap_transition

/-- The comparison of the underlying tower of `IsLAdicSheaf.toLAdicSheaf` with the restriction
of `F` to the indices `n ≥ 0`. -/
def underlyingLAdicTowerHom (hF : IsLAdicSheaf B X l F) :
    LAdicSheaf.underlyingLAdicTower B X l hF.toLAdicSheaf ⟶ (Functor.restrictNat _).obj F.obj :=
  NatTrans.ofOpSequence (fun k ↦ (hF.levelIso k).hom) (fun k ↦ by
    simp only [LAdicSheaf.underlyingLAdicTower, Functor.ofOpSequence_map_homOfLE_succ]
    change (underlyingLevelFunctor B X l (k + 1)).map (hF.transition k) ≫ _ = _
    rw [map_transition]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

instance isIso_underlyingLAdicTowerHom (hF : IsLAdicSheaf B X l F) :
    IsIso hF.underlyingLAdicTowerHom := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro k
  exact (hF.levelIso k.unop).isIso_hom

/-- The underlying tower of `IsLAdicSheaf.toLAdicSheaf` is the restriction of `F` to the
indices `n ≥ 0`. -/
def underlyingLAdicTowerIso (hF : IsLAdicSheaf B X l F) :
    LAdicSheaf.underlyingLAdicTower B X l hF.toLAdicSheaf ≅
      (Functor.restrictNat _).obj F.obj :=
  asIso hF.underlyingLAdicTowerHom

/-- **Every `l`-adic object of `P_X` comes from an `l`-adic sheaf.** -/
def toLTorsionProjectiveSystemObjIso (hF : IsLAdicSheaf B X l F) :
    (LAdicSheaf.toLTorsionProjectiveSystem B X l).obj hF.toLAdicSheaf ≅ F :=
  ObjectProperty.isoMk _ ((Functor.extendByZero _).mapIso hF.underlyingLAdicTowerIso ≪≫
    Functor.extendByZeroRestrictNatIso F.obj hF.isZero_of_neg)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{u + 1} (ZMod (l ^ (n + 1))))] [Fact l.Prime] [IsNoetherian X.obj] in
/-- Being an `l`-adic object of `P_X` is invariant under isomorphism. -/
theorem of_iso {F' : LTorsionProjectiveSystem.{u + 1} B X.obj X.property l} (e : F ≅ F')
    (hF : IsLAdicSheaf B X l F) : IsLAdicSheaf B X l F' where
  isConstructible n := isConstructibleFiniteSheaf_congr B X
    ((ObjectProperty.ι _ ⋙ (evaluation _ _).obj (op n)).mapIso e) (hF.isConstructible n)
  isZero_of_neg n hn := (hF.isZero_of_neg n hn).of_iso
    ((ObjectProperty.ι _ ⋙ (evaluation _ _).obj (op n)).mapIso e).symm
  nsmul_id_eq_zero n := nsmul_id_eq_zero_of_iso
    ((ObjectProperty.ι _ ⋙ (evaluation _ _).obj (op (n : ℤ))).mapIso e) (hF.nsmul_id_eq_zero n)
  isColimit n := by
    obtain ⟨hc⟩ := hF.isColimit n
    let ev (m : ℤ) : LTorsionProjectiveSystem.{u + 1} B X.obj X.property l ⥤
        Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
      ObjectProperty.ι _ ⋙ (evaluation _ _).obj (op m)
    refine ⟨isColimitCokernelCoforkNsmulOfIso _ hc ((ev _).mapIso e).symm ((ev _).mapIso e) _
      ?_ _⟩
    have h₁ := congrArg (fun φ ↦ φ.hom.app (op (n : ℤ))) e.inv_hom_id
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at h₁
    change _ = e.inv.hom.app _ ≫ F.obj.map _ ≫ e.hom.hom.app _
    rw [← Category.assoc, ← e.inv.hom.naturality, Category.assoc, h₁, Category.comp_id]

end IsLAdicSheaf

instance isClosedUnderIsomorphisms_isLAdicSheaf :
    ObjectProperty.IsClosedUnderIsomorphisms (IsLAdicSheaf.{u + 1} B X l) :=
  ⟨fun e hF ↦ hF.of_iso e⟩

/-- **`l`-adic sheaves of `P_X` are exactly the `l`-adic sheaves.** An object of `P_X` is an
`l`-adic sheaf in the sense of `IsLAdicSheaf` if and only if it is isomorphic to the underlying
projective system of an `l`-adic sheaf `AlgebraicGeometry.SmallEtale.LAdicSheaf`. -/
@[weil "def_fk112_l_adic_sheaf"]
theorem isLAdicSheaf_iff_mem_essImage (F : LTorsionProjectiveSystem.{u + 1} B X.obj X.property l) :
    IsLAdicSheaf B X l F ↔ (LAdicSheaf.toLTorsionProjectiveSystem B X l).essImage F :=
  ⟨fun hF ↦ ⟨hF.toLAdicSheaf, ⟨hF.toLTorsionProjectiveSystemObjIso⟩⟩,
    fun ⟨G, ⟨e⟩⟩ ↦ (LAdicSheaf.isLAdicSheaf_toLTorsionProjectiveSystem_obj B X l G).of_iso e⟩

/-- The embedding of `l`-adic sheaves into the full subcategory of `P_X` of the objects
satisfying `IsLAdicSheaf`. -/
def LAdicSheaf.toIsLAdicSheaf :
    LAdicSheaf.{u, u + 1} B X l ⥤ ObjectProperty.FullSubcategory (IsLAdicSheaf.{u + 1} B X l) :=
  ObjectProperty.lift _ (LAdicSheaf.toLTorsionProjectiveSystem B X l)
    (LAdicSheaf.isLAdicSheaf_toLTorsionProjectiveSystem_obj B X l)

instance : (LAdicSheaf.toIsLAdicSheaf B X l).Faithful :=
  Functor.Faithful.of_comp_iso (G := ObjectProperty.ι _)
    (Iso.refl (LAdicSheaf.toLTorsionProjectiveSystem B X l))

instance : (LAdicSheaf.toIsLAdicSheaf B X l).Full :=
  Functor.Full.of_comp_faithful_iso (G := ObjectProperty.ι _)
    (Iso.refl (LAdicSheaf.toLTorsionProjectiveSystem B X l))

instance : (LAdicSheaf.toIsLAdicSheaf B X l).EssSurj where
  mem_essImage F := ⟨F.property.toLAdicSheaf,
    ⟨ObjectProperty.isoMk _ F.property.toLTorsionProjectiveSystemObjIso⟩⟩

instance : (LAdicSheaf.toIsLAdicSheaf B X l).IsEquivalence where

/-- **The category of `l`-adic sheaves is the full subcategory of `P_X` of the `l`-adic
sheaves**: `AlgebraicGeometry.SmallEtale.LAdicSheaf` is equivalent to the full subcategory of
the projective systems of `l`-torsion sheaves satisfying `IsLAdicSheaf`. -/
@[weil "def_fk112_l_adic_sheaf"]
def lAdicSheafEquivIsLAdicSheaf :
    LAdicSheaf.{u, u + 1} B X l ≌ ObjectProperty.FullSubcategory (IsLAdicSheaf.{u + 1} B X l) :=
  (LAdicSheaf.toIsLAdicSheaf B X l).asEquivalence

end Embedding

end AlgebraicGeometry.SmallEtale
