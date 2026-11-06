module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ArHom
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# The Artin–Rees category of projective systems

Let `𝒫` be the category of projective systems `(F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion
`Λ`-modules. The *Artin–Rees category* (A–R category) has the objects of `𝒫`, and its morphisms
from `F` to `G` are the A–R morphisms `Hom_AR(F, G)`, the classes `[r, f]` of pairs `(r, f)` with
`r ≥ 0` and `f : F[r] ⟶ G`. On representatives, the composite of `(r, f) : F → G` and
`(s, g) : G → H` is `(r + s, g ∘ f[s])`, where `f[s] : F[r + s] ⟶ G[s]`; the identity of `F` is
`[0, id_F]`; and the sum of `(r, f)` and `(s, g)` is
`(t, f ∘ ε^{t-r}_{F[r]} + g ∘ ε^{t-s}_{F[s]})` with `t = max r s`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.ArCategory Λ l`: the A–R category, whose objects are the
  projective systems.
* `CategoryTheory.ProjectiveSystem.ArCategory.category`: its category structure, with the
  composition and identities above.
* `CategoryTheory.ProjectiveSystem.ArCategory.preadditive`: its preadditive structure, with the
  sum above.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk r f`: the A–R morphism `[r, f]`.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_comp_homMk`: `[r, f] ≫ [s, g]` is
  `[r + s, g ∘ f[s]]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.id_eq`: the identity of `F` is `[0, ε⁰_F]`, the
  class of the identity of `F` under `F[0] = F`.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_add_homMk`: `[r, f] + [s, g]` is
  `[t, f ∘ ε^{t-r}_{F[r]} + g ∘ ε^{t-s}_{F[s]}]` for every `t ≥ max r s`, in particular for
  `t = max r s`.
* `CategoryTheory.ProjectiveSystem.ArHom.comp_mk_mk`,
  `CategoryTheory.ProjectiveSystem.ArHom.mk_add_mk`: the same formulas on `ArHom`, which shows
  in particular that they do not depend on the representatives.

## Implementation notes

The shifted system `F[r][s]` has terms `F_{n+s+r}`, only propositionally equal to the terms
`F_{n+(r+s)}` of `F[r+s]`. The morphism `f[s] : F[r+s] ⟶ G[s]` of the source is therefore the
composite of the canonical identification `ProjectiveSystem.shiftShift F r s : F[r+s] ⟶ F[r][s]`
with `(shift s).map f : F[r][s] ⟶ G[s]`. Likewise `F[0]` is not `F`, and the identity is the class
of `ε⁰_F = natMap F 0 : F[0] ⟶ F`, the canonical identification. The maps `ε^{t-r}_{F[r]}` in the
sum are `ProjectiveSystem.shiftMap F (r ≤ t) : F[t] ⟶ F[r]` (`shiftMap_app_eq`).

The objects are wrapped in a structure, so that the category structure of the A–R category is not
confused with the one of `𝒫` on the same type.

The A–R category is also the Serre quotient of `𝒫` by the null systems; the comparison of the two
is a separate result.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

/-- For `r s ≥ 0`, the natural transformation `translate (r + s) ⟶ translate s ⋙ translate r`
of `ℤᵒᵖ`, whose component at `n` is the morphism `op (n + (r + s)) ⟶ op (n + s + r)`. -/
def translateAddHom (r s : ℕ) :
    translate ((r + s : ℕ) : ℤ) ⟶ translate (s : ℤ) ⋙ translate (r : ℤ) where
  app n := (homOfLE (show n.unop + s + r ≤ n.unop + ((r + s : ℕ) : ℤ) by push_cast; omega)).op
  naturality _ _ _ := Subsingleton.elim _ _

section Thin

variable {C : Type*} [Category C] (P : ℤᵒᵖ ⥤ C)

/-- Any two composites of images of morphisms of the thin category `ℤᵒᵖ` with the same source and
target agree. -/
private lemma map_comp_map_eq_map {X Y Z : ℤᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) :
    P.map a ≫ P.map b = P.map c :=
  (P.map_comp a b).symm.trans (congrArg P.map (Subsingleton.elim _ _))

private lemma map_comp_map_eq_map_comp_map {X Y Y' Z : ℤᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X ⟶ Y')
    (b' : Y' ⟶ Z) : P.map a ≫ P.map b = P.map a' ≫ P.map b' :=
  (map_comp_map_eq_map P a b (a ≫ b)).trans (map_comp_map_eq_map P a' b' (a ≫ b)).symm

private lemma map_comp_map_eq_map_comp_map_comp_map {X Y Y' Y'' Z : ℤᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z)
    (a' : X ⟶ Y') (b' : Y' ⟶ Y'') (c' : Y'' ⟶ Z) :
    P.map a ≫ P.map b = P.map a' ≫ P.map b' ≫ P.map c' := by
  rw [map_comp_map_eq_map P b' c' (b' ≫ c')]
  exact map_comp_map_eq_map_comp_map P _ _ _ _

end Thin

variable {Λ : Type u} [CommRing Λ] {l : Λ}

instance (r : ℤ) : (shift.{v} (Λ := Λ) (l := l) r).Additive where
  map_add := hom_ext fun _ => rfl

/-- The canonical identification `F[r + s] ⟶ F[r][s]`: its component `F_{n+(r+s)} ⟶ F_{n+s+r}`
is the map of `F` along the equality `n + s + r = n + (r + s)`. -/
def shiftShift (F : ProjectiveSystem.{v} Λ l) (r s : ℕ) :
    (shift ((r + s : ℕ) : ℤ)).obj F ⟶ (shift (s : ℤ)).obj ((shift (r : ℤ)).obj F) :=
  ObjectProperty.homMk (Functor.whiskerRight (translateAddHom r s) F.obj)

lemma shiftShift_app (F : ProjectiveSystem.{v} Λ l) (r s : ℕ) (n : ℤ) :
    app (shiftShift F r s) n =
      F.obj.map (homOfLE (by push_cast; omega : n + s + r ≤ n + (r + s : ℕ))).op := rfl

/-- `F[t + s] ⟶ F[t][s] ⟶ F[r][s]` equals `F[t + s] ⟶ F[r + s] ⟶ F[r][s]`. -/
@[reassoc]
lemma shiftShift_comp_shift_map_shiftMap (F : ProjectiveSystem.{v} Λ l) {r t : ℕ} (h : r ≤ t)
    (s : ℕ) :
    shiftShift F t s ≫ (shift (s : ℤ)).map (shiftMap F h) =
      shiftMap F (Nat.add_le_add_right h s) ≫ shiftShift F r s :=
  hom_ext fun n => by
    simp only [comp_app, shift_map_app, shiftShift_app, shiftMap_app]
    exact map_comp_map_eq_map_comp_map F.obj _ _ _ _

/-- `F[r + t] ⟶ F[r][t] ⟶ F[r][s]` equals `F[r + t] ⟶ F[r + s] ⟶ F[r][s]`. -/
@[reassoc]
lemma shiftShift_comp_shiftMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) {s t : ℕ} (h : s ≤ t) :
    shiftShift F r t ≫ shiftMap ((shift (r : ℤ)).obj F) h =
      shiftMap F (Nat.add_le_add_left h r) ≫ shiftShift F r s :=
  hom_ext fun n => by
    simp only [comp_app, shiftShift_app, shiftMap_app]
    exact map_comp_map_eq_map_comp_map F.obj _ _ _ _

@[reassoc]
lemma shiftShift_comp_shift_map_natMap_zero (F : ProjectiveSystem.{v} Λ l) (s : ℕ) :
    shiftShift F 0 s ≫ (shift (s : ℤ)).map (natMap F 0) =
      shiftMap F (Nat.le_add_left s 0) :=
  hom_ext fun n => by
    simp only [comp_app, shift_map_app, shiftShift_app, shiftMap_app, natMap_app]
    exact map_comp_map_eq_map F.obj _ _ _

@[reassoc]
lemma shiftShift_comp_natMap_zero (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    shiftShift F r 0 ≫ natMap ((shift (r : ℤ)).obj F) 0 = shiftMap F (Nat.le_add_right r 0) :=
  hom_ext fun n => by
    simp only [comp_app, shiftShift_app, shiftMap_app, natMap_app]
    exact map_comp_map_eq_map F.obj _ _ _

/-- The identification `F[r + s] ⟶ F[r][s]` is natural in `F`. -/
@[reassoc]
lemma shiftShift_naturality {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (r s : ℕ) :
    (shift ((r + s : ℕ) : ℤ)).map f ≫ shiftShift G r s =
      shiftShift F r s ≫ (shift (s : ℤ)).map ((shift (r : ℤ)).map f) :=
  hom_ext fun _ => (f.hom.naturality _).symm

@[reassoc]
lemma shiftShift_comp_shift_map_shiftShift (F : ProjectiveSystem.{v} Λ l) (r s u : ℕ) :
    shiftShift F (r + s) u ≫ (shift (u : ℤ)).map (shiftShift F r s) =
      shiftMap F (le_of_eq (Nat.add_assoc r s u).symm) ≫ shiftShift F r (s + u) ≫
        shiftShift ((shift (r : ℤ)).obj F) s u :=
  hom_ext fun n => by
    simp only [comp_app, shift_map_app, shiftShift_app, shiftMap_app]
    exact map_comp_map_eq_map_comp_map_comp_map F.obj _ _ _ _ _

namespace ArHom

variable {F G H : ProjectiveSystem.{v} Λ l}

/-- A function on pairs `(r, f)` that is unchanged when `(r, f)` is replaced by
`(t, f ∘ (F[t] ⟶ F[r]))` respects the relation `≈`. -/
lemma rel_of_shiftMap {X : Sort*} (Φ : (Σ r : ℕ, (shift (r : ℤ)).obj F ⟶ G) → X)
    (hΦ : ∀ (r t : ℕ) (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G),
      Φ ⟨t, shiftMap F h ≫ f⟩ = Φ ⟨r, f⟩) :
    ∀ a b, Rel F G a b → Φ a = Φ b := by
  rintro ⟨r, f⟩ ⟨s, g⟩ ⟨t, hr, hs, e⟩
  rw [← hΦ r t hr f, ← hΦ s t hs g, e]

/-- A function on A–R morphisms, from a function on pairs `(r, f)` that is unchanged when
`(r, f)` is replaced by `(t, f ∘ (F[t] ⟶ F[r]))`. -/
def lift {X : Sort*} (Φ : (Σ r : ℕ, (shift (r : ℤ)).obj F ⟶ G) → X)
    (hΦ : ∀ (r t : ℕ) (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G),
      Φ ⟨t, shiftMap F h ≫ f⟩ = Φ ⟨r, f⟩) : ArHom F G → X :=
  Quot.lift Φ (rel_of_shiftMap Φ hΦ)

@[simp]
lemma lift_mk {X : Sort*} (Φ : (Σ r : ℕ, (shift (r : ℤ)).obj F ⟶ G) → X) (hΦ)
    (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) : lift Φ hΦ (mk r f) = Φ ⟨r, f⟩ := rfl

/-- `[r, f] = [t, f ∘ (F[t] ⟶ F[r])]` for `t ≥ r`. -/
lemma mk_eq_mk_shiftMap_comp {r : ℕ} (t : ℕ) (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G) :
    mk r f = mk t (shiftMap F h ≫ f) :=
  (mk_shiftMap_comp h f).symm

/-- The representative `g ∘ f[s] : F[r + s] ⟶ H` of the composite of `(r, f)` and `(s, g)`, where
`f[s]` is `F[r + s] ⟶ F[r][s] ⟶ G[s]`. -/
def compRep {r s : ℕ} (f : (shift (r : ℤ)).obj F ⟶ G) (g : (shift (s : ℤ)).obj G ⟶ H) :
    (shift ((r + s : ℕ) : ℤ)).obj F ⟶ H :=
  shiftShift F r s ≫ (shift (s : ℤ)).map f ≫ g

lemma mk_compRep_shiftMap_comp_left {r t s : ℕ} (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G)
    (g : (shift (s : ℤ)).obj G ⟶ H) :
    mk (t + s) (compRep (shiftMap F h ≫ f) g) = mk (r + s) (compRep f g) := by
  rw [← mk_shiftMap_comp (Nat.add_le_add_right h s) (compRep f g)]
  congr 1
  simp only [compRep, Functor.map_comp, Category.assoc, shiftShift_comp_shift_map_shiftMap_assoc]

lemma mk_compRep_shiftMap_comp_right {r s t : ℕ} (h : s ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G)
    (g : (shift (s : ℤ)).obj G ⟶ H) :
    mk (r + t) (compRep f (shiftMap G h ≫ g)) = mk (r + s) (compRep f g) := by
  rw [← mk_shiftMap_comp (Nat.add_le_add_left h r) (compRep f g)]
  congr 1
  rw [compRep, compRep, shiftMap_naturality_assoc, shiftShift_comp_shiftMap_assoc]

/-- The composite of A–R morphisms: on representatives, the composite of `(r, f)` and `(s, g)` is
`(r + s, g ∘ f[s])` (`comp_mk_mk`). -/
def comp (φ : ArHom F G) (ψ : ArHom G H) : ArHom F H :=
  lift (fun p => lift (fun q => mk (p.1 + q.1) (compRep p.2 q.2))
    (fun _ _ h g => mk_compRep_shiftMap_comp_right h p.2 g) ψ)
    (fun _ _ h f => by
      induction ψ using ind with
      | h s g => exact mk_compRep_shiftMap_comp_left h f g) φ

/-- The composite of `[r, f]` and `[s, g]` is `[r + s, g ∘ f[s]]`. -/
lemma comp_mk_mk {r s : ℕ} (f : (shift (r : ℤ)).obj F ⟶ G) (g : (shift (s : ℤ)).obj G ⟶ H) :
    comp (mk r f) (mk s g) = mk (r + s) (shiftShift F r s ≫ (shift (s : ℤ)).map f ≫ g) := rfl

/-- The identity A–R morphism `[0, ε⁰_F]`, the class of the identity of `F` under `F[0] = F`. -/
def id (F : ProjectiveSystem.{v} Λ l) : ArHom F F :=
  mk 0 (natMap F 0)

lemma id_comp (φ : ArHom F G) : comp (id F) φ = φ := by
  induction φ using ind with
  | h s g =>
    rw [id, comp_mk_mk, shiftShift_comp_shift_map_natMap_zero_assoc]
    exact mk_shiftMap_comp _ g

lemma comp_id (φ : ArHom F G) : comp φ (id G) = φ := by
  induction φ using ind with
  | h r f =>
    rw [id, comp_mk_mk, natMap_naturality, shiftShift_comp_natMap_zero_assoc]
    exact mk_shiftMap_comp _ f

lemma comp_assoc {K : ProjectiveSystem.{v} Λ l} (φ : ArHom F G) (ψ : ArHom G H)
    (χ : ArHom H K) : comp (comp φ ψ) χ = comp φ (comp ψ χ) := by
  induction φ using ind with
  | h r f =>
  induction ψ using ind with
  | h s g =>
  induction χ using ind with
  | h u k =>
    simp only [comp_mk_mk]
    refine mk_eq_mk_of_comp_eq (le_refl _) (le_of_eq (Nat.add_assoc r s u).symm) ?_
    simp only [shiftMap_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [shiftShift_naturality_assoc, shiftShift_comp_shift_map_shiftShift_assoc]

/-! ### The additive structure -/

/-- The sum of `[r, f]` and `[s, g]` computed at any `t ≥ max r s` is the same. -/
lemma mk_add_eq_mk_add {r s t t' : ℕ} (hr : r ≤ t) (hs : s ≤ t) (hr' : r ≤ t') (hs' : s ≤ t')
    (f : (shift (r : ℤ)).obj F ⟶ G) (g : (shift (s : ℤ)).obj F ⟶ G) :
    mk t (shiftMap F hr ≫ f + shiftMap F hs ≫ g) =
      mk t' (shiftMap F hr' ≫ f + shiftMap F hs' ≫ g) := by
  refine mk_eq_mk_of_comp_eq (le_max_left t t') (le_max_right t t') ?_
  simp only [Preadditive.comp_add, shiftMap_comp_shiftMap_assoc]

/-- The sum of A–R morphisms: on representatives, the sum of `(r, f)` and `(s, g)` is
`(t, f ∘ ε^{t-r}_{F[r]} + g ∘ ε^{t-s}_{F[s]})` with `t = max r s` (`mk_add_mk`). -/
instance : Add (ArHom F G) where
  add φ ψ := lift (fun p => lift (fun q => mk (max p.1 q.1)
      (shiftMap F (le_max_left p.1 q.1) ≫ p.2 + shiftMap F (le_max_right p.1 q.1) ≫ q.2))
    (fun s t h g => by
      simp only [shiftMap_comp_shiftMap_assoc]
      exact mk_add_eq_mk_add _ _ _ _ _ _) ψ)
    (fun r t h f => by
      induction ψ using ind with
      | h s g =>
        simp only [lift_mk, shiftMap_comp_shiftMap_assoc]
        exact mk_add_eq_mk_add _ _ _ _ _ _) φ

/-- The sum of `[r, f]` and `[s, g]` is `[t, f ∘ ε^{t-r}_{F[r]} + g ∘ ε^{t-s}_{F[s]}]`, for any
`t ≥ max r s`. -/
lemma mk_add_mk {r s : ℕ} (t : ℕ) (hr : r ≤ t) (hs : s ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G)
    (g : (shift (s : ℤ)).obj F ⟶ G) :
    mk r f + mk s g = mk t (shiftMap F hr ≫ f + shiftMap F hs ≫ g) :=
  mk_add_eq_mk_add _ _ _ _ f g

lemma mk_add_mk_same {t : ℕ} (f g : (shift (t : ℤ)).obj F ⟶ G) :
    mk t f + mk t g = mk t (f + g) := by
  rw [mk_add_mk t le_rfl le_rfl, shiftMap_refl, Category.id_comp, Category.id_comp]

instance : Zero (ArHom F G) where
  zero := mk 0 0

lemma zero_eq_mk (t : ℕ) : (0 : ArHom F G) = mk t 0 := by
  change mk 0 0 = _
  rw [mk_eq_mk_shiftMap_comp t (Nat.zero_le t) 0, Limits.comp_zero]

instance : Neg (ArHom F G) where
  neg := lift (fun p => mk p.1 (-p.2)) fun r t h f => by
    change mk t (-(shiftMap F h ≫ f)) = mk r (-f)
    rw [← Preadditive.comp_neg]
    exact mk_shiftMap_comp h (-f)

lemma neg_mk {r : ℕ} (f : (shift (r : ℤ)).obj F ⟶ G) : -mk r f = mk r (-f) := rfl

instance : AddCommGroup (ArHom F G) where
  add_assoc a b c := by
    induction a using ind with
    | h r f =>
    induction b using ind with
    | h s g =>
    induction c using ind with
    | h u k =>
      rw [mk_eq_mk_shiftMap_comp (max (max r s) u) (by omega) f,
        mk_eq_mk_shiftMap_comp (max (max r s) u) (by omega) g,
        mk_eq_mk_shiftMap_comp (max (max r s) u) (by omega) k]
      simp only [mk_add_mk_same, add_assoc]
  zero_add a := by
    induction a using ind with
    | h r f => rw [zero_eq_mk r, mk_add_mk_same, zero_add]
  add_zero a := by
    induction a using ind with
    | h r f => rw [zero_eq_mk r, mk_add_mk_same, add_zero]
  neg_add_cancel a := by
    induction a using ind with
    | h r f => rw [neg_mk, mk_add_mk_same, neg_add_cancel, ← zero_eq_mk]
  add_comm a b := by
    induction a using ind with
    | h r f =>
    induction b using ind with
    | h s g =>
      rw [mk_eq_mk_shiftMap_comp (max r s) (le_max_left r s) f,
        mk_eq_mk_shiftMap_comp (max r s) (le_max_right r s) g, mk_add_mk_same, mk_add_mk_same,
        add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma add_comp (φ φ' : ArHom F G) (ψ : ArHom G H) :
    comp (φ + φ') ψ = comp φ ψ + comp φ' ψ := by
  induction φ using ind with
  | h r f =>
  induction φ' using ind with
  | h r' f' =>
  induction ψ using ind with
  | h s g =>
    rw [mk_eq_mk_shiftMap_comp (max r r') (le_max_left r r') f,
      mk_eq_mk_shiftMap_comp (max r r') (le_max_right r r') f', mk_add_mk_same]
    simp only [comp_mk_mk, mk_add_mk_same, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]

lemma comp_add (φ : ArHom F G) (ψ ψ' : ArHom G H) :
    comp φ (ψ + ψ') = comp φ ψ + comp φ ψ' := by
  induction φ using ind with
  | h r f =>
  induction ψ using ind with
  | h s g =>
  induction ψ' using ind with
  | h s' g' =>
    rw [mk_eq_mk_shiftMap_comp (max s s') (le_max_left s s') g,
      mk_eq_mk_shiftMap_comp (max s s') (le_max_right s s') g', mk_add_mk_same]
    simp only [comp_mk_mk, mk_add_mk_same, Preadditive.comp_add]

end ArHom

/-- The *Artin–Rees category* (A–R category) of projective systems of `l`-power torsion
`Λ`-modules: its objects are the projective systems, and its morphisms from `F` to `G` are the
A–R morphisms `Hom_AR(F, G)` (`ArCategory.category`). -/
@[weil "def_fk112_ar_category"]
structure ArCategory (Λ : Type u) [CommRing Λ] (l : Λ) where
  /-- The A–R category object of a projective system. -/
  of ::
  /-- The projective system underlying an object of the A–R category. -/
  obj : ProjectiveSystem.{v} Λ l

namespace ArCategory

/-- The category structure of the A–R category: morphisms are A–R morphisms, the composite of
`[r, f]` and `[s, g]` is `[r + s, g ∘ f[s]]` (`homMk_comp_homMk`), and the identity of `F` is
`[0, id_F]` (`id_eq`). -/
@[weil "def_fk112_ar_category"]
instance category : Category (ArCategory.{v} Λ l) where
  Hom X Y := ArHom X.obj Y.obj
  id X := ArHom.id X.obj
  comp φ ψ := ArHom.comp φ ψ
  id_comp := ArHom.id_comp
  comp_id := ArHom.comp_id
  assoc := ArHom.comp_assoc

/-- The preadditive structure of the A–R category: the sum of `[r, f]` and `[s, g]` is
`[t, f ∘ ε^{t-r}_{F[r]} + g ∘ ε^{t-s}_{F[s]}]` with `t = max r s` (`homMk_add_homMk`). -/
@[weil "def_fk112_ar_category"]
instance preadditive : Preadditive (ArCategory.{v} Λ l) where
  homGroup X Y := inferInstanceAs (AddCommGroup (ArHom X.obj Y.obj))
  add_comp _ _ _ φ φ' ψ := ArHom.add_comp φ φ' ψ
  comp_add _ _ _ φ ψ ψ' := ArHom.comp_add φ ψ ψ'

/-- The morphism `[r, f] : F ⟶ G` of the A–R category, for `f : F[r] ⟶ G`. -/
def homMk {F G : ProjectiveSystem.{v} Λ l} (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) :
    of F ⟶ of G :=
  ArHom.mk r f

lemma homMk_surjective {F G : ProjectiveSystem.{v} Λ l} (φ : of F ⟶ of G) :
    ∃ (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G), homMk r f = φ :=
  ArHom.mk_surjective φ

@[elab_as_elim]
lemma hom_induction {X Y : ArCategory.{v} Λ l} {motive : (X ⟶ Y) → Prop}
    (h : ∀ (r : ℕ) (f : (shift (r : ℤ)).obj X.obj ⟶ Y.obj), motive (homMk (F := X.obj) r f))
    (φ : X ⟶ Y) : motive φ :=
  ArHom.ind h φ

/-- The composite of `[r, f] : F ⟶ G` and `[s, g] : G ⟶ H` is `[r + s, g ∘ f[s]]`, where
`f[s] : F[r + s] ⟶ F[r][s] ⟶ G[s]`. -/
@[weil "def_fk112_ar_category"]
lemma homMk_comp_homMk {F G H : ProjectiveSystem.{v} Λ l} {r s : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) (g : (shift (s : ℤ)).obj G ⟶ H) :
    homMk r f ≫ homMk s g =
      homMk (r + s) (shiftShift F r s ≫ (shift (s : ℤ)).map f ≫ g) := rfl

/-- The identity of `F` in the A–R category is `[0, ε⁰_F]`, the class of the identity of `F` under
the canonical identification `ε⁰_F : F[0] ⟶ F`. -/
@[weil "def_fk112_ar_category"]
lemma id_eq (F : ProjectiveSystem.{v} Λ l) : 𝟙 (of F) = homMk 0 (natMap F 0) := rfl

/-- `ε⁰_F : F[0] ⟶ F` is the canonical isomorphism `F[0] ≅ F`, so the identity of the A–R
category is the class of the identity of `F`. -/
lemma id_eq_shiftZero (F : ProjectiveSystem.{v} Λ l) :
    𝟙 (of F) = homMk 0 (shiftZero.hom.app F) := by
  rw [id_eq, natMap_zero]

/-- The sum of `[r, f]` and `[s, g]` is `[t, f ∘ ε^{t-r}_{F[r]} + g ∘ ε^{t-s}_{F[s]}]` for any
`t ≥ max r s`, in particular for `t = max r s`; here `ε^{t-r}_{F[r]}` is `shiftMap F hr`
(`shiftMap_app_eq`). -/
@[weil "def_fk112_ar_category"]
lemma homMk_add_homMk {F G : ProjectiveSystem.{v} Λ l} {r s : ℕ} (t : ℕ) (hr : r ≤ t)
    (hs : s ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G) (g : (shift (s : ℤ)).obj F ⟶ G) :
    homMk r f + homMk s g = homMk t (shiftMap F hr ≫ f + shiftMap F hs ≫ g) :=
  ArHom.mk_add_mk t hr hs f g

lemma homMk_zero {F G : ProjectiveSystem.{v} Λ l} (r : ℕ) :
    homMk r (0 : (shift (r : ℤ)).obj F ⟶ G) = 0 :=
  (ArHom.zero_eq_mk r).symm

lemma neg_homMk {F G : ProjectiveSystem.{v} Λ l} {r : ℕ} (f : (shift (r : ℤ)).obj F ⟶ G) :
    -homMk r f = homMk r (-f) := rfl

/-- `[r, f] = [t, f ∘ (F[t] ⟶ F[r])]` for `t ≥ r`. -/
lemma homMk_shiftMap_comp {F G : ProjectiveSystem.{v} Λ l} {r t : ℕ} (h : r ≤ t)
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    homMk t (shiftMap F h ≫ f) = homMk r f :=
  ArHom.mk_shiftMap_comp h f

end ArCategory

end ProjectiveSystem

end CategoryTheory
