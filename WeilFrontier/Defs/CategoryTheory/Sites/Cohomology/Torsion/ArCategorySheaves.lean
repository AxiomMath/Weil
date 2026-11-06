module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ShiftMorphismSheaves
public import Weil.Attr

/-!
# The Artin–Rees category of projective systems of `l`-torsion sheaves

Let `S` be a scheme and `P_S` the category of projective systems `(F_n, u_n)_{n ∈ ℤ}` of
`l`-torsion sheaves on the small étale site of `S`. The *Artin–Rees category* (A–R category)
`AR_S` has the objects of `P_S`, and
`Hom_AR(F, G) = colim_{r ≥ 0} Hom_{P_S}(F[r], G)`,
where the transition map from level `r` to level `r + 1` sends `f` to `f ∘ ε_1^{F[r]}`. The class
of `f : F[r] ⟶ G` is written `[r, f]`. The composite of `[r, f] : F ⟶ G` and `[s, g] : G ⟶ H` is
`[r + s, g ∘ f[s]]`, where `f[s] : F[r + s] ⟶ G[s]`; the identity of `F` is `[0, ε_0^F]`, and the
sum of `[r, f]` and `[s, g]` is `[t, f ∘ ε + g ∘ ε]` at any common level `t ≥ max r s`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftMap F h`: for `r ≤ t`, the map
  `F[t] ⟶ F[r]` whose components are the maps `F_{n+t} ⟶ F_{n+r}` of `F`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.ArHom F G`: the colimit
  `colim_{r ≥ 0} Hom(F[r], G)`, as the quotient of the pairs `(r, f)` by the transition maps.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.ArHom.mk r f`: the class `[r, f]`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem B S hS l`: the A–R category, with
  its `Category` and `Preadditive` structures.

## Main results

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.ArHom.mk_eq_mk_shift_comp_shiftι`:
  `[r, f] = [r + 1, f ∘ ε_1^{F[r]}]`, the transition map of the colimit, with `F[r][1]`
  identified with `F[r + 1]`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.ArHom.mk_eq_mk_iff`: `[r, f] = [s, g]`
  if and only if `f` and `g` agree after precomposition with `F[t] ⟶ F[r]` and `F[t] ⟶ F[s]`
  for some `t ≥ max r s`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.homMk_comp_homMk`:
  `[r, f] ≫ [s, g] = [r + s, g ∘ f[s]]`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.id_eq`: the identity is
  `[0, ε_0^F]`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.homMk_add_homMk`: the sum.

## Implementation notes

The levels `r ≥ 0` form a directed (in fact totally ordered) set, so the colimit of the sets
`Hom(F[r], G)` is the quotient of the disjoint union by the relation identifying `(r, f)` with
`(t, f ∘ (F[t] ⟶ F[r]))` for `t ≥ r`. The map `F[t] ⟶ F[r]` is the composite of the transition
maps `ε_1` of the colimit, up to the identification of `F[r][t - r]` with `F[t]`; it is used
directly, since `F[r][1]` has terms `F_{n+1+r}`, only propositionally equal to the terms
`F_{n+(r+1)}` of `F[r+1]`. In the same way `f[s]` is the composite of the canonical
identification `shiftShift F r s : F[r + s] ⟶ F[r][s]` with `f[s] : F[r][s] ⟶ G[s]`, and `F[0]`
is identified with `F` by `ε_0^F`.

The objects are wrapped in a structure, so that the category structure of the A–R category is not
confused with the one of `P_S` on the same type. The construction is the one made for projective
systems of `l`-power torsion modules, `CategoryTheory.ProjectiveSystem.ArCategory`, for systems
of sheaves.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

namespace IsLTorsionProjectiveSystem

/-- For `r ≤ t`, the natural transformation from the translation `n ↦ n + t` of `ℤᵒᵖ` to the
translation `n ↦ n + r`, whose component at `n` is the morphism given by `n + r ≤ n + t`. -/
def translateLE {r t : ℕ} (h : r ≤ t) : (translate (t : ℤ)).op ⟶ (translate (r : ℤ)).op where
  app n := (homOfLE (by omega : n.unop + r ≤ n.unop + t)).op
  naturality _ _ _ := Subsingleton.elim _ _

/-- For `r, s ≥ 0`, the natural transformation from the translation by `r + s` to the composite
of the translations by `s` and by `r`, whose component at `n` is given by
`n + s + r = n + (r + s)`. -/
def translateAddHom (r s : ℕ) :
    (translate ((r + s : ℕ) : ℤ)).op ⟶ (translate (s : ℤ)).op ⋙ (translate (r : ℤ)).op where
  app n := (homOfLE (by dsimp; omega : n.unop + s + r ≤ n.unop + ((r + s : ℕ) : ℤ))).op
  naturality _ _ _ := Subsingleton.elim _ _

end IsLTorsionProjectiveSystem

namespace LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

section Thin

variable {C : Type*} [Category C] (P : ℤᵒᵖ ⥤ C)

private lemma map_comp_map_eq_map {X Y Z : ℤᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) :
    P.map a ≫ P.map b = P.map c :=
  (P.map_comp a b).symm.trans (congrArg P.map (Subsingleton.elim _ _))

private lemma map_comp_map_eq_map_comp_map {X Y Y' Z : ℤᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z)
    (a' : X ⟶ Y') (b' : Y' ⟶ Z) : P.map a ≫ P.map b = P.map a' ≫ P.map b' :=
  (map_comp_map_eq_map P a b (a ≫ b)).trans (map_comp_map_eq_map P a' b' (a ≫ b)).symm

private lemma map_comp_map_eq_map_comp_map_comp_map {X Y Y' Y'' Z : ℤᵒᵖ} (a : X ⟶ Y)
    (b : Y ⟶ Z) (a' : X ⟶ Y') (b' : Y' ⟶ Y'') (c' : Y'' ⟶ Z) :
    P.map a ≫ P.map b = P.map a' ≫ P.map b' ≫ P.map c' := by
  rw [map_comp_map_eq_map P b' c' (b' ≫ c')]
  exact map_comp_map_eq_map_comp_map P _ _ _ _

end Thin

instance (r : ℤ) : (shift.{w} B S hS l r).Additive where
  map_add := hom_ext fun _ => rfl

/-- For `r ≤ t`, the map `F[t] ⟶ F[r]` whose component `F_{n+t} ⟶ F_{n+r}` is the map of `F`
along `n + r ≤ n + t`. It is the composite of `t - r` transition maps `ε_1` of the colimit
defining A–R morphisms (`shiftMap_succ`). -/
def shiftMap (F : LTorsionProjectiveSystem.{w} B S hS l) {r t : ℕ} (h : r ≤ t) :
    (shift B S hS l (t : ℤ)).obj F ⟶ (shift B S hS l (r : ℤ)).obj F :=
  ObjectProperty.homMk
    (Functor.whiskerRight (IsLTorsionProjectiveSystem.translateLE h) F.obj)

lemma shiftMap_hom_app (F : LTorsionProjectiveSystem.{w} B S hS l) {r t : ℕ} (h : r ≤ t)
    (n : ℤ) : (shiftMap F h).hom.app (op n) =
      F.obj.map (homOfLE (by omega : n + r ≤ n + t)).op :=
  rfl

@[simp]
lemma shiftMap_refl (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    shiftMap F (le_refl r) = 𝟙 _ :=
  hom_ext fun _ => (congrArg F.obj.map (Subsingleton.elim _ _)).trans (F.obj.map_id _)

@[reassoc (attr := simp)]
lemma shiftMap_comp_shiftMap (F : LTorsionProjectiveSystem.{w} B S hS l) {r s t : ℕ}
    (h₁ : r ≤ s) (h₂ : s ≤ t) : shiftMap F h₂ ≫ shiftMap F h₁ = shiftMap F (h₁.trans h₂) :=
  hom_ext fun _ => map_comp_map_eq_map F.obj _ _ _

/-- `ε_r^F ∘ (F[t] ⟶ F[r]) = ε_t^F`. -/
@[reassoc (attr := simp)]
lemma shiftMap_comp_shiftι (F : LTorsionProjectiveSystem.{w} B S hS l) {r t : ℕ} (h : r ≤ t) :
    shiftMap F h ≫ (shiftι B S hS l r).app F = (shiftι B S hS l t).app F :=
  hom_ext fun _ => map_comp_map_eq_map F.obj _ _ _

/-- The maps `F[t] ⟶ F[r]` are natural in `F`. -/
@[reassoc]
lemma shiftMap_naturality {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G) {r t : ℕ}
    (h : r ≤ t) :
    (shift B S hS l (t : ℤ)).map f ≫ shiftMap G h = shiftMap F h ≫ (shift B S hS l (r : ℤ)).map f :=
  hom_ext fun _ => (f.hom.naturality _).symm

/-- The canonical identification `F[r + s] ⟶ F[r][s]`: its component
`F_{n+(r+s)} ⟶ F_{n+s+r}` is the map of `F` along the equality `n + s + r = n + (r + s)`. -/
def shiftShift (F : LTorsionProjectiveSystem.{w} B S hS l) (r s : ℕ) :
    (shift B S hS l ((r + s : ℕ) : ℤ)).obj F ⟶
      (shift B S hS l (s : ℤ)).obj ((shift B S hS l (r : ℤ)).obj F) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (IsLTorsionProjectiveSystem.translateAddHom r s) F.obj)

lemma shiftShift_hom_app (F : LTorsionProjectiveSystem.{w} B S hS l) (r s : ℕ) (n : ℤ) :
    (shiftShift F r s).hom.app (op n) =
      F.obj.map (homOfLE (by push_cast; omega : n + s + r ≤ n + ((r + s : ℕ) : ℤ))).op :=
  rfl

/-- The transition maps of the colimit: `F[r + 1] ⟶ F[r]` is `ε_1^{F[r]}`, after identifying
`F[r + 1]` with `F[r][1]`. -/
lemma shiftMap_succ (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    shiftMap F (Nat.le_succ r) =
      shiftShift F r 1 ≫ (shiftι B S hS l 1).app ((shift B S hS l (r : ℤ)).obj F) :=
  hom_ext fun _ => (map_comp_map_eq_map F.obj _ _ _).symm

@[reassoc]
lemma shiftShift_comp_shift_map_shiftMap (F : LTorsionProjectiveSystem.{w} B S hS l) {r t : ℕ}
    (h : r ≤ t) (s : ℕ) :
    shiftShift F t s ≫ (shift B S hS l (s : ℤ)).map (shiftMap F h) =
      shiftMap F (Nat.add_le_add_right h s) ≫ shiftShift F r s :=
  hom_ext fun _ => map_comp_map_eq_map_comp_map F.obj _ _ _ _

@[reassoc]
lemma shiftShift_comp_shiftMap (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) {s t : ℕ}
    (h : s ≤ t) :
    shiftShift F r t ≫ shiftMap ((shift B S hS l (r : ℤ)).obj F) h =
      shiftMap F (Nat.add_le_add_left h r) ≫ shiftShift F r s :=
  hom_ext fun _ => map_comp_map_eq_map_comp_map F.obj _ _ _ _

@[reassoc]
lemma shiftShift_comp_shift_map_shiftι_zero (F : LTorsionProjectiveSystem.{w} B S hS l)
    (s : ℕ) :
    shiftShift F 0 s ≫ (shift B S hS l (s : ℤ)).map ((shiftι B S hS l 0).app F) =
      shiftMap F (Nat.le_add_left s 0) :=
  hom_ext fun _ => map_comp_map_eq_map F.obj _ _ _

@[reassoc]
lemma shiftShift_comp_shiftι_zero (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) :
    shiftShift F r 0 ≫ (shiftι B S hS l 0).app ((shift B S hS l (r : ℤ)).obj F) =
      shiftMap F (Nat.le_add_right r 0) :=
  hom_ext fun _ => map_comp_map_eq_map F.obj _ _ _

/-- The identification `F[r + s] ⟶ F[r][s]` is natural in `F`. -/
@[reassoc]
lemma shiftShift_naturality {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G)
    (r s : ℕ) :
    (shift B S hS l ((r + s : ℕ) : ℤ)).map f ≫ shiftShift G r s =
      shiftShift F r s ≫ (shift B S hS l (s : ℤ)).map ((shift B S hS l (r : ℤ)).map f) :=
  hom_ext fun _ => (f.hom.naturality _).symm

@[reassoc]
lemma shiftShift_comp_shift_map_shiftShift (F : LTorsionProjectiveSystem.{w} B S hS l)
    (r s u : ℕ) :
    shiftShift F (r + s) u ≫ (shift B S hS l (u : ℤ)).map (shiftShift F r s) =
      shiftMap F (le_of_eq (Nat.add_assoc r s u).symm) ≫ shiftShift F r (s + u) ≫
        shiftShift ((shift B S hS l (r : ℤ)).obj F) s u :=
  hom_ext fun _ => map_comp_map_eq_map_comp_map_comp_map F.obj _ _ _ _ _

/-- The relation on pairs `(r, f)` with `f : F[r] ⟶ G` generating the colimit
`colim_{r ≥ 0} Hom(F[r], G)`: `(r, f)` and `(s, g)` are related if `f` and `g` agree after
precomposition with `F[t] ⟶ F[r]` and `F[t] ⟶ F[s]` for some `t ≥ max r s`. -/
def ArHom.Rel (F G : LTorsionProjectiveSystem.{w} B S hS l) :
    (Σ r : ℕ, (shift B S hS l (r : ℤ)).obj F ⟶ G) →
      (Σ r : ℕ, (shift B S hS l (r : ℤ)).obj F ⟶ G) → Prop
  | ⟨r, f⟩, ⟨s, g⟩ => ∃ (t : ℕ) (hr : r ≤ t) (hs : s ≤ t), shiftMap F hr ≫ f = shiftMap F hs ≫ g

/-- **A–R morphisms of projective systems of `l`-torsion sheaves.** The colimit
`Hom_AR(F, G) = colim_{r ≥ 0} Hom(F[r], G)`, whose transition map from level `r` to level
`r + 1` sends `f` to `f ∘ ε_1^{F[r]}` (`ArHom.mk_eq_mk_shift_comp_shiftι`): the classes `[r, f]`
of pairs `(r, f)` with `f : F[r] ⟶ G`. -/
def ArHom (F G : LTorsionProjectiveSystem.{w} B S hS l) : Type _ :=
  Quot (ArHom.Rel F G)

namespace ArHom

variable {F G H : LTorsionProjectiveSystem.{w} B S hS l}

/-- The class `[r, f]` of `f : F[r] ⟶ G`. -/
def mk (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) : ArHom F G :=
  Quot.mk _ ⟨r, f⟩

lemma mk_surjective (φ : ArHom F G) :
    ∃ (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G), mk r f = φ := by
  induction φ using Quot.ind with
  | mk p => exact ⟨p.1, p.2, rfl⟩

@[elab_as_elim]
lemma ind {motive : ArHom F G → Prop}
    (h : ∀ (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G), motive (mk r f)) (φ : ArHom F G) :
    motive φ := by
  obtain ⟨r, f, rfl⟩ := mk_surjective φ
  exact h r f

/-- `[t, f ∘ (F[t] ⟶ F[r])] = [r, f]` for `t ≥ r`. -/
lemma mk_shiftMap_comp {r t : ℕ} (h : r ≤ t) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    mk t (shiftMap F h ≫ f) = mk r f :=
  Quot.sound ⟨t, le_refl t, h, by simp⟩

lemma mk_eq_mk_shiftMap_comp {r : ℕ} (t : ℕ) (h : r ≤ t)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) : mk r f = mk t (shiftMap F h ≫ f) :=
  (mk_shiftMap_comp h f).symm

/-- The transition map of the colimit: `[r, f] = [r + 1, f ∘ ε_1^{F[r]}]`, where `F[r][1]` is
identified with `F[r + 1]` by `shiftShift F r 1`. -/
lemma mk_eq_mk_shift_comp_shiftι {r : ℕ} (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    mk r f =
      mk (r + 1)
        (shiftShift F r 1 ≫ (shiftι B S hS l 1).app ((shift B S hS l (r : ℤ)).obj F) ≫ f) := by
  rw [← Category.assoc, ← shiftMap_succ]
  exact mk_eq_mk_shiftMap_comp _ _ f

lemma mk_eq_mk_of_comp_eq {r s t : ℕ} (hr : r ≤ t) (hs : s ≤ t)
    {f : (shift B S hS l (r : ℤ)).obj F ⟶ G} {g : (shift B S hS l (s : ℤ)).obj F ⟶ G}
    (h : shiftMap F hr ≫ f = shiftMap F hs ≫ g) : mk r f = mk s g :=
  Quot.sound ⟨t, hr, hs, h⟩

/-- The relation is an equivalence relation: transitivity holds since the levels are directed. -/
lemma rel_trans {a b c : Σ r : ℕ, (shift B S hS l (r : ℤ)).obj F ⟶ G}
    (h₁ : Rel F G a b) (h₂ : Rel F G b c) : Rel F G a c := by
  obtain ⟨r, f⟩ := a
  obtain ⟨s, g⟩ := b
  obtain ⟨u, k⟩ := c
  obtain ⟨t, hr, hs, e⟩ := h₁
  obtain ⟨t', hs', hu, e'⟩ := h₂
  refine ⟨max t t', hr.trans (le_max_left _ _), hu.trans (le_max_right _ _), ?_⟩
  rw [← shiftMap_comp_shiftMap F hr (le_max_left t t'), Category.assoc, e,
    ← Category.assoc, shiftMap_comp_shiftMap,
    ← shiftMap_comp_shiftMap F hs' (le_max_right t t'), Category.assoc, e', ← Category.assoc,
    shiftMap_comp_shiftMap]

lemma rel_equivalence : Equivalence (Rel F G) where
  refl := fun ⟨r, _⟩ => ⟨r, le_rfl, le_rfl, rfl⟩
  symm := fun {a b} h => by
    obtain ⟨r, f⟩ := a
    obtain ⟨s, g⟩ := b
    obtain ⟨t, hr, hs, e⟩ := h
    exact ⟨t, hs, hr, e.symm⟩
  trans := rel_trans

/-- `[r, f] = [s, g]` if and only if `f` and `g` agree after precomposition with
`F[t] ⟶ F[r]` and `F[t] ⟶ F[s]` for some `t ≥ max r s`. -/
lemma mk_eq_mk_iff {r s : ℕ} (f : (shift B S hS l (r : ℤ)).obj F ⟶ G)
    (g : (shift B S hS l (s : ℤ)).obj F ⟶ G) :
    mk r f = mk s g ↔
      ∃ (t : ℕ) (hr : r ≤ t) (hs : s ≤ t), shiftMap F hr ≫ f = shiftMap F hs ≫ g :=
  ⟨fun h => rel_equivalence.eqvGen_iff.mp (Quot.eqvGen_exact h),
    fun ⟨_, hr, hs, e⟩ => mk_eq_mk_of_comp_eq hr hs e⟩

lemma rel_of_shiftMap {X : Sort*} (Φ : (Σ r : ℕ, (shift B S hS l (r : ℤ)).obj F ⟶ G) → X)
    (hΦ : ∀ (r t : ℕ) (h : r ≤ t) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G),
      Φ ⟨t, shiftMap F h ≫ f⟩ = Φ ⟨r, f⟩) :
    ∀ a b, Rel F G a b → Φ a = Φ b := by
  rintro ⟨r, f⟩ ⟨s, g⟩ ⟨t, hr, hs, e⟩
  rw [← hΦ r t hr f, ← hΦ s t hs g, e]

/-- A function on A–R morphisms, from a function on pairs `(r, f)` that is unchanged when
`(r, f)` is replaced by `(t, f ∘ (F[t] ⟶ F[r]))`. -/
def lift {X : Sort*} (Φ : (Σ r : ℕ, (shift B S hS l (r : ℤ)).obj F ⟶ G) → X)
    (hΦ : ∀ (r t : ℕ) (h : r ≤ t) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G),
      Φ ⟨t, shiftMap F h ≫ f⟩ = Φ ⟨r, f⟩) : ArHom F G → X :=
  Quot.lift Φ (rel_of_shiftMap Φ hΦ)

@[simp]
lemma lift_mk {X : Sort*} (Φ : (Σ r : ℕ, (shift B S hS l (r : ℤ)).obj F ⟶ G) → X) (hΦ)
    (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) : lift Φ hΦ (mk r f) = Φ ⟨r, f⟩ := rfl

/-- The representative `g ∘ f[s] : F[r + s] ⟶ H` of the composite of `(r, f)` and `(s, g)`, where
`f[s]` is `F[r + s] ⟶ F[r][s] ⟶ G[s]`. -/
def compRep {r s : ℕ} (f : (shift B S hS l (r : ℤ)).obj F ⟶ G)
    (g : (shift B S hS l (s : ℤ)).obj G ⟶ H) : (shift B S hS l ((r + s : ℕ) : ℤ)).obj F ⟶ H :=
  shiftShift F r s ≫ (shift B S hS l (s : ℤ)).map f ≫ g

lemma mk_compRep_shiftMap_comp_left {r t s : ℕ} (h : r ≤ t)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj G ⟶ H) :
    mk (t + s) (compRep (shiftMap F h ≫ f) g) = mk (r + s) (compRep f g) := by
  rw [← mk_shiftMap_comp (Nat.add_le_add_right h s) (compRep f g)]
  congr 1
  simp only [compRep, Functor.map_comp, Category.assoc, shiftShift_comp_shift_map_shiftMap_assoc]

lemma mk_compRep_shiftMap_comp_right {r s t : ℕ} (h : s ≤ t)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj G ⟶ H) :
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

lemma comp_mk_mk {r s : ℕ} (f : (shift B S hS l (r : ℤ)).obj F ⟶ G)
    (g : (shift B S hS l (s : ℤ)).obj G ⟶ H) :
    comp (mk r f) (mk s g) =
      mk (r + s) (shiftShift F r s ≫ (shift B S hS l (s : ℤ)).map f ≫ g) := rfl

/-- The identity A–R morphism `[0, ε_0^F]`, the class of the identification `F[0] ⟶ F`. -/
def id (F : LTorsionProjectiveSystem.{w} B S hS l) : ArHom F F :=
  mk 0 ((shiftι B S hS l 0).app F)

lemma id_comp (φ : ArHom F G) : comp (id F) φ = φ := by
  induction φ using ind with
  | h s g =>
    rw [id, comp_mk_mk, shiftShift_comp_shift_map_shiftι_zero_assoc]
    exact mk_shiftMap_comp _ g

lemma comp_id (φ : ArHom F G) : comp φ (id G) = φ := by
  induction φ using ind with
  | h r f =>
    rw [id, comp_mk_mk, shiftι_naturality, shiftShift_comp_shiftι_zero_assoc]
    exact mk_shiftMap_comp _ f

lemma comp_assoc {K : LTorsionProjectiveSystem.{w} B S hS l} (φ : ArHom F G) (ψ : ArHom G H)
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

lemma mk_add_eq_mk_add {r s t t' : ℕ} (hr : r ≤ t) (hs : s ≤ t) (hr' : r ≤ t') (hs' : s ≤ t')
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj F ⟶ G) :
    mk t (shiftMap F hr ≫ f + shiftMap F hs ≫ g) =
      mk t' (shiftMap F hr' ≫ f + shiftMap F hs' ≫ g) := by
  refine mk_eq_mk_of_comp_eq (le_max_left t t') (le_max_right t t') ?_
  simp only [Preadditive.comp_add, shiftMap_comp_shiftMap_assoc]

/-- The sum of A–R morphisms: on representatives, the sum of `(r, f)` and `(s, g)` is
`(t, f ∘ (F[t] ⟶ F[r]) + g ∘ (F[t] ⟶ F[s]))` with `t = max r s` (`mk_add_mk`). -/
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

lemma mk_add_mk {r s : ℕ} (t : ℕ) (hr : r ≤ t) (hs : s ≤ t)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj F ⟶ G) :
    mk r f + mk s g = mk t (shiftMap F hr ≫ f + shiftMap F hs ≫ g) :=
  mk_add_eq_mk_add _ _ _ _ f g

lemma mk_add_mk_same {t : ℕ} (f g : (shift B S hS l (t : ℤ)).obj F ⟶ G) :
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

lemma neg_mk {r : ℕ} (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) : -mk r f = mk r (-f) := rfl

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

end LTorsionProjectiveSystem

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (l : ℕ)

/-- **The A–R category `AR_S` of projective systems of `l`-torsion sheaves** on the small étale
site of `S`: its objects are the projective systems of `l`-torsion sheaves, and its morphisms
from `F` to `G` are the A–R morphisms `colim_{r ≥ 0} Hom(F[r], G)`
(`ArLTorsionProjectiveSystem.category`). -/
@[weil "def_fk112_ar_category_sheaves"]
structure ArLTorsionProjectiveSystem where
  /-- The A–R category object of a projective system of `l`-torsion sheaves. -/
  of ::
  /-- The projective system underlying an object of the A–R category. -/
  obj : LTorsionProjectiveSystem.{w} B S hS l

namespace ArLTorsionProjectiveSystem

variable {B S hS l}

open LTorsionProjectiveSystem

/-- The category structure of the A–R category: the morphisms are the A–R morphisms, the
composite of `[r, f]` and `[s, g]` is `[r + s, g ∘ f[s]]` (`homMk_comp_homMk`), and the identity
of `F` is `[0, ε_0^F]` (`id_eq`). -/
@[weil "def_fk112_ar_category_sheaves"]
instance category : Category (ArLTorsionProjectiveSystem.{w} B S hS l) where
  Hom X Y := ArHom X.obj Y.obj
  id X := ArHom.id X.obj
  comp φ ψ := ArHom.comp φ ψ
  id_comp := ArHom.id_comp
  comp_id := ArHom.comp_id
  assoc := ArHom.comp_assoc

/-- The preadditive structure of the A–R category: the sum of `[r, f]` and `[s, g]` is
`[t, f ∘ (F[t] ⟶ F[r]) + g ∘ (F[t] ⟶ F[s])]` for any `t ≥ max r s` (`homMk_add_homMk`). -/
instance preadditive : Preadditive (ArLTorsionProjectiveSystem.{w} B S hS l) where
  homGroup X Y := inferInstanceAs (AddCommGroup (ArHom X.obj Y.obj))
  add_comp _ _ _ φ φ' ψ := ArHom.add_comp φ φ' ψ
  comp_add _ _ _ φ ψ ψ' := ArHom.comp_add φ ψ ψ'

/-- The morphism `[r, f] : F ⟶ G` of the A–R category, for `f : F[r] ⟶ G`. -/
def homMk {F G : LTorsionProjectiveSystem.{w} B S hS l} (r : ℕ)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) : of F ⟶ of G :=
  ArHom.mk r f

lemma homMk_surjective {F G : LTorsionProjectiveSystem.{w} B S hS l} (φ : of F ⟶ of G) :
    ∃ (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G), homMk r f = φ :=
  ArHom.mk_surjective φ

@[elab_as_elim]
lemma hom_induction {X Y : ArLTorsionProjectiveSystem.{w} B S hS l} {motive : (X ⟶ Y) → Prop}
    (h : ∀ (r : ℕ) (f : (shift B S hS l (r : ℤ)).obj X.obj ⟶ Y.obj),
      motive (homMk (F := X.obj) r f))
    (φ : X ⟶ Y) : motive φ :=
  ArHom.ind h φ

/-- The transition maps of the colimit: `[r, f] = [r + 1, f ∘ ε_1^{F[r]}]`, with `F[r][1]`
identified with `F[r + 1]`. -/
@[weil "def_fk112_ar_category_sheaves"]
lemma homMk_eq_homMk_succ {F G : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    homMk r f = homMk (r + 1)
      (shiftShift F r 1 ≫ (shiftι B S hS l 1).app ((shift B S hS l (r : ℤ)).obj F) ≫ f) :=
  ArHom.mk_eq_mk_shift_comp_shiftι f

/-- `[r, f] = [s, g]` if and only if `f` and `g` agree after precomposition with `F[t] ⟶ F[r]`
and `F[t] ⟶ F[s]` for some `t ≥ max r s`: the morphisms of the A–R category are the colimit of
the sets `Hom(F[r], G)`. -/
@[weil "def_fk112_ar_category_sheaves"]
lemma homMk_eq_homMk_iff {F G : LTorsionProjectiveSystem.{w} B S hS l} {r s : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj F ⟶ G) :
    homMk r f = homMk s g ↔
      ∃ (t : ℕ) (hr : r ≤ t) (hs : s ≤ t), shiftMap F hr ≫ f = shiftMap F hs ≫ g :=
  ArHom.mk_eq_mk_iff f g

/-- The composite of `[r, f] : F ⟶ G` and `[s, g] : G ⟶ H` is `[r + s, g ∘ f[s]]`, where
`f[s] : F[r + s] ⟶ F[r][s] ⟶ G[s]`. -/
@[weil "def_fk112_ar_category_sheaves"]
lemma homMk_comp_homMk {F G H : LTorsionProjectiveSystem.{w} B S hS l} {r s : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) (g : (shift B S hS l (s : ℤ)).obj G ⟶ H) :
    homMk r f ≫ homMk s g =
      homMk (r + s) (shiftShift F r s ≫ (shift B S hS l (s : ℤ)).map f ≫ g) := rfl

/-- The identity of `F` in the A–R category is `[0, ε_0^F]`, the class of the canonical
isomorphism `F[0] ≅ F` (`shiftι_zero`). -/
lemma id_eq (F : LTorsionProjectiveSystem.{w} B S hS l) :
    𝟙 (of F) = homMk 0 ((shiftι B S hS l 0).app F) := rfl

lemma id_eq_shiftZeroIso (F : LTorsionProjectiveSystem.{w} B S hS l) :
    𝟙 (of F) = homMk 0 (shiftZeroIso.hom.app F) := by
  rw [id_eq, shiftι_zero]

/-- The sum of `[r, f]` and `[s, g]` is `[t, f ∘ (F[t] ⟶ F[r]) + g ∘ (F[t] ⟶ F[s])]` for any
`t ≥ max r s`. -/
lemma homMk_add_homMk {F G : LTorsionProjectiveSystem.{w} B S hS l} {r s : ℕ} (t : ℕ)
    (hr : r ≤ t) (hs : s ≤ t) (f : (shift B S hS l (r : ℤ)).obj F ⟶ G)
    (g : (shift B S hS l (s : ℤ)).obj F ⟶ G) :
    homMk r f + homMk s g = homMk t (shiftMap F hr ≫ f + shiftMap F hs ≫ g) :=
  ArHom.mk_add_mk t hr hs f g

lemma homMk_zero {F G : LTorsionProjectiveSystem.{w} B S hS l} (r : ℕ) :
    homMk r (0 : (shift B S hS l (r : ℤ)).obj F ⟶ G) = 0 :=
  (ArHom.zero_eq_mk r).symm

lemma neg_homMk {F G : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) : -homMk r f = homMk r (-f) := rfl

/-- `[t, f ∘ (F[t] ⟶ F[r])] = [r, f]` for `t ≥ r`. -/
lemma homMk_shiftMap_comp {F G : LTorsionProjectiveSystem.{w} B S hS l} {r t : ℕ} (h : r ≤ t)
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    homMk t (shiftMap F h ≫ f) = homMk r f :=
  ArHom.mk_shiftMap_comp h f

end ArLTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
