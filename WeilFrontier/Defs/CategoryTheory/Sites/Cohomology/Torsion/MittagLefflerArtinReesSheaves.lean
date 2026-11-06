module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ShiftMorphismSheaves
public import Weil.Attr

/-!
# The Mittag-Leffler–Artin–Rees condition for projective systems of `l`-torsion sheaves

Let `F = (F_n, u_n)_n` be a projective system of `l`-torsion sheaves on the small étale site of a
scheme `S`, and for `r ≥ 0` let `ε_r^F : F[r] ⟶ F` be the natural morphism, with components
`ε_{r,n} = u_{n+1} ∘ ⋯ ∘ u_{n+r} : F_{n+r} ⟶ F_n`. The system `F` satisfies the
*Mittag-Leffler–Artin–Rees condition* (MLAR) *with constant `r`* if `im ε_t^F = im ε_r^F`, as
subsystems of `F`, for all `t ≥ r`; it satisfies MLAR if it does so with some constant `r ≥ 0`.
In degree `n` the image of `ε_t^F` is the image of `F_{n+t} ⟶ F_n`, so MLAR is the
Mittag-Leffler condition with a stabilisation index independent of the degree.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.imageShiftι F r n`: the image of
  `ε_{r,n} : F_{n+r} ⟶ F_n`, a subobject of the sheaf `F_n`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.IsMittagLefflerArtinReesWith F r`: `F`
  satisfies MLAR with constant `r`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.IsMittagLefflerArtinRees F`: `F`
  satisfies MLAR with some constant.

## Main results

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.imageShiftι_antitone`: the images
  `im ε_t^F` decrease in `t`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.isMittagLefflerArtinReesWith_iff_le`:
  MLAR with constant `r` holds iff `im ε_r^F ≤ im ε_t^F` for all `t ≥ r`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.IsMittagLefflerArtinReesWith.mono`:
  MLAR with constant `r` implies MLAR with any larger constant.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.isMittagLefflerArtinReesWith_zero_iff`:
  MLAR with constant `0` says that every `ε_{t,n}` has image all of `F_n`.

## Implementation notes

The image of `ε_t^F` is a subsystem of `F`, and two subsystems of `F` coincide exactly when their
terms coincide in every degree; so the equality of images "as subsystems of `F`" is stated
degreewise, as an equality `im ε_{t,n} = im ε_{r,n}` of subobjects of the sheaf `F_n`, for every
`n ∈ ℤ`. This is the formulation of
`CategoryTheory.ProjectiveSystem.IsMittagLefflerArtinReesWith` for systems of modules, with
submodules replaced by subobjects (`CategoryTheory.Limits.imageSubobject`). The images exist in
the category of abelian sheaves, which is abelian as soon as sheafification exists; the
definitions take the existence of images as an instance argument, so that they apply in every
universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

namespace LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}
variable [HasImages (Sheaf (topology B S hS) AddCommGrpCat.{w})]

/-- The image of the component `ε_{r,n} : F_{n+r} ⟶ F_n` of the natural morphism
`ε_r^F : F[r] ⟶ F`, a subobject of the sheaf `F_n`: the `n`-th term of the image subsystem
`im ε_r^F ⊆ F`. -/
def imageShiftι (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) (n : ℤ) :
    Subobject (F.obj.obj (op n)) :=
  imageSubobject (((shiftι B S hS l r).app F).hom.app (op n))

theorem imageShiftι_eq (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) (n : ℤ) :
    imageShiftι F r n = imageSubobject (F.obj.map (homOfLE (by simp : n ≤ n + r)).op) :=
  rfl

/-- The images of the natural morphisms decrease: `im ε_s^F ≤ im ε_r^F` for `r ≤ s`. -/
theorem imageShiftι_antitone (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    Antitone fun r => imageShiftι F r n := by
  intro r s hrs
  have h : F.obj.map (homOfLE (by simp : n ≤ n + s)).op =
      F.obj.map (homOfLE (by simpa using hrs : n + r ≤ n + s)).op ≫
        F.obj.map (homOfLE (by simp : n ≤ n + r)).op := by
    rw [← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  simp only [imageShiftι_eq, h]
  exact imageSubobject_comp_le _ _

/-- **MLAR with constant `r`.** A projective system `F` of `l`-torsion sheaves satisfies the
Mittag-Leffler–Artin–Rees condition with constant `r` if the image of `ε_t^F : F[t] ⟶ F` equals
the image of `ε_r^F : F[r] ⟶ F`, as subsystems of `F`, for every `t ≥ r`. -/
@[weil "def_fk112_mittag_leffler_artin_rees_sheaves"]
def IsMittagLefflerArtinReesWith (F : LTorsionProjectiveSystem.{w} B S hS l) (r : ℕ) : Prop :=
  ∀ t, r ≤ t → ∀ n : ℤ, imageShiftι F t n = imageShiftι F r n

/-- **MLAR.** A projective system `F` of `l`-torsion sheaves satisfies the
Mittag-Leffler–Artin–Rees condition if it satisfies it with some constant `r ≥ 0`. -/
@[weil "def_fk112_mittag_leffler_artin_rees_sheaves"]
def IsMittagLefflerArtinRees (F : LTorsionProjectiveSystem.{w} B S hS l) : Prop :=
  ∃ r : ℕ, IsMittagLefflerArtinReesWith F r

theorem isMittagLefflerArtinRees_iff (F : LTorsionProjectiveSystem.{w} B S hS l) :
    IsMittagLefflerArtinRees F ↔
      ∃ r : ℕ, ∀ t, r ≤ t → ∀ n : ℤ, imageShiftι F t n = imageShiftι F r n :=
  Iff.rfl

/-- Since the images decrease, MLAR with constant `r` only asks for `im ε_r^F ≤ im ε_t^F`. -/
theorem isMittagLefflerArtinReesWith_iff_le (F : LTorsionProjectiveSystem.{w} B S hS l)
    (r : ℕ) :
    IsMittagLefflerArtinReesWith F r ↔
      ∀ t, r ≤ t → ∀ n : ℤ, imageShiftι F r n ≤ imageShiftι F t n :=
  ⟨fun h t ht n => (h t ht n).ge, fun h t ht n =>
    le_antisymm (imageShiftι_antitone F n ht) (h t ht n)⟩

theorem IsMittagLefflerArtinReesWith.imageShiftι_eq
    {F : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ} (h : IsMittagLefflerArtinReesWith F r)
    {t : ℕ} (ht : r ≤ t) (n : ℤ) : imageShiftι F t n = imageShiftι F r n :=
  h t ht n

/-- MLAR with constant `r` implies MLAR with any constant `s ≥ r`. -/
theorem IsMittagLefflerArtinReesWith.mono {F : LTorsionProjectiveSystem.{w} B S hS l}
    {r s : ℕ} (h : IsMittagLefflerArtinReesWith F r) (hrs : r ≤ s) :
    IsMittagLefflerArtinReesWith F s :=
  fun t ht n => (h t (hrs.trans ht) n).trans (h s hrs n).symm

theorem IsMittagLefflerArtinReesWith.isMittagLefflerArtinRees
    {F : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ} (h : IsMittagLefflerArtinReesWith F r) :
    IsMittagLefflerArtinRees F :=
  ⟨r, h⟩

/-- Under MLAR with constant `r`, the images `im ε_t^F` and `im ε_s^F` agree for `t, s ≥ r`. -/
theorem IsMittagLefflerArtinReesWith.imageShiftι_eq_of_le
    {F : LTorsionProjectiveSystem.{w} B S hS l} {r : ℕ} (h : IsMittagLefflerArtinReesWith F r)
    {t s : ℕ} (ht : r ≤ t) (hs : r ≤ s) (n : ℤ) : imageShiftι F t n = imageShiftι F s n :=
  (h t ht n).trans (h s hs n).symm

/-- The image of `ε_0^F` is all of `F`. -/
theorem imageShiftι_zero (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    imageShiftι F 0 n = ⊤ := by
  have : IsIso (((shiftι B S hS l 0).app F).hom.app (op n)) := by
    rw [shiftι_zero_app_hom_app]
    exact (eqToIso (congrArg (fun m : ℤ ↦ F.obj.obj (op m))
      (show n + ((0 : ℕ) : ℤ) = n by simp))).isIso_hom
  rw [imageShiftι, imageSubobject_mono, Subobject.mk_eq_top_of_isIso]

/-- MLAR with constant `0` says that every component `ε_{t,n} : F_{n+t} ⟶ F_n` has image all
of `F_n`. -/
theorem isMittagLefflerArtinReesWith_zero_iff (F : LTorsionProjectiveSystem.{w} B S hS l) :
    IsMittagLefflerArtinReesWith F 0 ↔ ∀ t : ℕ, ∀ n : ℤ, imageShiftι F t n = ⊤ := by
  simp only [IsMittagLefflerArtinReesWith, imageShiftι_zero, zero_le, true_implies]

end LTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
