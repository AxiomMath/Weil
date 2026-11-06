module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap

/-!
# The Mittag-Leffler–Artin–Rees condition

A projective system `F = (F_n, u_n)` of `l`-power torsion `Λ`-modules satisfies the
*Mittag-Leffler–Artin–Rees condition* (MLAR) if the images of the natural maps
`ε^r_F : F[r] ⟶ F` stabilise uniformly: there is `t ≥ 0` with `im ε^r_F = im ε^t_F` for all
`r ≥ t`. In degree `n` the image of `ε^r_F` is the image of `u_{n+1} ∘ ⋯ ∘ u_{n+r}`, so MLAR is
the Mittag-Leffler condition with a stabilisation index independent of the degree.

## Main definitions

* `CategoryTheory.ProjectiveSystem.imageNatMap F r n`: the image of `ε^r_{F,n} : F_{n+r} ⟶ F_n`,
  a submodule of `F_n`.
* `CategoryTheory.ProjectiveSystem.IsMittagLefflerArtinReesWith F t`: `F` satisfies MLAR with
  constant `t`, i.e. `im ε^r_F = im ε^t_F` for all `r ≥ t`.
* `CategoryTheory.ProjectiveSystem.IsMittagLefflerArtinRees F`: `F` satisfies MLAR with some
  constant.

## Main results

* `CategoryTheory.ProjectiveSystem.imageNatMap_antitone`: the images `im ε^r_F` decrease in `r`.
* `CategoryTheory.ProjectiveSystem.isMittagLefflerArtinReesWith_iff_le`: MLAR with constant `t`
  holds iff `im ε^t_F ⊆ im ε^r_F` for all `r ≥ t`.
* `CategoryTheory.ProjectiveSystem.IsMittagLefflerArtinReesWith.mono`: MLAR with constant `t`
  implies MLAR with any larger constant.

## Implementation notes

The image of `ε^r_F` is a subsystem of `F`; two subsystems of `F` coincide exactly when their
terms coincide in every degree, so the equality of images "as subobjects of `F`" is stated
degreewise, as an equality of submodules `im ε^r_{F,n} = im ε^t_{F,n}` of `F_n` for every `n`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The image of the component `ε^r_{F,n} : F_{n+r} ⟶ F_n` of the natural map, a submodule
of `F_n`: the `n`-th term of the image subsystem `im ε^r_F ⊆ F`. -/
def imageNatMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) (n : ℤ) : Submodule Λ (F.term n) :=
  LinearMap.range (app (natMap F r) n).hom

/-- The images of the natural maps decrease: `im ε^s_F ⊆ im ε^r_F` for `r ≤ s`. -/
lemma imageNatMap_antitone (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    Antitone fun r => imageNatMap F r n := by
  intro r s hrs
  have h : app (natMap F s) n =
      F.obj.map (homOfLE (by simpa using hrs : n + r ≤ n + s)).op ≫ app (natMap F r) n := by
    rw [natMap_app, natMap_app, ← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  simp only [imageNatMap, h]
  exact LinearMap.range_comp_le_range _ _

/-- `F` satisfies the Mittag-Leffler–Artin–Rees condition with constant `t`: the image of
`ε^r_F : F[r] ⟶ F` equals the image of `ε^t_F : F[t] ⟶ F`, as subsystems of `F`, for every
`r ≥ t`. -/
@[weil "def_fk112_mittag_leffler_artin_rees"]
def IsMittagLefflerArtinReesWith (F : ProjectiveSystem.{v} Λ l) (t : ℕ) : Prop :=
  ∀ r, t ≤ r → ∀ n : ℤ, imageNatMap F r n = imageNatMap F t n

/-- `F` satisfies the Mittag-Leffler–Artin–Rees condition (MLAR): there is `t ≥ 0` with
`im ε^r_F = im ε^t_F`, as subsystems of `F`, for all `r ≥ t`. -/
@[weil "def_fk112_mittag_leffler_artin_rees"]
def IsMittagLefflerArtinRees (F : ProjectiveSystem.{v} Λ l) : Prop :=
  ∃ t : ℕ, F.IsMittagLefflerArtinReesWith t

lemma isMittagLefflerArtinRees_iff (F : ProjectiveSystem.{v} Λ l) :
    F.IsMittagLefflerArtinRees ↔
      ∃ t : ℕ, ∀ r, t ≤ r → ∀ n : ℤ, imageNatMap F r n = imageNatMap F t n :=
  Iff.rfl

/-- Since the images decrease, MLAR with constant `t` only asks for `im ε^t_F ⊆ im ε^r_F`. -/
lemma isMittagLefflerArtinReesWith_iff_le (F : ProjectiveSystem.{v} Λ l) (t : ℕ) :
    F.IsMittagLefflerArtinReesWith t ↔
      ∀ r, t ≤ r → ∀ n : ℤ, imageNatMap F t n ≤ imageNatMap F r n :=
  ⟨fun h r hr n => (h r hr n).ge, fun h r hr n =>
    le_antisymm (imageNatMap_antitone F n hr) (h r hr n)⟩

lemma IsMittagLefflerArtinReesWith.imageNatMap_eq {F : ProjectiveSystem.{v} Λ l} {t : ℕ}
    (h : F.IsMittagLefflerArtinReesWith t) {r : ℕ} (hr : t ≤ r) (n : ℤ) :
    imageNatMap F r n = imageNatMap F t n :=
  h r hr n

/-- MLAR with constant `t` implies MLAR with any constant `s ≥ t`. -/
lemma IsMittagLefflerArtinReesWith.mono {F : ProjectiveSystem.{v} Λ l} {t s : ℕ}
    (h : F.IsMittagLefflerArtinReesWith t) (hts : t ≤ s) : F.IsMittagLefflerArtinReesWith s :=
  fun r hr n => (h r (hts.trans hr) n).trans (h s hts n).symm

lemma IsMittagLefflerArtinReesWith.isMittagLefflerArtinRees {F : ProjectiveSystem.{v} Λ l}
    {t : ℕ} (h : F.IsMittagLefflerArtinReesWith t) : F.IsMittagLefflerArtinRees :=
  ⟨t, h⟩

/-- Under MLAR with constant `t`, the images `im ε^r_F` and `im ε^s_F` agree for `r, s ≥ t`. -/
lemma IsMittagLefflerArtinReesWith.imageNatMap_eq_of_le {F : ProjectiveSystem.{v} Λ l}
    {t : ℕ} (h : F.IsMittagLefflerArtinReesWith t) {r s : ℕ} (hr : t ≤ r) (hs : t ≤ s)
    (n : ℤ) : imageNatMap F r n = imageNatMap F s n :=
  (h r hr n).trans (h s hs n).symm

end ProjectiveSystem

end CategoryTheory
