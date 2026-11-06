module

public import StacksFrontier.AlgebraicGeometry.Etale.RefinedTorsionStalk
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import Weil.Attr

/-!
# Sections of an étale sheaf with stalks of torsion prime to `p`

Let `F` be an abelian sheaf on the small étale site of a scheme `S`, and `p` a natural number
(in applications the characteristic exponent of a base field). If every element of every stalk
`F_t` at a geometric point `t` is annihilated by a positive integer prime to `p`, then every
section of `F` over a quasi-compact étale `S`-scheme `U` has finite order prime to `p`.

By the stalk criterion
`AlgebraicGeometry.SmallEtale.isPrimeToCharacteristicTorsion_iff_forall_etaleStalk` the
hypothesis says that `F` is of torsion prime to `p`: every section is, locally on a covering
sieve, killed by a positive integer prime to `p`. Such a sheaf has no nonzero section killed by
`p`, since a section killed by `p` and locally by integers prime to `p` vanishes locally, hence
vanishes. A section `s` of finite order `m` with a prime `q` dividing both `m` and `p` would then
give the nonzero section `(m / q) • s`, which is killed by `q` and so by `p`; hence `m` is prime
to `p`. Sections over a quasi-compact object have finite order because `F` is in particular a
torsion sheaf.

## Main results

* `Stacks.Torsion.IsPrimeToCharacteristicTorsion.eq_zero_of_nsmul_eq_zero`: on any site, a
  section of a sheaf of torsion prime to `p` which is killed by `p` vanishes.
* `Stacks.Torsion.IsPrimeToCharacteristicTorsion.coprime_addOrderOf`: on any site, a section of
  finite order of a sheaf of torsion prime to `p` has order prime to `p`.
* `AlgebraicGeometry.SmallEtale.coprime_addOrderOf_of_forall_etaleStalk`: if the stalks of an
  abelian étale sheaf at all geometric points are torsion prime to `p`, every section over a
  quasi-compact étale `S`-scheme has finite order prime to `p`.

## Implementation notes

Freitag and Kiehl state the result for a torsion sheaf on their category `Et(X)` of noetherian
separated étale `X`-schemes, over a scheme `X` over a field of characteristic exponent `p`. Here
`p` is an arbitrary natural number, the base field plays no role, and the sections are taken
over every étale `S`-scheme with quasi-compact underlying scheme, which includes every object of
`Et(S)`. The torsion hypothesis is not needed: it follows from the condition on the stalks.
Over a non-quasi-compact `U` a section need not have finite order, but it is still never killed
by `p` unless it vanishes
(`AlgebraicGeometry.SmallEtale.eq_zero_of_nsmul_eq_zero_of_forall_etaleStalk`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v' v u

namespace Stacks.Torsion.IsPrimeToCharacteristicTorsion

variable {C : Type u} [Category.{v'} C] {J : GrothendieckTopology C} {p : ℕ}
  {F : Sheaf J AddCommGrpCat.{w}}

/-- **A sheaf of torsion prime to `p` has no `p`-torsion sections.** A section killed by `p` is
locally killed by an integer prime to `p` as well, hence vanishes locally, hence vanishes. -/
theorem eq_zero_of_nsmul_eq_zero (hF : IsPrimeToCharacteristicTorsion J p F) {U : C}
    {x : F.obj.obj (op U)} (hx : p • x = 0) : x = 0 := by
  obtain ⟨R, hR, h⟩ := hF U x
  refine sheaf_section_eq_zero_of_mem F x hR fun V f hf ↦ ?_
  obtain ⟨n, -, hcop, hn⟩ := h V f hf
  have hp : p • F.obj.map f.op x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hdvd : addOrderOf (F.obj.map f.op x) ∣ Nat.gcd n p :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hn) (addOrderOf_dvd_of_nsmul_eq_zero hp)
  rw [hcop, Nat.dvd_one] at hdvd
  simpa [hdvd] using addOrderOf_nsmul_eq_zero (F.obj.map f.op x)

/-- **Sections of finite order of a sheaf of torsion prime to `p` have order prime to `p`.** -/
theorem coprime_addOrderOf (hF : IsPrimeToCharacteristicTorsion J p F) {U : C}
    {x : F.obj.obj (op U)} (hx : IsOfFinAddOrder x) : (addOrderOf x).Coprime p := by
  have hm : 0 < addOrderOf x := hx.addOrderOf_pos
  refine Nat.coprime_of_dvd fun q hq hqm hqp ↦ ?_
  obtain ⟨k, hk⟩ := hqm
  obtain ⟨l, hl⟩ := hqp
  have hy : k • x = 0 := by
    refine hF.eq_zero_of_nsmul_eq_zero ?_
    rw [hl, mul_comm q l, mul_smul, smul_smul q k, ← hk, addOrderOf_nsmul_eq_zero,
      smul_zero]
  have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hm)
  have hle : addOrderOf x ≤ k := Nat.le_of_dvd hkpos (addOrderOf_dvd_of_nsmul_eq_zero hy)
  have hlt : k < addOrderOf x := by
    rw [hk]
    exact lt_mul_left hkpos hq.one_lt
  exact absurd hle (not_le.mpr hlt)

end Stacks.Torsion.IsPrimeToCharacteristicTorsion

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {p : ℕ}
  {F : Sheaf (topology B S hS) AddCommGrpCat.{max (u + 1) v}}

/-- If the stalks of an abelian étale sheaf at all geometric points are torsion prime to `p`, no
nonzero section of it, over any étale `S`-scheme, is killed by `p`. -/
theorem eq_zero_of_nsmul_eq_zero_of_forall_etaleStalk
    (hF : ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
      ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • g = 0)
    {U : SmallEtale B S hS} {x : F.obj.obj (op U)} (hx : p • x = 0) : x = 0 :=
  ((isPrimeToCharacteristicTorsion_iff_forall_etaleStalk.{u, v} B S hS p F).2
    hF).eq_zero_of_nsmul_eq_zero hx

/-- **Torsion prime to `p` on stalks gives sections of order prime to `p`.** If every element of
every stalk of an abelian étale sheaf `F` at a geometric point is annihilated by a positive
integer prime to `p`, then every section of `F` over an étale `S`-scheme with quasi-compact
underlying scheme has finite order, and that order is prime to `p`. -/
@[weil "lem_fk105_prime_to_char_iff_stalks"]
theorem coprime_addOrderOf_of_forall_etaleStalk
    (hF : ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
      ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • g = 0)
    (U : SmallEtale B S hS) [CompactSpace ((toScheme B S hS).obj U)] (x : F.obj.obj (op U)) :
    IsOfFinAddOrder x ∧ (addOrderOf x).Coprime p := by
  have hF' := (isPrimeToCharacteristicTorsion_iff_forall_etaleStalk.{u, v} B S hS p F).2 hF
  have hx : IsOfFinAddOrder x :=
    IsTorsionSheaf.isAddTorsion_of_compactSpace
      (Stacks.Torsion.torsionSheafProperty_of_isPrimeToCharacteristicTorsion _ hF') U x
  exact ⟨hx, hF'.coprime_addOrderOf hx⟩

end AlgebraicGeometry.SmallEtale

end
