module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import Weil.Defs.RingTheory.Henselian.Henselization.Defs
public import Weil.Defs.RingTheory.Smooth.Locus

/-!
# Strict Henselizations of smooth local algebras

Let `A → B` be a local homomorphism of strictly Henselian local rings. The algebra `B` is
*sh-smooth over `A`* if there are a localization `C` of a smooth `A`-algebra at a prime ideal with
`A → C` local, a separably closed field `k` with a local homomorphism `φ : C → k`, and an
isomorphism of `A`-algebras from `B` to the Henselization `Csh` of `C` with respect to `φ`.
Since `k` is separably closed, `Csh` is a strict Henselization of `C`, and the field `k` and the
map `φ` can be eliminated: `B` is sh-smooth over `A` if and only if it is `A`-isomorphic to a strict
Henselization of a local, essentially smooth `A`-algebra `C`.

## Main definitions

* `Algebra.IsShSmooth A B`: `B` is sh-smooth over `A`.

## Main results

* `Algebra.IsShSmooth.of_algEquiv`, `Algebra.IsShSmooth.iff_of_algEquiv`: the property is
  invariant under isomorphism of `A`-algebras.
* `Algebra.isShSmooth_iff_isHenselization`: `B` is sh-smooth over `A` if and only if it is
  `A`-isomorphic to a strict Henselization (a henselization with residue field a separable closure
  of the residue field) of a localization `C` of a smooth `A`-algebra with `A → C` local.
* `Algebra.IsShSmooth.of_isHenselization`: the strict Henselization of such a `C` is sh-smooth
  over `A`.

## Implementation notes

The source states the definition for a local homomorphism `A → B` of strictly Henselian local
rings. The definition does not need these hypotheses; they are the standing hypotheses under
which it is applied (`StrictlyHenselianLocalRing A`, `StrictlyHenselianLocalRing B`,
`IsLocalHom (algebraMap A B)`), kept as separate instances.

The smooth local homomorphism `A → C` is `Algebra.IsSmoothLocalization A C` together with
`IsLocalHom (algebraMap A C)`, and the Henselization with respect to `φ` is
`IsLocalRing.IsHenselizationAlong`. The rings `C`, `k` and `Csh` are taken in the universe of `A`:
`C` is a localization of a finitely presented `A`-algebra, `k` may be replaced by the separable
closure of the residue field of `C`, and the Henselization exists in the universe of `C`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Algebra

/-- **Sh-smooth algebras.** An `A`-algebra `B` is *sh-smooth over `A`* if there are a
localization `C` of a smooth `A`-algebra at a prime ideal with `A → C` a local homomorphism, a
separably closed field `k` with a local homomorphism `φ : C → k`, and an isomorphism of
`A`-algebras from `B` to the Henselization `(Csh, ψ)` of `C` with respect to `φ`. It is applied to
local homomorphisms `A → B` of strictly Henselian local rings. -/
@[weil "def_fk107_smooth_strictly_henselian_algebra"]
def IsShSmooth (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra A C),
    IsSmoothLocalization A C ∧ IsLocalHom (algebraMap A C) ∧
    ∃ (k : Type u) (_ : Field k) (_ : IsSepClosed k) (φ : C →+* k) (_ : IsLocalHom φ)
      (Csh : Type u) (_ : CommRing Csh) (_ : IsLocalRing Csh) (_ : Algebra C Csh)
      (_ : Algebra A Csh) (_ : IsScalarTower A C Csh) (ψ : Csh →+* k),
      IsHenselizationAlong φ Csh ψ ∧ Nonempty (B ≃ₐ[A] Csh)

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace IsShSmooth

/-- Being sh-smooth is invariant under isomorphism of `A`-algebras. -/
theorem of_algEquiv {B' : Type w} [CommRing B'] [Algebra A B'] (h : IsShSmooth A B)
    (e : B ≃ₐ[A] B') : IsShSmooth A B' := by
  obtain ⟨C, _, _, _, hC, hl, k, _, _, φ, _, Csh, _, _, _, _, _, ψ, hψ, ⟨f⟩⟩ := h
  exact ⟨C, _, ‹_›, _, hC, hl, k, _, ‹_›, φ, ‹_›, Csh, _, ‹_›, _, _, ‹_›, ψ, hψ, ⟨e.symm.trans f⟩⟩

theorem iff_of_algEquiv {B' : Type w} [CommRing B'] [Algebra A B'] (e : B ≃ₐ[A] B') :
    IsShSmooth A B ↔ IsShSmooth A B' :=
  ⟨fun h => h.of_algEquiv e, fun h => h.of_algEquiv e.symm⟩

/-- The strict Henselization of a localization `C` of a smooth `A`-algebra, with `A → C` local,
is sh-smooth over `A`. -/
theorem of_isHenselization {C : Type u} [CommRing C] [IsLocalRing C] [Algebra A C]
    (hC : IsSmoothLocalization A C) [IsLocalHom (algebraMap A C)] (Csh : Type u) [CommRing Csh]
    [IsLocalRing Csh] [Algebra C Csh] [Algebra A Csh] [IsScalarTower A C Csh]
    [IsHenselization C (SeparableClosure (ResidueField C)) Csh] : IsShSmooth A Csh := by
  let k := SeparableClosure (ResidueField C)
  let φ : C →+* k := (algebraMap (ResidueField C) k).comp (residue C)
  have : IsLocalHom φ := inferInstanceAs (IsLocalHom ((algebraMap _ k).comp (residue C)))
  have : IsHenselization C (residueSeparableClosure φ) Csh :=
    IsHenselization.of_residueAlgEquiv
      (IsSepClosure.equiv (ResidueField C) (SeparableClosure (ResidueField C))
        (residueSeparableClosure φ))
  obtain ⟨ψ, hψ⟩ := IsHenselization.exists_isHenselizationAlong (φ := φ) (Ã := Csh)
  exact ⟨C, _, ‹_›, _, hC, inferInstance, k, _, inferInstance, φ, inferInstance, Csh, _, ‹_›, _, _,
    inferInstance, ψ, hψ, ⟨AlgEquiv.refl⟩⟩

end IsShSmooth

/-- **Sh-smooth algebras as strict Henselizations.** `B` is sh-smooth over `A` if and only if it
is `A`-isomorphic to a strict Henselization `Csh` of a localization `C` of a smooth `A`-algebra with
`A → C` local: a henselization of `C` whose residue field is a separable closure of the residue
field of `C`. -/
theorem isShSmooth_iff_isHenselization :
    IsShSmooth A B ↔
      ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra A C),
        IsSmoothLocalization A C ∧ IsLocalHom (algebraMap A C) ∧
        ∃ (Csh : Type u) (_ : CommRing Csh) (_ : IsLocalRing Csh) (_ : Algebra C Csh)
          (_ : Algebra A Csh) (_ : IsScalarTower A C Csh),
          IsHenselization C (SeparableClosure (ResidueField C)) Csh ∧ Nonempty (B ≃ₐ[A] Csh) := by
  constructor
  · rintro ⟨C, _, _, _, hC, hl, k, _, _, φ, _, Csh, _, _, _, _, _, ψ, hψ, e⟩
    exact ⟨C, _, ‹_›, _, hC, hl, Csh, _, ‹_›, _, _, inferInstance,
      hψ.isHenselization_separableClosure, e⟩
  · rintro ⟨C, _, _, _, hC, hl, Csh, _, _, _, _, _, hh, ⟨e⟩⟩
    exact (IsShSmooth.of_isHenselization hC Csh).of_algEquiv e.symm

end Algebra

end
