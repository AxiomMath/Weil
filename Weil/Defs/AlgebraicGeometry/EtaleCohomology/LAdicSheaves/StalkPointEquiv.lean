module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointEquiv
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import Weil.Attr

/-!
# Galois transport on `ℓ`-adic stalks

Let `F = (F_n)_n` be an `ℓ`-adic sheaf on a scheme `X`, let `b` be a geometric point of `X` with
algebraically closed field `k`, and let `σ` be an endomorphism of `k` (in the main case an
automorphism of `k` over a base field `κ`). At each level `n` the Galois transport
`T^b_σ : F_{n,b} → F_{n, b ∘ Spec σ}` is an isomorphism of stalks, and these isomorphisms are
compatible with the transition maps of `F`, since the transitions are morphisms of sheaves and
the transport is natural. Their projective limit is the *Galois transport on the `ℓ`-adic stalk*
`T^b_σ : F_b ≃ F_{b ∘ Spec σ}`, an isomorphism of `ℤ_ℓ`-modules.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.galoisTransport`: the transport
  `T^b_σ : F_b ≃ₗ[ℤ_[ℓ]] F_{b ∘ Spec σ}` on `ℓ`-adic stalks.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.galoisTransport_apply_coe`: the level-`n` component of
  `T^b_σ (x)` is the level-`n` Galois transport `AlgebraicGeometry.galoisTransport` applied to the
  level-`n` component of `x`.
* `Stacks.EtaleCohomology.LAdicSheaf.galoisTransport_stalkMap`: the transport commutes with the
  stalk maps of morphisms of `ℓ`-adic sheaves.

## Implementation notes

The `ℓ`-adic stalk of a strict system `F` is `Stacks.EtaleCohomology.LAdicSheaf.stalk`, the module
of compatible families of finite-level germs, and a morphism `θ : s ⟶ t` of geometric points
induces the isomorphism `Stacks.EtaleCohomology.LAdicSheaf.stalkPointEquiv` of `ℓ`-adic stalks,
the limit of the finite-level stalk maps along `θ`. The transport is that isomorphism for the
morphism `Spec σ : b ∘ Spec σ ⟶ b` of geometric points
(`AlgebraicGeometry.GeometricPoint.specHom`); its level-`n` components are the level-`n`
transports by definition. As for the finite-level transport, `σ` is an arbitrary ring
endomorphism of `k`; an automorphism `σ : k ≃ₐ[κ] k` enters through `σ.toAlgHom.toRingHom`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.4][freitagkiehl1988]
* [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **Galois transport on `ℓ`-adic stalks.** For an `ℓ`-adic sheaf `F`, a geometric point `b`
and an endomorphism `σ` of its field, the isomorphism `T^b_σ : F_b ≃ F_{b ∘ Spec σ}` of
`ℤ_ℓ`-modules which is the projective limit of the finite-level transports
`T^b_σ : F_{n,b} → F_{n, b ∘ Spec σ}` (`galoisTransport_apply_coe`). -/
@[weil "def_fk204_galois_transport_ladic_stalk"]
def LAdicSheaf.galoisTransport (F : LAdicSheaf B X ℓ) (b : GeometricPoint X.1)
    (σ : b.residueField →+* b.residueField) :
    LAdicSheaf.stalk B X ℓ F b ≃ₗ[ℤ_[ℓ]] LAdicSheaf.stalk B X ℓ F (b.precompSpec σ) :=
  LAdicSheaf.stalkPointEquiv B X ℓ F (b.specHom σ)

/-- The level-`n` component of `T^b_σ (x)` is the finite-level Galois transport of the level-`n`
component of `x`. -/
@[weil "def_fk204_galois_transport_ladic_stalk", simp]
lemma LAdicSheaf.galoisTransport_apply_coe (F : LAdicSheaf B X ℓ) (b : GeometricPoint X.1)
    (σ : b.residueField →+* b.residueField) (x : LAdicSheaf.stalk B X ℓ F b) (n : ℕ) :
    (LAdicSheaf.galoisTransport B X ℓ F b σ x).1 n =
      ((AlgebraicGeometry.galoisTransport B X.1 X.property b σ
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).app (F.level n).obj).hom (x.1 n) :=
  rfl

/-- The level-`n` component of `(T^b_σ)⁻¹ (y)` is the inverse of the finite-level Galois
transport applied to the level-`n` component of `y`. -/
lemma LAdicSheaf.galoisTransport_symm_apply_coe (F : LAdicSheaf B X ℓ) (b : GeometricPoint X.1)
    (σ : b.residueField →+* b.residueField) (y : LAdicSheaf.stalk B X ℓ F (b.precompSpec σ))
    (n : ℕ) :
    ((LAdicSheaf.galoisTransport B X ℓ F b σ).symm y).1 n =
      (inv ((AlgebraicGeometry.galoisTransport B X.1 X.property b σ
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).app (F.level n).obj)).hom (y.1 n) :=
  rfl

variable {B X ℓ} in
/-- The transport commutes with the stalk maps of a morphism `φ : F ⟶ G` of `ℓ`-adic sheaves:
`φ_{b ∘ Spec σ} ∘ T^b_σ = T^b_σ ∘ φ_b`. -/
lemma LAdicSheaf.galoisTransport_stalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (b : GeometricPoint X.1) (σ : b.residueField →+* b.residueField)
    (x : LAdicSheaf.stalk B X ℓ F b) :
    LAdicSheaf.galoisTransport B X ℓ G b σ (LAdicSheaf.stalkMap φ b x) =
      LAdicSheaf.stalkMap φ (b.precompSpec σ) (LAdicSheaf.galoisTransport B X ℓ F b σ x) :=
  LAdicSheaf.stalkPointEquiv_stalkMap B X ℓ (b.specHom σ) φ x

end Stacks.EtaleCohomology

end
