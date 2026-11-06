module

public import Weil.Attr
public import WeilFrontier.RingTheory.Etale.Locus
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic

/-!
# Henselizations along a local-étale homomorphism

Let `B → C` be a local-étale homomorphism of noetherian local rings
(`RingHom.IsEtaleLocalHom`) and let `φ : C → k` be a local homomorphism to a field. A
Henselization `(C̃, ψ)` of `C` with respect to `φ` is also a Henselization of `B` with respect to
the composite `B → C → k`. Since a Henselization with respect to a map to a field is unique up to
unique isomorphism compatible with the maps to `k`, the Henselization of `C` with respect to `φ`
and that of `B` with respect to `B → C → k` are isomorphic as `B`-algebras.

The case of the source is `B = A[T₁, …, T_r]_𝔭`, for a noetherian ring `A`, a localization
`C = (C₀)_𝔮` of a finitely generated `A`-algebra `C₀` at a prime, an `A`-algebra homomorphism
`ψ : A[T] → C` and `𝔭 = ψ⁻¹(𝔪_C)`.

## Main results

* `Algebra.indEtale_of_isEtaleLocalHom`: a local-étale homomorphism is ind-étale.
* `IsLocalRing.residueSeparableClosure_comp_eq`: for `B → C` local with finite separable residue
  field extension, the separable closures of the residue fields of `B` and `C` in `k` coincide.
* `IsLocalRing.IsHenselizationAlong.of_isEtaleLocalHom`: a Henselization of `C` with respect to
  `φ` is a Henselization of `B` with respect to `B → C → k`.
* `IsLocalRing.IsHenselizationAlong.exists_algEquiv`: two Henselizations of `A` with respect to
  `φ` are isomorphic as `A`-algebras, compatibly with their maps to `k`.
* `IsLocalRing.IsHenselizationAlong.exists_ringEquiv_of_isEtaleLocalHom_mvPolynomial`: the
  statement of the source for `A[T]_𝔭 → (C₀)_𝔮`.

## Implementation notes

The source deduces the result from the corresponding statement for strict local rings of an
étale morphism of schemes, after spreading `A[T]_𝔭 → C` out to an étale homomorphism
`A[T] → C₀[1/s]`. Here the argument is made directly at the level of rings: `C` is ind-étale over
`B`, being the localization at a prime of an étale `B`-algebra, so a Henselization of `C` is
ind-étale over `B` (ind-étale homomorphisms compose), and the separable closures of the residue
fields of `B` and `C` inside `k` agree because `κ(C)/κ(B)` is finite separable. The field `k` is
not assumed separably closed.

The induced homomorphism `A[T]_𝔭 → C` is an argument `g` with `g ∘ (A[T] → A[T]_𝔭) = ψ`; it is
unique by the universal property of localization, and it is automatically local
(`IsLocalRing.isLocalHom_of_comp_algebraMap_eq`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT)
-/

public section

open IsLocalRing

universe u v w w' w''

namespace Algebra

open StacksDraft

/-- **A local-étale homomorphism is ind-étale.** If `B → C` is a local-étale homomorphism of
noetherian local rings, then `C` is a filtered colimit of étale `B`-algebras. -/
theorem indEtale_of_isEtaleLocalHom {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    [Algebra B C] [IsNoetherianRing B] [IsNoetherianRing C] [IsLocalRing B] [IsLocalRing C]
    [IsLocalHom (algebraMap B C)] (h : (algebraMap B C).IsEtaleLocalHom) : IndEtale B C := by
  obtain ⟨E, _, _, hE, 𝔭, _, ⟨e⟩⟩ :=
    exists_etale_algEquiv_localization_atPrime_of_isEtaleLocalHom B C h
  have h1 : IndEtale B E := by
    have : Algebra.Etale B (ULift.{u} E) := Algebra.Etale.of_equiv ULift.algEquiv.symm
    exact CategoryTheory.ObjectProperty.le_ind (CommAlgCat.etale.{max u v} B)
      (CommAlgCat.of B (ULift.{u} E)) this
  have h2 : IndEtale E (Localization.AtPrime 𝔭) := indEtale_atPrime 𝔭
  have h3 : IndEtale B (Localization.AtPrime 𝔭) := indEtale_comp h1 h2
  exact indEtale_of_equiv (RingEquiv.refl B) e.toRingEquiv (fun b => e.commutes b) h3

end Algebra

namespace IsLocalRing

/-- For a local homomorphism `B → C` of local rings with separable residue field extension and a
local homomorphism `φ : C → k` to a field, the separable closure of `κ(B)` in `k` along
`B → C → k` is the separable closure of `κ(C)` in `k` along `φ`. -/
theorem residueSeparableClosure_comp_eq {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    [Algebra B C] [IsLocalRing B] [IsLocalRing C] [IsLocalHom (algebraMap B C)]
    [Algebra.IsSeparable (ResidueField B) (ResidueField C)]
    {k : Type w} [Field k] (φ : C →+* k) [IsLocalHom φ] :
    residueSeparableClosure (φ.comp (algebraMap B C)) = residueSeparableClosure φ := by
  ext x
  rw [mem_residueSeparableClosure, mem_residueSeparableClosure]
  let : Algebra (ResidueField C) k := (ResidueField.lift φ).toAlgebra
  let : Algebra (ResidueField B) k := (ResidueField.lift (φ.comp (algebraMap B C))).toAlgebra
  have : IsScalarTower (ResidueField B) (ResidueField C) k := by
    refine IsScalarTower.of_algebraMap_eq fun y => ?_
    obtain ⟨b, rfl⟩ := residue_surjective y
    change ResidueField.lift (φ.comp (algebraMap B C)) (residue B b) =
      ResidueField.lift φ (ResidueField.map (algebraMap B C) (residue B b))
    rw [ResidueField.map_residue, ResidueField.lift_residue_apply,
      ResidueField.lift_residue_apply, RingHom.comp_apply]
  exact ⟨fun hx => hx.tower_top (ResidueField C),
    fun hx => IsSeparable.of_algebra_isSeparable_of_isSeparable (ResidueField B) hx⟩

/-- The homomorphism `P_𝔭 → C` induced by `ψ : P → C`, for `C` local and `𝔭 = ψ⁻¹(𝔪_C)`, is
local. -/
theorem isLocalHom_of_comp_algebraMap_eq {P : Type u} {C : Type v} [CommRing P] [CommRing C]
    [IsLocalRing C] (ψ : P →+* C)
    (g : Localization.AtPrime ((maximalIdeal C).comap ψ) →+* C)
    (hg : g.comp (algebraMap P _) = ψ) : IsLocalHom g := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective ((maximalIdeal C).comap ψ).primeCompl x
  have hs : IsUnit (g (algebraMap P _ (s : P))) := by
    rw [← RingHom.comp_apply, hg]
    by_contra hn
    exact s.2 (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hn))
  have ha : IsUnit (g (algebraMap P _ a)) := by
    have : g (IsLocalization.mk' _ a s) * g (algebraMap P _ (s : P)) = g (algebraMap P _ a) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [← this]
    exact hx.mul hs
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro ha'
  change ψ a ∈ maximalIdeal C at ha'
  rw [mem_maximalIdeal, mem_nonunits_iff, ← hg] at ha'
  exact ha' ha

namespace IsHenselizationAlong

/-- **Henselizations along a local-étale homomorphism.** Let `B → C` be a local-étale
homomorphism of noetherian local rings and `φ : C → k` a local homomorphism to a field. A
Henselization `(C̃, ψ)` of `C` with respect to `φ` is a Henselization of `B` with respect to the
composite `B → C → k`. -/
theorem of_isEtaleLocalHom {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra B C]
    [IsNoetherianRing B] [IsNoetherianRing C] [IsLocalRing B] [IsLocalRing C]
    [IsLocalHom (algebraMap B C)] (hBC : (algebraMap B C).IsEtaleLocalHom)
    {k : Type w} [Field k] {φ : C →+* k} [IsLocalHom φ]
    {C' : Type w'} [CommRing C'] [IsLocalRing C'] [Algebra C C'] [Algebra B C']
    [IsScalarTower B C C'] {ψ : C' →+* k} (h : IsHenselizationAlong φ C' ψ) :
    IsHenselizationAlong (φ.comp (algebraMap B C)) C' ψ := by
  have : Algebra.FormallyUnramified B C := RingHom.formallyUnramified_algebraMap.mp hBC.2.1
  have : Algebra.EssFiniteType B C := RingHom.essFiniteType_algebraMap.mp hBC.2.2
  have heq := residueSeparableClosure_comp_eq (B := B) φ
  have := h.isHenselization
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := C)
    (L := residueSeparableClosure φ) (Rh := C')
  refine ⟨⟨h.henselian, ?_, ⟨(RingEquiv.subfieldCongr heq).trans e, fun b => ?_⟩⟩, ?_⟩
  · exact StacksDraft.indEtale_comp (Algebra.indEtale_of_isEtaleLocalHom hBC)
      (IsHenselization.ind_etale (R := C) (L := residueSeparableClosure φ) (Rh := C'))
  · have : RingEquiv.subfieldCongr heq
        (algebraMap (ResidueField B) _ (residue B b)) =
        algebraMap (ResidueField C) (residueSeparableClosure φ) (residue C (algebraMap B C b)) := by
      apply Subtype.ext
      change ResidueField.lift (φ.comp (algebraMap B C)) (residue B b) =
        ResidueField.lift φ (residue C (algebraMap B C b))
      rw [ResidueField.lift_residue_apply, ResidueField.lift_residue_apply, RingHom.comp_apply]
    rw [RingEquiv.trans_apply, this, he, ← IsScalarTower.algebraMap_apply]
  · rw [IsScalarTower.algebraMap_eq B C C', ← RingHom.comp_assoc, h.ψ_comp_algebraMap]

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type v} [Field k] {φ : A →+* k}
  [IsLocalHom φ]

/-- Two local `A`-algebra homomorphisms from a Henselization of `A` with respect to `φ` to a
henselian local ring `D` agree as soon as they agree after a local homomorphism `D → k`. -/
theorem algHom_ext {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}
    (h : IsHenselizationAlong φ Ã ψ) {D : Type w'} [CommRing D] [HenselianLocalRing D]
    [Algebra A D] (χ : D →+* k) [IsLocalHom χ] (f f' : Ã →ₐ[A] D) [IsLocalHom f]
    [IsLocalHom f'] (hff' : χ.comp f.toRingHom = χ.comp f'.toRingHom) : f = f' := by
  have := h.isHenselization
  have : IsLocalHom f.toRingHom := ⟨fun x hx => IsLocalHom.map_nonunit (f := f) x hx⟩
  have hi : StacksDraft.IndEtale A Ã :=
    IsHenselization.ind_etale (R := A) (L := residueSeparableClosure φ) (Rh := Ã)
  obtain ⟨u, -, hu⟩ := StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale hi
    (ResidueField.map f.toRingHom) (by
      ext a
      simp [ResidueField.map_residue])
  have hres : (residue D).comp f'.toRingHom =
      (ResidueField.map f.toRingHom).comp (residue Ã) := by
    ext x
    apply (ResidueField.lift χ).injective
    simp only [RingHom.comp_apply, ResidueField.map_residue, ResidueField.lift_residue_apply]
    exact (RingHom.congr_fun hff' x).symm
  rw [hu f ⟨inferInstance, by ext x; simp [ResidueField.map_residue]⟩,
    hu f' ⟨inferInstance, hres⟩]

/-- A Henselization `(Ã, ψ)` of `A` with respect to `φ` maps to any other one `(Ã', ψ')` by a
local `A`-algebra homomorphism compatible with the maps to `k`. -/
theorem exists_algHom {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}
    (h : IsHenselizationAlong φ Ã ψ) {Ã' : Type w'} [CommRing Ã'] [IsLocalRing Ã']
    [Algebra A Ã'] {ψ' : Ã' →+* k} (h' : IsHenselizationAlong φ Ã' ψ') :
    ∃ f : Ã →ₐ[A] Ã', IsLocalHom f ∧ ψ'.comp f.toRingHom = ψ := by
  have := h.isHenselization
  have := h.isLocalHom_ψ
  have := h'.isLocalHom_ψ
  have := h'.henselian
  have hi : StacksDraft.IndEtale A Ã :=
    IsHenselization.ind_etale (R := A) (L := residueSeparableClosure φ) (Rh := Ã)
  have mem : ∀ x : ResidueField Ã, ResidueField.lift ψ x ∈ (ResidueField.lift ψ').range := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rw [ResidueField.lift_residue_apply]
    have : ψ a ∈ ψ'.range := by
      rw [h'.range_ψ, ← h.range_ψ]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := this
    exact ⟨residue Ã' b, by rw [ResidueField.lift_residue_apply, hb]⟩
  let σ : ResidueField Ã' ≃+* (ResidueField.lift ψ').range :=
    RingEquiv.ofBijective (ResidueField.lift ψ').rangeRestrict
      ⟨fun x y hxy => (ResidueField.lift ψ').injective (congrArg Subtype.val hxy),
        (ResidueField.lift ψ').rangeRestrict_surjective⟩
  let ρ : ResidueField Ã →+* ResidueField Ã' :=
    σ.symm.toRingHom.comp ((ResidueField.lift ψ).codRestrict _ mem)
  have hρ : ∀ x, ResidueField.lift ψ' (ρ x) = ResidueField.lift ψ x := fun x =>
    congrArg Subtype.val (σ.apply_symm_apply ((ResidueField.lift ψ).codRestrict _ mem x))
  obtain ⟨f, ⟨hfl, hfr⟩, -⟩ := StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale hi ρ
    (by
      ext a
      apply (ResidueField.lift ψ').injective
      simp only [RingHom.comp_apply, hρ, ResidueField.lift_residue_apply, h.ψ_algebraMap,
        h'.ψ_algebraMap])
  refine ⟨f, hfl, RingHom.ext fun x => ?_⟩
  have hx := RingHom.congr_fun hfr x
  simp only [RingHom.comp_apply] at hx
  change ψ' (f x) = ψ x
  rw [← ResidueField.lift_residue_apply ψ' (f x), ← ResidueField.lift_residue_apply ψ x,
    ← hρ]
  exact congrArg _ hx

/-- **Uniqueness of the Henselization with respect to `φ`** (Stacks 08HT). Two Henselizations
`(Ã, ψ)` and `(Ã', ψ')` of `A` with respect to `φ` are isomorphic as `A`-algebras, by an
isomorphism compatible with the maps `ψ` and `ψ'` to `k`. -/
theorem exists_algEquiv {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}
    (h : IsHenselizationAlong φ Ã ψ) {Ã' : Type w'} [CommRing Ã'] [IsLocalRing Ã']
    [Algebra A Ã'] {ψ' : Ã' →+* k} (h' : IsHenselizationAlong φ Ã' ψ') :
    ∃ e : Ã ≃ₐ[A] Ã', ∀ x, ψ' (e x) = ψ x := by
  obtain ⟨f, hf, hψf⟩ := h.exists_algHom h'
  obtain ⟨g, hg, hψg⟩ := h'.exists_algHom h
  have := h.isLocalHom_ψ
  have := h'.isLocalHom_ψ
  have := h.henselian
  have := h'.henselian
  have hgf : IsLocalHom (g.comp f) :=
    ⟨fun x hx => hf.map_nonunit x (hg.map_nonunit (f x) hx)⟩
  have hfg : IsLocalHom (f.comp g) :=
    ⟨fun x hx => hg.map_nonunit x (hf.map_nonunit (g x) hx)⟩
  have hid : IsLocalHom (AlgHom.id A Ã) := ⟨fun _ hx => hx⟩
  have hid' : IsLocalHom (AlgHom.id A Ã') := ⟨fun _ hx => hx⟩
  have e1 : g.comp f = AlgHom.id A Ã := h.algHom_ext ψ _ _ (by
    ext x
    change ψ (g (f x)) = ψ x
    exact (RingHom.congr_fun hψg (f x)).trans (RingHom.congr_fun hψf x))
  have e2 : f.comp g = AlgHom.id A Ã' := h'.algHom_ext ψ' _ _ (by
    ext x
    change ψ' (f (g x)) = ψ' x
    exact (RingHom.congr_fun hψf (g x)).trans (RingHom.congr_fun hψg x))
  exact ⟨AlgEquiv.ofAlgHom f g e2 e1, fun x => RingHom.congr_fun hψf x⟩

/-- **The Henselization of `(C₀)_𝔮` along a local-étale `A[T]_𝔭 → (C₀)_𝔮`.** Let `A` be a
noetherian ring, `C₀` a finitely generated `A`-algebra, `𝔮` a prime of `C₀`, `C = (C₀)_𝔮`,
`ψ : A[T₁, …, T_r] → C` an `A`-algebra homomorphism and `𝔭 = ψ⁻¹(𝔪_C)`, such that the induced
local homomorphism `g : A[T]_𝔭 → C` is local-étale. Let `φ : C → k` be a local homomorphism to a
field. Then the Henselization `C̃` of `C` with respect to `φ` is isomorphic, as an
`A[T]_𝔭`-algebra and hence as an `A[T]`-algebra, to the Henselization `B̃` of `A[T]_𝔭` with
respect to `φ ∘ g`, compatibly with the maps of both to `k`. -/
@[weil "lem_fk107_local_etale_over_polynomial_strict_henselization"]
theorem exists_ringEquiv_of_isEtaleLocalHom_mvPolynomial {A : Type u} [CommRing A]
    [IsNoetherianRing A] {C₀ : Type v} [CommRing C₀] [Algebra A C₀] [Algebra.FiniteType A C₀]
    (q : Ideal C₀) [q.IsPrime] {r : ℕ}
    (ψ : MvPolynomial (Fin r) A →ₐ[A] Localization.AtPrime q)
    (g : Localization.AtPrime ((maximalIdeal (Localization.AtPrime q)).comap ψ.toRingHom) →+*
      Localization.AtPrime q)
    (hg : g.comp (algebraMap _ _) = ψ.toRingHom)
    (hét : letI := Algebra.FiniteType.isNoetherianRing A C₀
      letI := isLocalHom_of_comp_algebraMap_eq ψ.toRingHom g hg
      g.IsEtaleLocalHom)
    {k : Type w} [Field k] (φ : Localization.AtPrime q →+* k) [IsLocalHom φ]
    {C' : Type w'} [CommRing C'] [IsLocalRing C'] [Algebra (Localization.AtPrime q) C']
    {ψ' : C' →+* k} (hC : IsHenselizationAlong φ C' ψ')
    {B' : Type w''} [CommRing B'] [IsLocalRing B']
    [Algebra (Localization.AtPrime ((maximalIdeal (Localization.AtPrime q)).comap ψ.toRingHom)) B']
    {χ : B' →+* k}
    (hB : letI := isLocalHom_of_comp_algebraMap_eq ψ.toRingHom g hg
      IsHenselizationAlong (φ.comp g) B' χ) :
    ∃ e : B' ≃+* C', (∀ b, e (algebraMap _ B' b) = algebraMap _ C' (g b)) ∧
      (∀ x : MvPolynomial (Fin r) A,
        e (algebraMap _ B' (algebraMap (MvPolynomial (Fin r) A)
          (Localization.AtPrime ((maximalIdeal (Localization.AtPrime q)).comap ψ.toRingHom)) x)) =
          algebraMap _ C' (ψ x)) ∧
      ∀ y, ψ' (e y) = χ y := by
  let B := Localization.AtPrime ((maximalIdeal (Localization.AtPrime q)).comap ψ.toRingHom)
  let C := Localization.AtPrime q
  have : IsNoetherianRing C₀ := Algebra.FiniteType.isNoetherianRing A C₀
  have hgl : IsLocalHom g := isLocalHom_of_comp_algebraMap_eq ψ.toRingHom g hg
  let : Algebra B C := g.toAlgebra
  let : Algebra B C' := ((algebraMap C C').comp g).toAlgebra
  have : IsScalarTower B C C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalHom (algebraMap B C) := hgl
  have hC' : IsHenselizationAlong (φ.comp g) C' ψ' := hC.of_isEtaleLocalHom (B := B) hét
  obtain ⟨e, he⟩ := hB.exists_algEquiv hC'
  have hb : ∀ b, e (algebraMap B B' b) = algebraMap C C' (g b) := fun b => e.commutes b
  refine ⟨e.toRingEquiv, hb, fun x => ?_, he⟩
  change e (algebraMap B B' _) = _
  rw [hb, ← RingHom.comp_apply g, hg]
  rfl

end IsHenselizationAlong

end IsLocalRing
