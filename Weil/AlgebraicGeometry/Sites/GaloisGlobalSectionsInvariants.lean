module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleSheaf
public import Weil.AlgebraicGeometry.Sites.GaloisStalkIndexGaloisCofinal
public import Weil.Defs.AlgebraicGeometry.Sites.GaloisActionOnStalk
public import Weil.RingTheory.Etale.Basic
public import StacksFrontier.FieldTheory.GaloisTensorProduct

/-!
# Global sections of a sheaf on `Et(K)` are the Galois invariants of its Galois stalk

Let `K` be a field, `Ω` a normal extension of `K` (in the source, a separable closure `K̄`),
`G = Aut_K(Ω)`, and `F` a sheaf of abelian groups on the étale category `Et(K)`. The map
`F(K) → F(Ω)`, `s ↦ [s]`, to the Galois stalk is injective, with image the group `F(Ω)^G` of
invariants for the Galois action on `F(Ω)`.

The proof is Galois descent. For `L ∈ Λ_K` and `L ⊆ L'`, the inclusion `L → L'` is faithfully
flat, so the sheaf axiom for faithfully flat morphisms makes `F(L) → F(L')` injective; passing to
the colimit, every `F(L) → F(Ω)` is injective. If `L / K` is Galois with group `H`, the
`K`-algebra `L ⊗_K L` is identified with `∏_{h ∈ H} L` by `a ⊗ b ↦ (a h(b))_h`; by the sheaf axiom
for finite products a section `s ∈ F(L)` fixed by every `F(h)` has the same image under the two
maps `F(L) → F(L ⊗_K L)`, hence `F(u)(s) = F(v)(s)` for every pair `u, v : L ⟶ D` of `Et(K)`,
and so `s` comes from `F(K)`. Finally an invariant element of `F(Ω)` is `[t]` with `t ∈ F(L)`,
`L / K` finite Galois; each `h ∈ Gal(L/K)` extends to `σ ∈ G`, and injectivity of
`F(L) → F(Ω)` makes `t` fixed by `Gal(L/K)`.

## Main results

- `AlgebraicGeometry.EtaleCategory.injective_galoisStalkι_bot`: `F(K) → F(Ω)` is injective.
- `AlgebraicGeometry.EtaleCategory.range_galoisStalkι_bot`: its image is `F(Ω)^G`.
- `AlgebraicGeometry.EtaleCategory.injective_galoisStalkι`: `F(L) → F(Ω)` is injective for every
  `L ∈ Λ_K`.
- `AlgebraicGeometry.EtaleCategory.map_eq_map_of_forall_map_etaleHom_eq`: for `L / K` Galois,
  a section of `F(L)` fixed by `Gal(L/K)` is equalised by every pair of morphisms out of `L`.

## Implementation notes

The object `K` of `Et(K)` is taken as the element `GaloisStalkIndex.bot` of `Λ_K`, the bottom
intermediate field `K ⊆ Ω`; this is how `F(K) → F(Ω)` is an instance of `s ↦ [s]`. The
statement holds for every normal extension `Ω` of `K`, not only a separable closure: the
elements of `Λ_K` are the finite separable subextensions of `Ω`, and normality is what lets an
automorphism of a finite Galois subextension extend to `Ω`. Injectivity needs no hypothesis on
`Ω`. The identification `L ⊗_K L ≅ ∏_{h} L` is `IsGalois.bijective_tensorProductPi`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
-/

public section

noncomputable section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

namespace EtaleCategory

open GaloisStalkIndex

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The morphism of `Et(K)` given by a `K`-algebra map of étale `K`-algebras. -/
abbrev homOfAlgHom {B C : (IsEtaleAlgebra (CommRingCat.of K)).FullSubcategory}
    (f : B.obj →ₐ[K] C.obj) : ofAlgebra _ B ⟶ ofAlgebra _ C :=
  (fromAlgebras (CommRingCat.of K)).map (ObjectProperty.homMk (CommAlgCat.ofHom f))

/-- A ring homomorphism between fields is faithfully flat. -/
private lemma faithfullyFlat_of_field {L L' : Type u} [Field L] [Field L'] (f : L →+* L') :
    f.FaithfullyFlat := by
  let := f.toAlgebra
  change (algebraMap L L').FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

variable (F : Presheaf (CommRingCat.of K) AddCommGrpCat.{u})

/-- Restriction `F(L) → F(L')` along an inclusion `L ⊆ L'` in `Λ_K` is injective. -/
lemma injective_map_toEtaleCategory_map
    (hF : IsSheafAxioms (F ⋙ forget AddCommGrpCat)) {L L' : GaloisStalkIndex K Ω} (h : L ⟶ L') :
    Function.Injective (F.map ((toEtaleCategory K Ω).map h)) :=
  hF.injective_of_faithfullyFlat ((toEtaleCategory K Ω).map h)
    (faithfullyFlat_of_field (IntermediateField.inclusion (le_iff.mp h.le)).toRingHom :)

/-- For every `L ∈ Λ_K`, the map `F(L) → F(Ω)`, `s ↦ [s]`, is injective. -/
lemma injective_galoisStalkι (hF : IsSheafAxioms (F ⋙ forget AddCommGrpCat))
    (L : GaloisStalkIndex K Ω) : Function.Injective (galoisStalkι Ω F L) := by
  refine (injective_iff_map_eq_zero (galoisStalkι Ω F L).hom).mpr fun s hs ↦ ?_
  obtain ⟨L', h, h0⟩ := (galoisStalkι_eq_zero_iff Ω F s).mp hs
  exact injective_map_toEtaleCategory_map F hF h (h0.trans (map_zero _).symm)

/-- Let `L ∈ Λ_K` be Galois over `K` and `s ∈ F(L)` fixed by `F(h)` for every `h ∈ Gal(L/K)`.
Then `F(u)(s) = F(v)(s)` for every pair of morphisms `u v : L ⟶ D` of `Et(K)`. -/
lemma map_eq_map_of_forall_map_etaleHom_eq (hF : IsSheafAxioms (F ⋙ forget AddCommGrpCat))
    (L : GaloisStalkIndex K Ω) [IsGalois K L.field] (s : F.obj ((toEtaleCategory K Ω).obj L))
    (hs : ∀ h : L.field ≃ₐ[K] L.field, F.map (etaleHom h.toAlgHom) s = s)
    {D : EtaleCategory (CommRingCat.of K)} (u v : (toEtaleCategory K Ω).obj L ⟶ D) :
    F.map u s = F.map v s := by
  classical
  suffices H : ∀ (B : (IsEtaleAlgebra (CommRingCat.of K)).FullSubcategory)
      (u v : (toEtaleCategory K Ω).obj L ⟶ ofAlgebra _ B), F.map u s = F.map v s by
    let e := ofAlgebraToAlgebraIso D
    obtain ⟨u', rfl⟩ : ∃ u', u = u' ≫ e.hom := ⟨u ≫ e.inv, by simp⟩
    obtain ⟨v', rfl⟩ : ∃ v', v = v' ≫ e.hom := ⟨v ≫ e.inv, by simp⟩
    rw [F.map_comp, F.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      H _ u' v']
  intro B u v
  let M := L.field
  let T : (IsEtaleAlgebra (CommRingCat.of K)).FullSubcategory :=
    ⟨CommAlgCat.of K (M ⊗[K] M), Algebra.Etale.tensorProduct K M M⟩
  let i₁ : (toEtaleCategory K Ω).obj L ⟶ ofAlgebra _ T :=
    homOfAlgHom (B := GaloisStalkIndex.toAlgebra K L) (C := T) Algebra.TensorProduct.includeLeft
  let i₂ : (toEtaleCategory K Ω).obj L ⟶ ofAlgebra _ T :=
    homOfAlgHom (B := GaloisStalkIndex.toAlgebra K L) (C := T) Algebra.TensorProduct.includeRight
  let w : ofAlgebra _ T ⟶ ofAlgebra _ B := homOfAlgHom (B := T) (C := B)
    (Algebra.TensorProduct.lift (algHomOfHom u) (algHomOfHom v) fun _ _ ↦ Commute.all _ _)
  have hu : u = i₁ ≫ w := by
    refine hom_ext ?_
    ext x
    change algHomOfHom u x = algHomOfHom u x * algHomOfHom v 1
    simp
  have hv : v = i₂ ≫ w := by
    refine hom_ext ?_
    ext x
    change algHomOfHom v x = algHomOfHom u 1 * algHomOfHom v x
    simp
  let θ : (M ≃ₐ[K] M) → (ofAlgebra _ T ⟶ (toEtaleCategory K Ω).obj L) := fun h ↦
    homOfAlgHom (B := T) (C := GaloisStalkIndex.toAlgebra K L)
      ((IsGalois.tensorEvalAlgHom h).restrictScalars K)
  have h₁ : ∀ h, i₁ ≫ θ h = 𝟙 _ := fun h ↦ by
    refine hom_ext ?_
    ext x
    change IsGalois.tensorEvalAlgHom h ((show M from x) ⊗ₜ[K] 1) = (show M from x)
    rw [IsGalois.tensorEvalAlgHom_tmul, _root_.map_one, mul_one]
  have h₂ : ∀ h : M ≃ₐ[K] M, i₂ ≫ θ h = etaleHom h.toAlgHom := fun h ↦ by
    refine hom_ext ?_
    ext x
    change IsGalois.tensorEvalAlgHom h (1 ⊗ₜ[K] (show M from x)) = h (show M from x)
    rw [IsGalois.tensorEvalAlgHom_tmul, one_mul]
  let e := Finite.equivFin (M ≃ₐ[K] M)
  have hbij := hF.bijective_pi (fun _ ↦ (toEtaleCategory K Ω).obj L) (ofAlgebra _ T)
    (fun k ↦ θ (e.symm k))
    ((Equiv.arrowCongr e (Equiv.refl M)).bijective.comp (IsGalois.bijective_tensorProductPi K M))
  have key : F.map i₁ s = F.map i₂ s := by
    refine hbij.1 (funext fun k ↦ ?_)
    change F.map (θ (e.symm k)) (F.map i₁ s) = F.map (θ (e.symm k)) (F.map i₂ s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp,
      ← F.map_comp, h₁, h₂, F.map_id, hs]
    rfl
  rw [hu, hv, F.map_comp, F.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    key]

/-- Two `K`-algebra maps out of the bottom intermediate field `K ⊆ Ω` agree. -/
lemma algHom_bot_ext {E : Type*} [Ring E] [Algebra K E]
    (f g : (⊥ : IntermediateField K Ω) →ₐ[K] E) : f = g := by
  ext x
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp x.2
  have hx : x = algebraMap K _ r := Subtype.ext hr.symm
  rw [hx, f.commutes, g.commutes]

/-- If `σ L ⊆ L`, then `σ · [t] = [F(σ|_L)(t)]`, where `σ|_L : L → L` is the restriction
of `σ`. -/
lemma galoisStalkAction_galoisStalkι_of_map_le (σ : Ω ≃ₐ[K] Ω) {L : GaloisStalkIndex K Ω}
    (hle : map σ L ≤ L) (t : F.obj ((toEtaleCategory K Ω).obj L)) :
    galoisStalkAction σ F (galoisStalkι Ω F L t) =
      galoisStalkι Ω F L (F.map (etaleHom
        ((IntermediateField.inclusion (le_iff.mp hle)).comp (restrict σ L).toAlgHom)) t) := by
  have h : F.map (restrictHom σ L) ≫ F.map ((toEtaleCategory K Ω).map (homOfLE hle)) =
      F.map (etaleHom
        ((IntermediateField.inclusion (le_iff.mp hle)).comp (restrict σ L).toAlgHom)) := by
    rw [← F.map_comp, restrictHom, toEtaleCategory_map_eq_etaleHom, etaleHom_comp]
  rw [galoisStalkAction_galoisStalkι_apply, ← map_galoisStalkι Ω F (homOfLE hle), ← h]
  rfl

/-- The element `K` of `Λ_K`: the bottom intermediate field `K ⊆ Ω`. -/
abbrev GaloisStalkIndex.bot : GaloisStalkIndex K Ω := ofIsSeparable ⊥

lemma GaloisStalkIndex.bot_le (L : GaloisStalkIndex K Ω) : GaloisStalkIndex.bot ≤ L :=
  le_iff.mpr _root_.bot_le

/-- **Galois descent for global sections, injectivity** [FK, I.1]. For a sheaf of abelian groups
`F` on `Et(K)`, the map `F(K) → F(Ω)`, `s ↦ [s]`, is injective. -/
@[weil "lem_fk101_galois_global_sections_invariants"]
theorem injective_galoisStalkι_bot
    (hF : Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of K))) F) :
    Function.Injective (galoisStalkι Ω F GaloisStalkIndex.bot) :=
  injective_galoisStalkι F ((isSheaf_iff_isSheafAxioms_forget F).mp hF) _

/-- **Galois descent for global sections, image** [FK, I.1]. For a sheaf of abelian groups `F` on
`Et(K)` and a normal extension `Ω / K` (e.g. a separable closure), the image of
`F(K) → F(Ω)`, `s ↦ [s]`, is the group `F(Ω)^G` of invariants of `G = Aut_K(Ω)`. -/
@[weil "lem_fk101_galois_global_sections_invariants"]
theorem range_galoisStalkι_bot [Normal K Ω]
    (hF : Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of K))) F) :
    Set.range (galoisStalkι Ω F GaloisStalkIndex.bot) =
      {x | ∀ σ : Ω ≃ₐ[K] Ω, galoisStalkAction σ F x = x} := by
  have hA := (isSheaf_iff_isSheafAxioms_forget F).mp hF
  ext x
  constructor
  · rintro ⟨s, rfl⟩ σ
    have hle : map σ (GaloisStalkIndex.bot : GaloisStalkIndex K Ω) ≤ GaloisStalkIndex.bot :=
      le_iff.mpr (by rw [field_map]; exact (IntermediateField.map_bot _).le)
    have hid : (IntermediateField.inclusion (le_iff.mp hle)).comp
        (restrict σ (GaloisStalkIndex.bot : GaloisStalkIndex K Ω)).toAlgHom = AlgHom.id K _ :=
      algHom_bot_ext _ _
    rw [galoisStalkAction_galoisStalkι_of_map_le F σ hle, hid, etaleHom_id, F.map_id]
    rfl
  · intro hx
    obtain ⟨L₀, t₀, rfl⟩ := galoisStalk_exists_rep Ω F x
    obtain ⟨L, hGal, hL₀, -⟩ := exists_isGalois_le L₀ L₀
    let t := F.map ((toEtaleCategory K Ω).map (homOfLE hL₀)) t₀
    have ht : galoisStalkι Ω F L₀ t₀ = galoisStalkι Ω F L t := by
      rw [← map_galoisStalkι Ω F (homOfLE hL₀), ConcreteCategory.comp_apply]
    rw [ht] at hx ⊢
    have hfix : ∀ h : L.field ≃ₐ[K] L.field, F.map (etaleHom h.toAlgHom) t = t := by
      intro h
      let σ : Ω ≃ₐ[K] Ω := h.liftNormal Ω
      have hσ (z : L.field) : σ z = h z := AlgEquiv.liftNormal_commutes h Ω z
      have hle : map σ L ≤ L := by
        refine le_iff.mpr fun y hy ↦ ?_
        obtain ⟨z, hz, rfl⟩ := mem_map_field.mp hy
        rw [hσ ⟨z, hz⟩]
        exact (h ⟨z, hz⟩).2
      have hh : (IntermediateField.inclusion (le_iff.mp hle)).comp (restrict σ L).toAlgHom =
          h.toAlgHom := AlgHom.ext fun z ↦ Subtype.ext (hσ z)
      apply injective_galoisStalkι F hA L
      rw [← hx σ, galoisStalkAction_galoisStalkι_of_map_le F σ hle, hh]
    have hbot : (GaloisStalkIndex.bot : GaloisStalkIndex K Ω) ≤ L := GaloisStalkIndex.bot_le L
    let g := (toEtaleCategory K Ω).map (homOfLE hbot)
    have hmem : t ∈ Set.range ((F ⋙ forget AddCommGrpCat).map g) := by
      rw [hA.range_of_faithfullyFlat g
        (faithfullyFlat_of_field (IntermediateField.inclusion (le_iff.mp hbot)).toRingHom :)]
      intro D u v _
      exact map_eq_map_of_forall_map_etaleHom_eq F hA L t hfix u v
    obtain ⟨s, hs⟩ := hmem
    refine ⟨s, ?_⟩
    rw [← map_galoisStalkι Ω F (homOfLE hbot), ConcreteCategory.comp_apply]
    exact congrArg _ hs

end EtaleCategory

end AlgebraicGeometry
