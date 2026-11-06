module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Complex.Basic
public import Weil.Defs.AlgebraicGeometry.ComplexPoints.AnalyticTopology
public import Weil.Attr

/-!
# Functoriality of the analytic topology on complex points

Let `Y` be a scheme over `ℂ`. The complex points `Y(ℂ)` carry the analytic topology, the
coarsest topology for which every `U(ℂ)`, `U` an affine open, is open and every regular function
on `U` is continuous on `U(ℂ)`. This file develops its basic properties.

For an affine open `U` of `Y`, the points of `U(ℂ)` are exactly the ring homomorphisms
`Γ(Y, U) → ℂ` which are the identity on constants, and the analytic topology of `U(ℂ)` is the
one induced by the evaluations of all regular functions: `p ↦ (g(p))_g` is a closed embedding of
`U(ℂ)` into `ℂ^{Γ(Y, U)}`. If `ℂ[x_i : i ∈ ι] ↠ Γ(Y, U)`, `x_i ↦ s_i`, is a presentation, then
`p ↦ (s_i(p))_i` is a homeomorphism of `U(ℂ)` onto the common zeros in `ℂ^ι` of the relations.
In particular every regular function on any open `U` is continuous on `U(ℂ)`.

A morphism `f : Y ⟶ Y'` over `ℂ` induces a continuous map `Y(ℂ) → Y'(ℂ)`, functorially. An open
immersion induces an open embedding onto the points of its image, and a closed immersion a
closed embedding.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.evalHom`: evaluation at a point as a ring
  homomorphism.
* `AlgebraicGeometry.Scheme.ComplexPoints.constHom`: the constants `ℂ → Γ(Y, U)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.ofRingHom`: the point of an affine open attached to a
  ring homomorphism `Γ(Y, U) → ℂ` over `ℂ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.evalMap`: the coordinates `U(ℂ) → ℂ^{Γ(Y, U)}`.
* `AlgebraicGeometry.Scheme.ComplexPoints.map`: the map on complex points induced by a morphism.
* `AlgebraicGeometry.Scheme.ComplexPoints.homeomorphZeroLocus`: `U(ℂ)` is homeomorphic to the
  zero set of the relations of a presentation of `Γ(Y, U)`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.range_evalMap`,
  `AlgebraicGeometry.Scheme.ComplexPoints.isClosedEmbedding_evalMap`: the affine coordinates.
* `AlgebraicGeometry.Scheme.ComplexPoints.isClosedEmbedding_coords`: coordinates from a
  presentation.
* `AlgebraicGeometry.Scheme.ComplexPoints.continuous_eval_of_isOpen`: regular functions on any
  open are continuous.
* `AlgebraicGeometry.Scheme.ComplexPoints.continuous_map`, `map_id`, `map_comp`: functoriality.
* `AlgebraicGeometry.Scheme.ComplexPoints.isOpenEmbedding_map_of_isOpenImmersion`.
* `AlgebraicGeometry.Scheme.ComplexPoints.isClosedEmbedding_map_of_isClosedImmersion`.

## Implementation notes

The constants are the ring homomorphism `constHom U : ℂ → Γ(Y, U)` coming from the structure
morphism, rather than an `Algebra ℂ Γ(Y, U)` instance, so that no instance on the rings of
sections is introduced. Presentations are stated for an arbitrary affine open `U` and a family
`s : ι → Γ(Y, U)`; the case of `Y = Spec A` with `A` of finite type is `U = ⊤`, `ι = Fin n`
(`homeomorphZeroLocusOfIsAffine`).

## References

* [SGA1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exposé XII, §1.
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-! ### Evaluation of regular functions -/

theorem Mem.mono {p : ComplexPoints y} {U V : Y.Opens} (h : V ≤ U) (hp : p.Mem V) : p.Mem U :=
  eq_top_iff.2 (hp.ge.trans (p.hom.preimage_mono h))

theorem mem_top (p : ComplexPoints y) : p.Mem ⊤ := p.hom.preimage_top

/-- Evaluation at a complex point `p ∈ U(ℂ)` as a ring homomorphism `Γ(Y, U) → ℂ`. -/
noncomputable def evalHom {U : Y.Opens} (p : ComplexPoints y) (hp : p.Mem U) : Γ(Y, U) →+* ℂ :=
  (p.hom.appLE U ⊤ hp.ge ≫ (Scheme.ΓSpecIso (.of ℂ)).hom).hom

@[simp]
theorem evalHom_apply {U : Y.Opens} (p : ComplexPoints y) (hp : p.Mem U) (g : Γ(Y, U)) :
    evalHom p hp g = eval g p hp := rfl

/-- Evaluation is compatible with restriction of regular functions. -/
theorem eval_map {U V : Y.Opens} (h : V ≤ U) (g : Γ(Y, U)) (p : ComplexPoints y) (hp : p.Mem V) :
    eval (Y.presheaf.map (homOfLE h).op g) p hp = eval g p (hp.mono h) := by
  have := Scheme.Hom.map_appLE p.hom (U := V) (U' := U) (V := ⊤) hp.ge (homOfLE h).op
  simp only [eval]
  rw [← this]
  rfl

/-- The constants `ℂ → Γ(Y, U)`, through the structure morphism `y`. -/
noncomputable def constHom (U : Y.Opens) : ℂ →+* Γ(Y, U) :=
  ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ y.appLE ⊤ U (by simp)).hom

/-- Constants restrict to constants. -/
@[simp]
theorem map_constHom {U V : Y.Opens} (h : V ≤ U) (c : ℂ) :
    Y.presheaf.map (homOfLE h).op (constHom (y := y) U c) = constHom (y := y) V c := by
  simp only [constHom]
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

/-- A constant takes its own value at every complex point. -/
@[simp]
theorem eval_constHom {U : Y.Opens} (c : ℂ) (p : ComplexPoints y) (hp : p.Mem U) :
    eval (constHom (y := y) U c) p hp = c := by
  have key : ∀ (f : Spec (.of ℂ) ⟶ Spec (.of ℂ)) (_ : f = 𝟙 _) (e : ⊤ ≤ f ⁻¹ᵁ ⊤),
      f.appLE ⊤ ⊤ e = 𝟙 _ := by
    rintro _ rfl e
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Spec _).presheaf.map_id (Opposite.op ⊤)
  simp only [eval, constHom]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc,
    Scheme.Hom.appLE_comp_appLE_assoc, key _ p.hom_comp, Category.id_comp]
  simp


/-- A global function on `Spec ℂ` is invertible everywhere iff it is nonzero. -/
theorem basicOpen_eq_top_iff_ne_zero (r : Γ(Spec (.of ℂ), ⊤)) :
    (Spec (.of ℂ)).basicOpen r = ⊤ ↔ (Scheme.ΓSpecIso (.of ℂ)).hom r ≠ 0 := by
  constructor
  · intro h h0
    have hr : r = 0 := by
      rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of ℂ)) r, h0, map_zero]
    rw [hr, Scheme.basicOpen_zero] at h
    obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
    exact (show x ∈ (⊥ : (Spec (.of ℂ)).Opens) from h ▸ trivial)
  · intro h
    apply Scheme.basicOpen_of_isUnit
    have hu : IsUnit ((Scheme.ΓSpecIso (.of ℂ)).hom r) := Ne.isUnit h
    have := hu.map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this

/-- `p ∈ D(g)(ℂ)` iff `g(p) ≠ 0`. -/
theorem mem_basicOpen_iff {U : Y.Opens} {g : Γ(Y, U)} {p : ComplexPoints y} (hp : p.Mem U) :
    p.Mem (Y.basicOpen g) ↔ eval g p hp ≠ 0 := by
  rw [eval, ← basicOpen_eq_top_iff_ne_zero, Mem, Scheme.Hom.preimage_basicOpen]
  change _ ↔ (Spec (.of ℂ)).basicOpen ((Spec (.of ℂ)).presheaf.map (homOfLE hp.ge).op
    (p.hom.app U g)) = ⊤
  rw [Scheme.basicOpen_res, top_inf_eq]

/-- The evaluations of a regular function at a point determine the point's appLE. -/
theorem appLE_eq_of_evalHom_eq {U : Y.Opens} {p q : ComplexPoints y} (hp : p.Mem U)
    (hq : q.Mem U) (h : evalHom p hp = evalHom q hq) :
    p.hom.appLE U ⊤ hp.ge = q.hom.appLE U ⊤ hq.ge := by
  rw [← cancel_mono (Scheme.ΓSpecIso (.of ℂ)).hom]
  exact CommRingCat.hom_ext h

/-- A morphism `Spec ℂ ⟶ Y` landing in an affine open `U` is determined by its pullback map on
`Γ(Y, U)`. -/
theorem hom_eq_of_appLE_eq {U : Y.Opens} (hU : IsAffineOpen U) {f g : Spec (.of ℂ) ⟶ Y}
    (hf : ⊤ ≤ f ⁻¹ᵁ U) (hg : ⊤ ≤ g ⁻¹ᵁ U) (h : f.appLE U ⊤ hf = g.appLE U ⊤ hg) : f = g := by
  have hV := isAffineOpen_top (Spec (.of ℂ))
  have : IsIso (⊤ : (Spec (.of ℂ)).Opens).ι := inferInstanceAs (IsIso (Scheme.topIso _).hom)
  have : IsIso hV.fromSpec := by rw [← hV.isoSpec_inv_ι]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hf,
    ← IsAffineOpen.SpecMap_appLE_fromSpec g hU hV hg, h]

/-- **Points of an affine open are determined by their evaluations.** -/
theorem eq_of_evalHom_eq {U : Y.Opens} (hU : IsAffineOpen U) {p q : ComplexPoints y}
    (hp : p.Mem U) (hq : q.Mem U) (h : evalHom p hp = evalHom q hq) : p = q :=
  ext (hom_eq_of_appLE_eq hU hp.ge hq.ge (appLE_eq_of_evalHom_eq hp hq h))

theorem eq_of_eval_eq {U : Y.Opens} (hU : IsAffineOpen U) {p q : ComplexPoints y}
    (hp : p.Mem U) (hq : q.Mem U) (h : ∀ g : Γ(Y, U), eval g p hp = eval g q hq) : p = q :=
  eq_of_evalHom_eq hU hp hq (RingHom.ext h)

section OfRingHom

variable {U : Y.Opens} (hU : IsAffineOpen U) (φ : Γ(Y, U) →+* ℂ)

/-- The morphism `Spec ℂ ⟶ Y` attached to a ring homomorphism `φ : Γ(Y, U) → ℂ`, `U` affine. -/
noncomputable def homOfRingHom : Spec (.of ℂ) ⟶ Y :=
  Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec

theorem le_preimage_homOfRingHom : ⊤ ≤ homOfRingHom hU φ ⁻¹ᵁ U := by
  simp [homOfRingHom, hU.fromSpec_preimage_self]

theorem fromSpec_appLE_top :
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE hU.fromSpec_preimage_self.ge).op :
      Opposite.op (⊤ : (Spec Γ(Y, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_top_top_eq_appTop {R S : CommRingCat} (f : Spec R ⟶ Spec S) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  simp only [Scheme.Hom.appLE]
  exact Category.comp_id _

theorem ΓSpecIso_appLE_homOfRingHom (e : ⊤ ≤ homOfRingHom hU φ ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (Scheme.ΓSpecIso (.of ℂ)).hom ((homOfRingHom hU φ).appLE U ⊤ e g) = φ g := by
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ e g) = φ g
  rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ hU.fromSpec_preimage_self.ge
    (Spec.map (CommRingCat.ofHom φ)).preimage_top.ge, fromSpec_appLE_top, appLE_top_top_eq_appTop,
    ← CommRingCat.comp_apply,
    Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc]
  erw [Iso.inv_hom_id]
  rfl

variable {φ}

theorem homOfRingHom_comp (hφ : ∀ c, φ (constHom (y := y) U c) = c) :
    homOfRingHom hU φ ≫ y = 𝟙 _ := by
  have e := le_preimage_homOfRingHom hU φ
  have key : ∀ z, (Scheme.ΓSpecIso (.of ℂ)).hom ((homOfRingHom hU φ ≫ y).appTop z) =
      (Scheme.ΓSpecIso (.of ℂ)).hom z := by
    intro z
    have h1 := ΓSpecIso_appLE_homOfRingHom hU φ e (constHom (y := y) U ((Scheme.ΓSpecIso _).hom z))
    rw [hφ] at h1
    rw [← h1]
    congr 1
    simp only [constHom]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc,
      Scheme.Hom.appLE_comp_appLE, appLE_top_top_eq_appTop, ← Category.assoc]
    erw [Iso.hom_inv_id]
    rfl
  apply ext_of_isAffine
  ext z
  apply (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.injective
  exact key z

/-- The complex point of `U` attached to a ring homomorphism `φ : Γ(Y, U) → ℂ` that is the
identity on constants, `U` affine. -/
noncomputable def ofRingHom (hφ : ∀ c, φ (constHom (y := y) U c) = c) : ComplexPoints y :=
  ⟨homOfRingHom hU φ, homOfRingHom_comp hU hφ⟩

theorem ofRingHom_mem (hφ : ∀ c, φ (constHom (y := y) U c) = c) : (ofRingHom hU hφ).Mem U :=
  top_le_iff.1 (le_preimage_homOfRingHom hU φ)

@[simp]
theorem eval_ofRingHom (hφ : ∀ c, φ (constHom (y := y) U c) = c) (g : Γ(Y, U))
    (h : (ofRingHom hU hφ).Mem U) : eval g (ofRingHom hU hφ) h = φ g :=
  ΓSpecIso_appLE_homOfRingHom hU φ h.ge g

end OfRingHom


section EvalAlgebra

variable {U : Y.Opens} (p : ComplexPoints y) (hp : p.Mem U)

@[simp] theorem eval_mul (g h : Γ(Y, U)) : eval (g * h) p hp = eval g p hp * eval h p hp :=
  map_mul (evalHom p hp) g h

@[simp] theorem eval_add (g h : Γ(Y, U)) : eval (g + h) p hp = eval g p hp + eval h p hp :=
  map_add (evalHom p hp) g h

@[simp] theorem eval_one : eval (1 : Γ(Y, U)) p hp = 1 := map_one (evalHom p hp)

@[simp] theorem eval_zero : eval (0 : Γ(Y, U)) p hp = 0 := map_zero (evalHom p hp)

@[simp] theorem eval_pow (g : Γ(Y, U)) (k : ℕ) : eval (g ^ k) p hp = eval g p hp ^ k :=
  map_pow (evalHom p hp) g k

end EvalAlgebra

/-! ### The affine coordinates -/

/-- The evaluation of all regular functions on `U` at points of `U(ℂ)`. -/
noncomputable def evalMap (U : Y.Opens) : {p : ComplexPoints y // p.Mem U} → (Γ(Y, U) → ℂ) :=
  fun p g => eval g p.1 p.2

/-- The functions `Γ(Y, U) → ℂ` which are ring homomorphisms and the identity on constants. -/
def ringHomSet (y : Y ⟶ Spec (.of ℂ)) (U : Y.Opens) : Set (Γ(Y, U) → ℂ) :=
  {φ | φ 1 = 1 ∧ (∀ a b, φ (a * b) = φ a * φ b) ∧ (∀ a b, φ (a + b) = φ a + φ b) ∧
    ∀ c, φ (constHom (y := y) U c) = c}

theorem isClosed_ringHomSet (U : Y.Opens) : IsClosed (ringHomSet y U) := by
  have : ringHomSet y U = {φ | φ 1 = 1} ∩ ((⋂ a, ⋂ b, {φ | φ (a * b) = φ a * φ b}) ∩
      ((⋂ a, ⋂ b, {φ | φ (a + b) = φ a + φ b}) ∩ ⋂ c, {φ | φ (constHom (y := y) U c) = c})) := by
    ext φ
    simp only [ringHomSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine (isClosed_eq (continuous_apply _) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b => ?_).inter
      ((isClosed_iInter fun a => isClosed_iInter fun b => ?_).inter
        (isClosed_iInter fun c => isClosed_eq (continuous_apply _) continuous_const)))
  · exact isClosed_eq (continuous_apply _) ((continuous_apply a).mul (continuous_apply b))
  · exact isClosed_eq (continuous_apply _) ((continuous_apply a).add (continuous_apply b))

variable {U : Y.Opens}

theorem continuous_evalMap (hU : IsAffineOpen U) : Continuous (evalMap (y := y) U) :=
  continuous_pi fun g => continuous_eval hU g

theorem injective_evalMap (hU : IsAffineOpen U) : Function.Injective (evalMap (y := y) U) :=
  fun p q h => Subtype.ext (eq_of_eval_eq hU p.2 q.2 fun g => congrFun h g)

/-- **The points of an affine open `U` are the ring homomorphisms `Γ(Y, U) → ℂ` over `ℂ`.** -/
theorem range_evalMap (hU : IsAffineOpen U) : Set.range (evalMap (y := y) U) = ringHomSet y U := by
  ext φ
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨eval_one _ _, fun a b => eval_mul _ _ a b, fun a b => eval_add _ _ a b,
      fun c => eval_constHom c _ _⟩
  · rintro ⟨h1, hmul, hadd, hc⟩
    let ψ : Γ(Y, U) →+* ℂ :=
      { toFun := φ
        map_one' := h1
        map_mul' := hmul
        map_zero' := by
          have := hadd 0 0
          rw [add_zero] at this
          exact left_eq_add.1 this
        map_add' := hadd }
    exact ⟨⟨ofRingHom hU (φ := ψ) hc, ofRingHom_mem hU hc⟩,
      funext fun g => eval_ofRingHom hU hc g _⟩

/-- **The analytic topology on an affine open is induced by the regular functions.** -/
theorem isInducing_evalMap (hU : IsAffineOpen U) : IsInducing (evalMap (y := y) U) := by
  rw [isInducing_iff]
  refine le_antisymm (continuous_iff_le_induced.1 (continuous_evalMap hU)) ?_
  change _ ≤ TopologicalSpace.induced Subtype.val (TopologicalSpace.generateFrom (basicSets y))
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  rintro _ ⟨_, ⟨U', -, g, V, hV, rfl⟩, rfl⟩
  let t := TopologicalSpace.induced (evalMap (y := y) U) inferInstance
  rw [@isOpen_iff_forall_mem_open _ t]
  rintro p ⟨hp', hpV⟩
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨f, hle, hxf⟩ := hU.exists_basicOpen_le ⟨p.1.hom.base pt, (mem_iff pt).1 hp'⟩
    ((mem_iff pt).1 p.2)
  have hpf : p.1.Mem (Y.basicOpen f) := (mem_iff pt).2 hxf
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨a, ⟨s, k, rfl⟩⟩, hgs⟩ :=
    IsLocalization.surj (Submonoid.powers f) (Y.presheaf.map (homOfLE hle).op g)
  have key : ∀ (q : {p : ComplexPoints y // p.Mem U}) (hq : q.1.Mem (Y.basicOpen f)),
      eval g q.1 (hq.mono hle) * eval (f ^ k) q.1 q.2 = eval a q.1 q.2 := by
    intro q hq
    have := congrArg (fun z => eval z q.1 hq) hgs
    simp only [eval_mul] at this
    rw [eval_map] at this
    erw [eval_map, eval_map] at this
    exact this
  let T : Set (Γ(Y, U) → ℂ) :=
    {φ | φ f ≠ 0} ∩ ({φ | φ (f ^ k) ≠ 0} ∩ (fun φ => φ a / φ (f ^ k)) ⁻¹' V)
  have hT : IsOpen T := by
    refine (isOpen_ne_fun (continuous_apply _) continuous_const).inter ?_
    refine ContinuousOn.isOpen_inter_preimage ?_
      (isOpen_ne_fun (continuous_apply _) continuous_const) hV
    exact (continuous_apply a).continuousOn.div (continuous_apply _).continuousOn fun φ h => h
  refine ⟨evalMap U ⁻¹' T, ?_, isOpen_induced hT, ?_⟩
  · rintro q ⟨hqf, hqs, hqV⟩
    have hq : q.1.Mem (Y.basicOpen f) := (mem_basicOpen_iff q.2).2 hqf
    refine ⟨hq.mono hle, ?_⟩
    have := key q hq
    change eval a q.1 q.2 / eval (f ^ k) q.1 q.2 ∈ V at hqV
    rwa [← this, mul_div_cancel_right₀ _ (show eval (f ^ k) q.1 q.2 ≠ 0 from hqs)] at hqV
  · have hf0 : eval f p.1 p.2 ≠ 0 := (mem_basicOpen_iff p.2).1 hpf
    have hs0 : eval (f ^ k) p.1 p.2 ≠ 0 := by rw [eval_pow]; exact pow_ne_zero _ hf0
    refine ⟨hf0, hs0, ?_⟩
    change eval a p.1 p.2 / eval (f ^ k) p.1 p.2 ∈ V
    rwa [← key p hpf, mul_div_cancel_right₀ _ hs0]

/-- **The coordinates of an affine open.** For `U` an affine open of `Y`, the evaluation of the
regular functions on `U` is a closed embedding of `U(ℂ)` into `ℂ^{Γ(Y, U)}`, with image the
ring homomorphisms over `ℂ`. -/
theorem isClosedEmbedding_evalMap (hU : IsAffineOpen U) :
    IsClosedEmbedding (evalMap (y := y) U) :=
  ⟨⟨isInducing_evalMap hU, injective_evalMap hU⟩, by
    rw [range_evalMap hU]; exact isClosed_ringHomSet U⟩


/-! ### Regular functions on arbitrary opens -/

/-- A regular function `g` on an arbitrary open `U` is continuous on `U(ℂ)`. -/
theorem continuous_eval_of_isOpen (U : Y.Opens) (g : Γ(Y, U)) :
    Continuous fun p : {p : ComplexPoints y // p.Mem U} => eval g p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) ((mem_iff pt).1 p.2)
  have hO : IsOpen {q : {p : ComplexPoints y // p.Mem U} | q.1.Mem V} :=
    (isOpen_setOf_mem V).preimage continuous_subtype_val
  have hpV : p.1.Mem V := (mem_iff pt).2 hxV
  refine ContinuousOn.continuousAt ?_ (hO.mem_nhds hpV)
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := (continuous_eval hV (Y.presheaf.map (homOfLE hVU).op g)).comp
    (show Continuous fun q : {q : {p : ComplexPoints y // p.Mem U} // q.1.Mem V} =>
      (⟨q.1.1, q.2⟩ : {p : ComplexPoints y // p.Mem V}) from
      continuous_subtype_val.subtype_val.subtype_mk _)
  exact hc.congr fun q => eval_map hVU g q.1.1 q.2

/-- `{p ∈ U(ℂ) | g(p) ∈ V}` is open for every open `U`, not only for affine ones. -/
theorem isOpen_basicSet_of_isOpen (U : Y.Opens) (g : Γ(Y, U)) {V : Set ℂ} (hV : IsOpen V) :
    IsOpen (basicSet (y := y) U g V) := by
  have : basicSet (y := y) U g V =
      Subtype.val '' ((fun p : {p : ComplexPoints y // p.Mem U} => eval g p.1 p.2) ⁻¹' V) := by
    ext p
    exact ⟨fun ⟨hp, h⟩ => ⟨⟨p, hp⟩, h, rfl⟩, fun ⟨q, hq, e⟩ => e ▸ ⟨q.2, hq⟩⟩
  rw [this]
  exact (isOpen_setOf_mem U).isOpenMap_subtype_val _
    (hV.preimage (continuous_eval_of_isOpen U g))

/-! ### Functoriality -/

variable {Y' : Scheme.{0}} {y' : Y' ⟶ Spec (.of ℂ)} {Y'' : Scheme.{0}} {y'' : Y'' ⟶ Spec (.of ℂ)}

/-- The map `Y(ℂ) → Y'(ℂ)` induced by a morphism `f : Y ⟶ Y'` over `ℂ`. -/
noncomputable def map (f : Y ⟶ Y') (hf : f ≫ y' = y) (p : ComplexPoints y) : ComplexPoints y' :=
  ⟨p.hom ≫ f, by rw [Category.assoc, hf, p.hom_comp]⟩

@[simp]
theorem map_hom (f : Y ⟶ Y') (hf : f ≫ y' = y) (p : ComplexPoints y) :
    (map f hf p).hom = p.hom ≫ f := rfl

theorem map_mem_iff (f : Y ⟶ Y') (hf : f ≫ y' = y) (p : ComplexPoints y) (U : Y'.Opens) :
    (map f hf p).Mem U ↔ p.Mem (f ⁻¹ᵁ U) := Iff.rfl

/-- The value of a regular function at the image of a point is the value of its pullback. -/
theorem eval_map_point (f : Y ⟶ Y') (hf : f ≫ y' = y) {U : Y'.Opens} (g : Γ(Y', U))
    (p : ComplexPoints y) (hp : (map f hf p).Mem U) :
    eval g (map f hf p) hp = eval (f.app U g) p hp := by
  simp only [eval, map_hom]
  rw [Scheme.Hom.comp_appLE]
  rfl

@[simp]
theorem map_id (p : ComplexPoints y) : map (𝟙 Y) (Category.id_comp y) p = p :=
  ext (Category.comp_id _)

theorem map_comp (f : Y ⟶ Y') (hf : f ≫ y' = y) (f' : Y' ⟶ Y'') (hf' : f' ≫ y'' = y')
    (p : ComplexPoints y) :
    map (f ≫ f') (by rw [Category.assoc, hf', hf]) p = map f' hf' (map f hf p) :=
  ext (Category.assoc _ _ _).symm

/-- **A morphism over `ℂ` induces a continuous map on complex points.** -/
theorem continuous_map (f : Y ⟶ Y') (hf : f ≫ y' = y) : Continuous (map f hf) := by
  rw [continuous_iff]
  intro U _ g V hV
  have : map f hf ⁻¹' basicSet U g V = basicSet (f ⁻¹ᵁ U) (f.app U g) V := by
    ext p
    exact ⟨fun ⟨hp, h⟩ => ⟨hp, (eval_map_point f hf g p hp) ▸ h⟩,
      fun ⟨hp, h⟩ => ⟨hp, (eval_map_point f hf g p hp).symm ▸ h⟩⟩
  rw [this]
  exact isOpen_basicSet_of_isOpen _ _ hV


theorem injective_map_of_mono (f : Y ⟶ Y') [Mono f] (hf : f ≫ y' = y) :
    Function.Injective (map f hf) :=
  fun _p _q h => ext ((cancel_mono f).1 (congrArg ComplexPoints.hom h))

/-! ### Open immersions -/

section OpenImmersion

variable (f : Y ⟶ Y') [IsOpenImmersion f] (hf : f ≫ y' = y)

/-- The image of `Y(ℂ)` under an open immersion is the set of points of its image. -/
theorem range_map_of_isOpenImmersion :
    Set.range (map f hf) = {p | p.Mem f.opensRange} := by
  ext p
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  constructor
  · rintro ⟨q, rfl⟩
    refine (map_mem_iff f hf q _).2 ?_
    have : f ⁻¹ᵁ f.opensRange = ⊤ := by simp
    rw [this]
    exact mem_top q
  · intro hp
    have hr : Set.range p.hom ⊆ Set.range f := by
      rintro _ ⟨z, rfl⟩
      have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
      rw [Subsingleton.elim z pt]
      exact (mem_iff pt).1 hp
    refine ⟨⟨IsOpenImmersion.lift f p.hom hr, ?_⟩, ext (IsOpenImmersion.lift_fac _ _ _)⟩
    rw [← hf, ← Category.assoc, IsOpenImmersion.lift_fac, p.hom_comp]

omit [IsOpenImmersion f] in
theorem eval_app_appIso_inv [IsOpenImmersion f] (U : Y.Opens) (g : Γ(Y, U)) (p : ComplexPoints y)
    (hp : p.Mem (f ⁻¹ᵁ f ''ᵁ U)) (hpU : p.Mem U) :
    eval (f.app (f ''ᵁ U) ((f.appIso U).inv g)) p hp = eval g p hpU := by
  have hU' : U ≤ f ⁻¹ᵁ f ''ᵁ U := (f.preimage_image_eq U).ge
  have key : Y.presheaf.map (homOfLE hU').op (f.app (f ''ᵁ U) ((f.appIso U).inv g)) = g := by
    have := (f.appIso U).inv_hom_id_apply g
    rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply] at this
    convert this using 3
    exact congrArg _ (Subsingleton.elim _ _)
  rw [← eval_map hU' _ p hpU, key]

/-- **An open immersion over `ℂ` induces an open embedding on complex points**, onto the points
of its image. -/
theorem isOpenEmbedding_map_of_isOpenImmersion : IsOpenEmbedding (map f hf) := by
  refine ⟨⟨?_, injective_map_of_mono f hf⟩, ?_⟩
  · rw [isInducing_iff]
    refine le_antisymm (continuous_iff_le_induced.1 (continuous_map f hf)) ?_
    apply le_generateFrom
    rintro _ ⟨U, hU, g, V, hV, rfl⟩
    refine isOpen_induced_iff.2 ⟨basicSet (f ''ᵁ U) ((f.appIso U).inv g) V,
      isOpen_basicSet (hU.image_of_isOpenImmersion f) _ hV, ?_⟩
    ext p
    have hU' : f ⁻¹ᵁ f ''ᵁ U = U := f.preimage_image_eq U
    constructor
    · rintro ⟨hp, h⟩
      have hpU : p.Mem U := by rw [← hU']; exact hp
      refine ⟨hpU, ?_⟩
      rw [eval_map_point] at h
      convert h using 1
      exact (eval_app_appIso_inv f U g p hp hpU).symm
    · rintro ⟨hp, h⟩
      have hpU : (map f hf p).Mem (f ''ᵁ U) := by
        rw [map_mem_iff, hU']; exact hp
      refine ⟨hpU, ?_⟩
      rw [eval_map_point]
      convert h using 1
      exact eval_app_appIso_inv f U g p hpU hp
  · rw [range_map_of_isOpenImmersion]
    exact isOpen_setOf_mem _

end OpenImmersion


/-! ### Closed immersions -/

/-- Precomposition with a surjection `π : A → B` is a closed embedding `ℂ^B → ℂ^A`. -/
theorem isClosedEmbedding_comp_of_surjective {A B : Type*} {π : A → B}
    (hπ : Function.Surjective π) : IsClosedEmbedding (fun ψ : B → ℂ => ψ ∘ π) :=
  Function.LeftInverse.isClosedEmbedding (f := fun φ : A → ℂ => φ ∘ Function.surjInv hπ)
    (fun ψ => by funext b; simp [Function.surjInv_eq hπ b])
    (continuous_pi fun _ => continuous_apply _) (continuous_pi fun _ => continuous_apply _)

/-- The open cover of `Y(ℂ)` by the `U(ℂ)`, `U` an affine open of `Y`. -/
theorem isOpenCover_affineOpens :
    IsOpenCover fun U : Y.affineOpens =>
      (⟨{p : ComplexPoints y | p.Mem U}, isOpen_setOf_mem _⟩ :
        TopologicalSpace.Opens (ComplexPoints y)) := by
  refine IsOpenCover.mk (eq_top_iff.2 fun p _ => ?_)
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨V, hV, hx, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
    (show p.hom.base pt ∈ (⊤ : Y.Opens) from trivial)
  exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, (mem_iff pt).2 hx⟩

section ClosedImmersion

variable {Z : Scheme.{0}} {z : Z ⟶ Spec (.of ℂ)} (i : Z ⟶ Y) [IsClosedImmersion i]
  (hi : i ≫ y = z)

/-- **A closed immersion over `ℂ` induces a closed embedding on complex points.** -/
theorem isClosedEmbedding_map_of_isClosedImmersion : IsClosedEmbedding (map i hi) := by
  rw [isOpenCover_affineOpens.isClosedEmbedding_iff_restrictPreimage (continuous_map i hi)]
  intro U
  rw [← (isClosedEmbedding_evalMap U.2).of_comp_iff]
  have hZ : IsAffineOpen (i ⁻¹ᵁ (U : Y.Opens)) := IsAffineHom.isAffine_preimage _ U.2
  let e : ↥(map i hi ⁻¹' ({p : ComplexPoints y | p.Mem U} : Set (ComplexPoints y))) ≃ₜ
      {q : ComplexPoints z // q.Mem (i ⁻¹ᵁ (U : Y.Opens))} :=
    Homeomorph.subtype (Homeomorph.refl _) fun _ => Iff.rfl
  have h := (isClosedEmbedding_comp_of_surjective (i.app_surjective U U.2)).comp
    ((isClosedEmbedding_evalMap hZ).comp e.isClosedEmbedding)
  convert h using 1
  funext q
  funext g
  exact eval_map_point i hi g q.1 q.2

end ClosedImmersion


/-! ### Presentations -/

section Presentation

variable {ι : Type*} (s : ι → Γ(Y, U))

variable (y) in
/-- The `ℂ`-algebra map `ℂ[x_i : i ∈ ι] → Γ(Y, U)` sending `x_i` to `s i`. -/
noncomputable def presentationHom : MvPolynomial ι ℂ →+* Γ(Y, U) :=
  MvPolynomial.eval₂Hom (constHom (y := y) U) s

variable (y) in
/-- The coordinates `p ↦ (s_i(p))_i` of `U(ℂ)` attached to a family of regular functions. -/
noncomputable def coords : {p : ComplexPoints y // p.Mem U} → (ι → ℂ) :=
  fun p i => eval (s i) p.1 p.2

variable (y) in
/-- The common zeros in `ℂ^ι` of the relations among the `s i`. -/
def zeroLocus : Set (ι → ℂ) :=
  {z | ∀ P ∈ RingHom.ker (presentationHom y s), MvPolynomial.eval z P = 0}

theorem eval_presentationHom (P : MvPolynomial ι ℂ) (p : ComplexPoints y) (hp : p.Mem U) :
    eval (presentationHom y s P) p hp = MvPolynomial.eval (fun i => eval (s i) p hp) P := by
  change (evalHom p hp).comp (presentationHom y s) P = _
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [presentationHom]
  · simp [presentationHom]

theorem continuous_coords (hU : IsAffineOpen U) : Continuous (coords y s) :=
  continuous_pi fun i => continuous_eval hU (s i)

theorem isClosed_zeroLocus : IsClosed (zeroLocus y s) := by
  have : zeroLocus y s =
      ⋂ P ∈ RingHom.ker (presentationHom y s), {z | MvPolynomial.eval z P = 0} := by
    ext z
    simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [this]
  exact isClosed_biInter fun P _ => isClosed_eq (MvPolynomial.continuous_eval P) continuous_const

variable {s}

theorem range_coords (hU : IsAffineOpen U) (hs : Function.Surjective (presentationHom y s)) :
    Set.range (coords y s) = zeroLocus y s := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩ P hP
    change MvPolynomial.eval (fun i => eval (s i) p.1 p.2) P = 0
    rw [← eval_presentationHom, (RingHom.mem_ker).1 hP, eval_zero]
  · intro hz
    let φ : Γ(Y, U) →+* ℂ := RingHom.liftOfRightInverse (presentationHom y s)
      (Function.surjInv hs) (Function.rightInverse_surjInv hs)
      ⟨MvPolynomial.eval z, fun P hP => (RingHom.mem_ker).2 (hz P hP)⟩
    have hφ : ∀ P, φ (presentationHom y s P) = MvPolynomial.eval z P := fun P =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
    have hc : ∀ c, φ (constHom (y := y) U c) = c := by
      intro c
      have := hφ (MvPolynomial.C c)
      simpa [presentationHom] using this
    refine ⟨⟨ofRingHom hU hc, ofRingHom_mem hU hc⟩, funext fun i => ?_⟩
    have := hφ (MvPolynomial.X i)
    simp only [presentationHom, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X] at this
    simp only [coords, eval_ofRingHom]
    exact this

/-- **The complex points of an affine open with a presentation are the zero set of the
relations.** For `U` affine and `ℂ[x_i] ↠ Γ(Y, U)`, `x_i ↦ s i`, the coordinates
`p ↦ (s_i(p))_i` are a closed embedding of `U(ℂ)` into `ℂ^ι` with image the zero set. -/
theorem isClosedEmbedding_coords (hU : IsAffineOpen U)
    (hs : Function.Surjective (presentationHom y s)) :
    IsClosedEmbedding (coords y s) := by
  let G : (ι → ℂ) → (Γ(Y, U) → ℂ) := fun z g => MvPolynomial.eval z (Function.surjInv hs g)
  have hG : Continuous G :=
    continuous_pi fun g => MvPolynomial.continuous_eval (Function.surjInv hs g)
  have hcomp : G ∘ coords y s = evalMap (y := y) U := by
    funext p g
    change MvPolynomial.eval (fun i => eval (s i) p.1 p.2) _ = _
    rw [← eval_presentationHom, Function.surjInv_eq hs g]
    rfl
  have he := isClosedEmbedding_evalMap (y := y) hU
  rw [← hcomp] at he
  refine ⟨⟨IsInducing.of_comp (continuous_coords s hU) hG he.isInducing,
    he.injective.of_comp⟩, ?_⟩
  rw [range_coords hU hs]
  exact isClosed_zeroLocus s

/-- The homeomorphism of `U(ℂ)` with the zero set of the relations of a presentation. -/
noncomputable def homeomorphZeroLocus (hU : IsAffineOpen U)
    (hs : Function.Surjective (presentationHom y s)) :
    {p : ComplexPoints y // p.Mem U} ≃ₜ zeroLocus y s :=
  (isClosedEmbedding_coords hU hs).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_coords hU hs))

/-- The homeomorphism of `Y(ℂ)`, `Y` affine, with the zero set in `ℂ^ι` of the relations of a
presentation `ℂ[x_i] ↠ Γ(Y, ⊤)`. -/
noncomputable def homeomorphZeroLocusOfIsAffine [IsAffine Y] {s : ι → Γ(Y, ⊤)}
    (hs : Function.Surjective (presentationHom y s)) :
    ComplexPoints y ≃ₜ zeroLocus y s :=
  ((Homeomorph.Set.univ _).symm.trans
      (Homeomorph.setCongr (Set.ext fun p => ⟨fun _ => mem_top p, fun _ => trivial⟩))).trans
    (homeomorphZeroLocus (isAffineOpen_top Y) hs)

end Presentation

end AlgebraicGeometry.Scheme.ComplexPoints
