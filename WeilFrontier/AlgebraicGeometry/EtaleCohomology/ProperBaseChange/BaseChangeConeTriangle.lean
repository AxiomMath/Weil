module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import WeilFrontier.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy
public import WeilFrontier.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilFrontier.Algebra.Homology.DerivedCategory.HomologySequence
public import Weil.Attr

/-!
# The base change morphism on the triangle of a mapping cone

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes, and let `θ : P ⟶ Q` be a morphism of bounded below
complexes of abelian sheaves on the small étale site of `X`, with mapping cone `C(θ)`. We show
that the choices of resolutions computing the base change morphism can be made compatibly with
the triangle `P ⟶ Q ⟶ C(θ) ⟶ P[1]`: there are choices of resolutions `(ι_P, q_P)`, `(ι_Q, q_Q)`,
`(ι, q)` of `P`, `Q`, `C(θ)`, with targets `I_P, J_P`, `I_Q, J_Q`, `I, J`, and admissible
triangles in the homotopy category of `Y'` with vertices `(g^* f_* I_P, g^* f_* I_Q, g^* f_* I)`
and `(f'_* J_P, f'_* J_Q, f'_* J)`, such that the classes of the three base change morphisms
`γ_{(ι_P,q_P)}`, `γ_{(ι_Q,q_Q)}`, `γ_{(ι,q)}` form a morphism of triangles.

The construction: resolve `P` and `Q` by `ι_P : P ⟶ I_P` and `ι_Q : Q ⟶ I_Q`, lift `θ` to
`θ̃ : I_P ⟶ I_Q` with `θ ≫ ι_Q` homotopic to `ι_P ≫ θ̃`, and let `ι : C(θ) ⟶ C(θ̃)` be the map
of cones induced by the homotopy; it is a quasi-isomorphism. On `X'`, resolve `g'^* I_P` and
`g'^* I_Q` by `q_P`, `q_Q`, lift `g'^* θ̃` to `θ̂ : J_P ⟶ J_Q` in the same way, and let `q` be
the identification `g'^* C(θ̃) ≅ C(g'^* θ̃)` followed by the induced map of cones
`C(g'^* θ̃) ⟶ C(θ̂)`. The triangles are the images of the triangles of `θ̃` and `θ̂` under
`g^* f_*` and `f'_*`.

The construction only uses that `g'^*`, `g^* f_*` and `f'_*` are additive and that the base
change map `β : g^* f_* ⟶ f'_* g'^*` is a natural transformation, so it is carried out for
additive functors `G : A ⥤ A'`, `F₁ : A ⥤ B`, `F₂ : A' ⥤ B` between abelian categories (`A`,
`A'` with enough injectives) and a natural transformation `β : F₁ ⟶ G ⋙ F₂`; the étale statement
is the case `G = g'^*`, `F₁ = g^* f_*`, `F₂ = f'_*`, `β = etaleAbelianBaseChange f g g' f' h`.

## Main definitions

* `CochainComplex.InjectiveResolutionPair G F` — a choice of resolutions of a complex `F`
  relative to `G`: quasi-isomorphisms `ι : F ⟶ I` and `q : G(I) ⟶ J` into bounded below
  complexes of injective objects.
* `CochainComplex.ResolutionBaseChangeConeTriangle G F₁ F₂ β θ` — the statement that suitable
  choices of resolutions of `P`, `Q` and `C(θ)` make the classes of the morphisms
  `γ = F₂(q) ∘ β_I` a morphism of admissible triangles.

## Main results

* `CochainComplex.resolutionBaseChangeConeTriangle` — the general statement, for any `θ`
  between cohomologically bounded below complexes.
* `Stacks.EtaleCohomology.resolutionBaseChangeConeTriangle_etaleAbelianBaseChange` — the case of
  the base change morphism of a commutative square of schemes.

## Implementation notes

"Bounded below" for `P` and `Q` is taken cohomologically (`CochainComplex.IsGE`), which
contains the case of complexes strictly in degrees `≥ a`; the resolving complexes are strictly
bounded below. The mapping cone is Mathlib's `CochainComplex.mappingCone`, and a morphism of
triangles is Mathlib's `CategoryTheory.Pretriangulated.TriangleMorphism`. The triangles are
admissible in the sense of `HomotopyCategory.admissibleTriangles` (third morphism the cone
projection); they are obtained from Mathlib's distinguished triangles by negating the third
morphism. Sheaves are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology`, the
setting of `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`. The square is only assumed
commutative.

In the étale case the morphism `γ_R = f'_*(q) ∘ β_I` appears in the statement in the form
`(NatTrans.mapHomologicalComplex β _).app I ≫ (f'_*).mapHomologicalComplex.map q`, which is the
definition of `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange f g g' f' h I q`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CochainComplex

section

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor preserving zero morphisms sends complexes strictly in degrees `≥ n` to complexes
strictly in degrees `≥ n`. -/
private lemma isStrictlyGE_mapHomologicalComplex_obj (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact F.map_isZero (K.isZero_of_isStrictlyGE n i hi)

end

variable {C : Type*} [Category* C] [Abelian C]

/-- `Q(f)` is invertible in the derived category exactly when `f` is a quasi-isomorphism. -/
private lemma quasiIso_iff_isIso_Qh_map [HasDerivedCategory C] {K L : CochainComplex C ℤ}
    (f : K ⟶ L) :
    QuasiIso f ↔
      IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)) := by
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]

/-- **Lifting a morphism to resolutions.** Let `θ : P ⟶ Q` be a morphism of complexes,
`ι_P : P ⟶ I` a quasi-isomorphism and `ι_Q : Q ⟶ J` a morphism into a K-injective complex. There
is a morphism `θ̃ : I ⟶ J` such that `θ ≫ ι_Q` is homotopic to `ι_P ≫ θ̃`. -/
private theorem exists_homotopy_comp_of_quasiIso {P Q I J : CochainComplex C ℤ} (θ : P ⟶ Q)
    (ιP : P ⟶ I) [QuasiIso ιP] (ιQ : Q ⟶ J) [J.IsKInjective] :
    ∃ θ' : I ⟶ J, Nonempty (Homotopy (θ ≫ ιQ) (ιP ≫ θ')) := by
  let := HasDerivedCategory.standard C
  have hP := (quasiIso_iff_isIso_Qh_map ιP).1 inferInstance
  obtain ⟨x, hx⟩ := (IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) J).2
    (inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ιP)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (θ ≫ ιQ)))
  obtain ⟨θ', rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective x
  refine ⟨θ', ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) J).1
  simp only [Functor.map_comp] at hx ⊢
  rw [hx, IsIso.hom_inv_id_assoc]

namespace mappingCone

/-- The terms of the mapping cone of a morphism between complexes of injective objects are
injective. -/
private theorem injective_X {K L : CochainComplex C ℤ} (φ : K ⟶ L) [∀ n, Injective (K.X n)]
    [∀ n, Injective (L.X n)] (n : ℤ) : Injective ((mappingCone φ).X n) :=
  Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
    inferInstance

/-- **The cone of a homotopy commutative square of quasi-isomorphisms.** If
`H : φ₁ ≫ b ≃ a ≫ φ₂` and `a`, `b` are quasi-isomorphisms, the induced morphism of mapping cones
`mappingCone φ₁ ⟶ mappingCone φ₂` is a quasi-isomorphism. -/
private theorem quasiIso_mapOfHomotopy {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁}
    {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))
    [QuasiIso a] [QuasiIso b] : QuasiIso (mapOfHomotopy H) := by
  let := HasDerivedCategory.standard C
  rw [quasiIso_iff_isIso_Qh_map]
  exact _root_.CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Qh.mapTriangle.map (trianglehMapOfHomotopy H))
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₁))
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₂))
    ((quasiIso_iff_isIso_Qh_map a).1 inferInstance) ((quasiIso_iff_isIso_Qh_map b).1 inferInstance)

section MapTriangle

variable {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The image under an additive functor `F` of the triangle of the mapping cone of `φ`, as a
triangle of the homotopy category of `D` with vertices `F(K)`, `F(L)`, `F(mappingCone φ)`. -/
private abbrev mapTriangleh : Triangle (HomotopyCategory D (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapTriangle.obj
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangle.obj (triangle φ))

/-- The triangle `mapTriangleh F φ` is distinguished. -/
private theorem mapTriangleh_distinguished : mapTriangleh F φ ∈ distTriang _ :=
  isomorphic_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) _
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapTriangle.mapIso (mapTriangleIso φ F))

/-- The triangle `mapTriangleh F φ` with its third morphism negated is admissible. -/
private theorem mk_neg_mapTriangleh_mor₃_mem_admissibleTriangles :
    Triangle.mk (mapTriangleh F φ).mor₁ (mapTriangleh F φ).mor₂ (-(mapTriangleh F φ).mor₃) ∈
      HomotopyCategory.admissibleTriangles D :=
  (HomotopyCategory.mem_distinguishedTriangles_iff_admissible _).1
    (mapTriangleh_distinguished F φ)

end MapTriangle

end mappingCone

/-- Applying `G ⋙ H` degreewise to `x` and then `H` to `y` is `H` applied to `G(x) ≫ y`. -/
@[reassoc]
private theorem mapHomologicalComplex_comp_map_comp {V W U : Type*} [Category* V]
    [Category* W] [Category* U] [HasZeroMorphisms V] [HasZeroMorphisms W]
    [HasZeroMorphisms U] (G : V ⥤ W) (H : W ⥤ U)
    [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    {K L : CochainComplex V ℤ} {M : CochainComplex W ℤ} (x : K ⟶ L)
    (y : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ M) :
    ((G ⋙ H).mapHomologicalComplex (ComplexShape.up ℤ)).map x ≫
        (H.mapHomologicalComplex (ComplexShape.up ℤ)).map y =
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map x ≫ y) := by
  rw [Functor.map_comp]
  rfl

section Resolutions

variable {A A' B : Type*} [Category* A] [Abelian A] [Category* A'] [Abelian A']
  [Category* B] [Abelian B]

/-- **A choice of resolutions** of a complex `F` in `A` relative to an additive functor
`G : A ⥤ A'`: quasi-isomorphisms `ι : F ⟶ I` and `q : G(I) ⟶ J`, where `I` (in `A`) and `J`
(in `A'`) are bounded below complexes of injective objects. -/
structure InjectiveResolutionPair (G : A ⥤ A') [G.Additive] (F : CochainComplex A ℤ) where
  /-- The complex of injective objects of `A` resolving `F`. -/
  I : CochainComplex A ℤ
  /-- The complex of injective objects of `A'` resolving `G(I)`. -/
  J : CochainComplex A' ℤ
  /-- The quasi-isomorphism `F ⟶ I`. -/
  ι : F ⟶ I
  /-- The quasi-isomorphism `G(I) ⟶ J`. -/
  q : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J
  quasiIso_ι : QuasiIso ι
  quasiIso_q : QuasiIso q
  injective_I (n : ℤ) : Injective (I.X n)
  injective_J (n : ℤ) : Injective (J.X n)
  exists_isStrictlyGE_I : ∃ a : ℤ, I.IsStrictlyGE a
  exists_isStrictlyGE_J : ∃ b : ℤ, J.IsStrictlyGE b

variable (G : A ⥤ A') [G.Additive] (F₁ : A ⥤ B) [F₁.Additive] (F₂ : A' ⥤ B) [F₂.Additive]
  (β : F₁ ⟶ G ⋙ F₂)

section ConeTriangle

variable {IP IQ : CochainComplex A ℤ} (θ' : IP ⟶ IQ) {JP JQ : CochainComplex A' ℤ}
  (qP : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj IP ⟶ JP)
  (qQ : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj IQ ⟶ JQ) (θ'' : JP ⟶ JQ)
  (H' : Homotopy ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map θ' ≫ qQ) (qP ≫ θ''))

/-- The resolution `G(C(θ̃)) ⟶ C(θ̂)` of the image of a cone: the identification
`G(C(θ̃)) ≅ C(G θ̃)` followed by the map of cones induced by the homotopy `H'`. -/
private def mappingCone.mapHomologicalComplexMapOfHomotopy :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mappingCone θ') ⟶ mappingCone θ'' :=
  (mappingCone.mapHomologicalComplexIso θ' G).hom ≫ mappingCone.mapOfHomotopy H'

include H' in
/-- The first square of the base change morphisms of resolutions commutes in the homotopy
category. -/
private theorem resolutionBaseChange_comm₁ :
    (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map θ') ≫
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app IQ ≫
          (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map qQ) =
    (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app IP ≫
          (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map qP) ≫
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map θ'') := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, NatTrans.naturality,
    Category.assoc, mapHomologicalComplex_comp_map_comp, Category.assoc, ← Functor.map_comp,
    Functor.map_comp, Functor.map_comp (HomotopyCategory.quotient B (ComplexShape.up ℤ)) _
      ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (qP ≫ θ''))]
  congr 1
  exact HomotopyCategory.eq_of_homotopy _ _ (F₂.mapHomotopy H')

/-- The second square of the base change morphisms of resolutions commutes. -/
private theorem resolutionBaseChange_comm₂ :
    (F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.inr θ') ≫
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app (mappingCone θ') ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (mappingCone.mapHomologicalComplexMapOfHomotopy G θ' qP qQ θ'' H') =
    ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app IQ ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map qQ) ≫
      (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.inr θ'') := by
  unfold mappingCone.mapHomologicalComplexMapOfHomotopy
  rw [← Category.assoc, NatTrans.naturality, Category.assoc,
    mapHomologicalComplex_comp_map_comp, ← Category.assoc,
    mappingCone.map_inr, mappingCone.triangleMapOfHomotopy_comm₂,
    Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The third square of the base change morphisms of resolutions commutes. -/
private theorem resolutionBaseChange_comm₃ :
    ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.triangle θ').mor₃ ≫
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app IP) ≫
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app IP ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map qP)⟦(1 : ℤ)⟧' =
    ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app (mappingCone θ') ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (mappingCone.mapHomologicalComplexMapOfHomotopy G θ' qP qQ θ'' H')) ≫
      (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.triangle θ'').mor₃ ≫
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app JP := by
  have h3 := mappingCone.map_δ θ' G
  have hs : ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app IP ≫
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app IP ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map qP)⟦(1 : ℤ)⟧' =
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app (IP⟦(1 : ℤ)⟧) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((G.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app IP ≫
            qP⟦(1 : ℤ)⟧') ≫
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app JP := by
    ext n
    simp
  unfold mappingCone.mapHomologicalComplexMapOfHomotopy
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Category.assoc, mappingCone.triangleMapOfHomotopy_comm₃,
    ← reassoc_of% h3, ← mapHomologicalComplex_comp_map_comp_assoc]
  rw [hs]
  exact NatTrans.naturality_assoc (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ))
    (mappingCone.triangle θ').mor₃ _

end ConeTriangle

/-- The property that the base change morphisms of resolutions are compatible with the
triangle of the mapping cone of `θ : P ⟶ Q`, for additive functors `G : A ⥤ A'`, `F₁ : A ⥤ B`,
`F₂ : A' ⥤ B` and a natural transformation `β : F₁ ⟶ G ⋙ F₂`: there are choices of resolutions
`R_P`, `R_Q`, `R` of `P`, `Q` and `mappingCone θ` relative to `G`, and admissible triangles in
the homotopy category of `B` with vertices `(F₁ I_P, F₁ I_Q, F₁ I)` and `(F₂ J_P, F₂ J_Q, F₂ J)`,
such that the classes of the morphisms `γ_R = F₂(q) ∘ β_I : F₁ I ⟶ F₂ J` are the components of a
morphism of triangles between them. -/
def ResolutionBaseChangeConeTriangle {P Q : CochainComplex A ℤ} (θ : P ⟶ Q) : Prop :=
  ∃ (RP : InjectiveResolutionPair G P) (RQ : InjectiveResolutionPair G Q)
    (R : InjectiveResolutionPair G (mappingCone θ))
    (u₁ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj RP.I) ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj RQ.I))
    (u₂ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj RQ.I) ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.I))
    (u₃ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.I) ⟶
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj RP.I))⟦(1 : ℤ)⟧)
    (v₁ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj RP.J) ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj RQ.J))
    (v₂ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj RQ.J) ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.J))
    (v₃ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.J) ⟶
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj RP.J))⟦(1 : ℤ)⟧),
    Triangle.mk u₁ u₂ u₃ ∈ HomotopyCategory.admissibleTriangles B ∧
    Triangle.mk v₁ v₂ v₃ ∈ HomotopyCategory.admissibleTriangles B ∧
    ∃ φ : Triangle.mk u₁ u₂ u₃ ⟶ Triangle.mk v₁ v₂ v₃,
      φ.hom₁ = (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app RP.I ≫
          (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map RP.q) ∧
      φ.hom₂ = (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app RQ.I ≫
          (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map RQ.q) ∧
      φ.hom₃ = (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app R.I ≫
          (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map R.q)

/-- **The base change morphism on the triangle of a mapping cone**, for additive functors
`G : A ⥤ A'`, `F₁ : A ⥤ B`, `F₂ : A' ⥤ B` and a natural transformation `β : F₁ ⟶ G ⋙ F₂`. Let
`θ : P ⟶ Q` be a morphism of bounded below complexes in `A`. There are choices of resolutions
`R_P`, `R_Q`, `R` of `P`, `Q` and `mappingCone θ`, and admissible triangles in the homotopy
category of `B` with vertices `(F₁ I_P, F₁ I_Q, F₁ I)` and `(F₂ J_P, F₂ J_Q, F₂ J)`, such that
the classes of the morphisms `γ_R = F₂(q) ∘ β_I` are the components of a morphism of triangles
between them. -/
theorem resolutionBaseChangeConeTriangle [EnoughInjectives A] [EnoughInjectives A']
    {P Q : CochainComplex A ℤ} (θ : P ⟶ Q) (a b : ℤ) [P.IsGE a] [Q.IsGE b] :
    ResolutionBaseChangeConeTriangle G F₁ F₂ β θ := by
  -- Step 1: resolving the cone of `θ` in `A`.
  obtain ⟨RP₀, hRP₀⟩ := InjectiveResolutionPlus.exists_isStrictlyGE_of_isGE P a
  obtain ⟨RQ₀, hRQ₀⟩ := InjectiveResolutionPlus.exists_isStrictlyGE_of_isGE Q b
  obtain ⟨θ', ⟨H⟩⟩ := exists_homotopy_comp_of_quasiIso θ RP₀.ι RQ₀.ι
  have hι := mappingCone.quasiIso_mapOfHomotopy H
  -- Step 2: resolving the cone of `G θ̃` in `A'`.
  have := isStrictlyGE_mapHomologicalComplex_obj G RP₀.cocomplex a
  have := isStrictlyGE_mapHomologicalComplex_obj G RQ₀.cocomplex b
  obtain ⟨SP, hSP⟩ := InjectiveResolutionPlus.exists_isStrictlyGE_of_isGE
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj RP₀.cocomplex) a
  obtain ⟨SQ, hSQ⟩ := InjectiveResolutionPlus.exists_isStrictlyGE_of_isGE
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj RQ₀.cocomplex) b
  obtain ⟨θ'', ⟨H'⟩⟩ := exists_homotopy_comp_of_quasiIso
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map θ') SP.ι SQ.ι
  have hq' := mappingCone.quasiIso_mapOfHomotopy H'
  have hq : QuasiIso (mappingCone.mapHomologicalComplexMapOfHomotopy G θ' SP.ι SQ.ι θ'' H') := by
    unfold mappingCone.mapHomologicalComplexMapOfHomotopy
    infer_instance
  let RP : InjectiveResolutionPair G P :=
    { I := RP₀.cocomplex, J := SP.cocomplex, ι := RP₀.ι, q := SP.ι
      quasiIso_ι := inferInstance, quasiIso_q := inferInstance
      injective_I := inferInstance, injective_J := inferInstance
      exists_isStrictlyGE_I := ⟨a, hRP₀⟩, exists_isStrictlyGE_J := ⟨a, hSP⟩ }
  let RQ : InjectiveResolutionPair G Q :=
    { I := RQ₀.cocomplex, J := SQ.cocomplex, ι := RQ₀.ι, q := SQ.ι
      quasiIso_ι := inferInstance, quasiIso_q := inferInstance
      injective_I := inferInstance, injective_J := inferInstance
      exists_isStrictlyGE_I := ⟨b, hRQ₀⟩, exists_isStrictlyGE_J := ⟨b, hSQ⟩ }
  let R : InjectiveResolutionPair G (mappingCone θ) :=
    { I := mappingCone θ', J := mappingCone θ''
      ι := mappingCone.mapOfHomotopy H
      q := mappingCone.mapHomologicalComplexMapOfHomotopy G θ' SP.ι SQ.ι θ'' H'
      quasiIso_ι := hι, quasiIso_q := hq
      injective_I := mappingCone.injective_X θ'
      injective_J := mappingCone.injective_X θ''
      exists_isStrictlyGE_I := ⟨min (a - 1) b, isStrictlyGE_mappingCone θ' a b _⟩
      exists_isStrictlyGE_J := ⟨min (a - 1) b, isStrictlyGE_mappingCone θ'' a b _⟩ }
  -- Step 3: the two triangles and the morphism between them.
  refine ⟨RP, RQ, R,
    (mappingCone.mapTriangleh F₁ θ').mor₁, (mappingCone.mapTriangleh F₁ θ').mor₂,
    -(mappingCone.mapTriangleh F₁ θ').mor₃,
    (mappingCone.mapTriangleh F₂ θ'').mor₁, (mappingCone.mapTriangleh F₂ θ'').mor₂,
    -(mappingCone.mapTriangleh F₂ θ'').mor₃,
    mappingCone.mk_neg_mapTriangleh_mor₃_mem_admissibleTriangles _ _,
    mappingCone.mk_neg_mapTriangleh_mor₃_mem_admissibleTriangles _ _,
    TriangleMorphism.negMor₃
      { hom₁ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app RP₀.cocomplex ≫
            (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map SP.ι)
        hom₂ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app RQ₀.cocomplex ≫
            (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map SQ.ι)
        hom₃ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app (mappingCone θ') ≫
            (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (mappingCone.mapHomologicalComplexMapOfHomotopy G θ' SP.ι SQ.ι θ'' H'))
        comm₁ := resolutionBaseChange_comm₁ G F₁ F₂ β θ' SP.ι SQ.ι θ'' H'
        comm₂ := by
          change (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.inr θ')) ≫
              (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app (mappingCone θ') ≫
                  (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
                    (mappingCone.mapHomologicalComplexMapOfHomotopy G θ' SP.ι SQ.ι θ'' H')) =
            (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app RQ₀.cocomplex ≫
                  (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map SQ.ι) ≫
              (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.inr θ''))
          rw [← Functor.map_comp, ← Functor.map_comp, resolutionBaseChange_comm₂]
        comm₃ := by
          change ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCone.triangle θ').mor₃ ≫
                ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
                  RP₀.cocomplex) ≫
              ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
                ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj RP₀.cocomplex)) ≫
              ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app RP₀.cocomplex ≫
                  (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map SP.ι))⟦(1 : ℤ)⟧' =
            (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app (mappingCone θ') ≫
                (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
                  (mappingCone.mapHomologicalComplexMapOfHomotopy G θ' SP.ι SQ.ι θ'' H')) ≫
              (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
                    (mappingCone.triangle θ'').mor₃ ≫
                  ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
                    SP.cocomplex) ≫
              ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
                ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj SP.cocomplex)
          rw [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc,
            resolutionBaseChange_comm₃ G F₁ F₂ β θ' SP.ι SQ.ι θ'' H']
          exact Functor.map_comp_assoc _ _ _ _ },
    rfl, rfl, rfl⟩

end Resolutions

end CochainComplex

/- As in `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`, the preadditive structure and
the zero morphisms of abelian sheaves are taken from the abelian structure. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change morphism on the triangle of a mapping cone.** Let `θ : P ⟶ Q` be a
morphism of bounded below complexes of abelian sheaves on `X`. There are choices of resolutions
`R_P`, `R_Q`, `R` of `P`, `Q` and `mappingCone θ` (relative to `g'^*`), and admissible triangles
in the homotopy category of `Y'` with vertices `(g^* f_* I_P, g^* f_* I_Q, g^* f_* I)` and
`(f'_* J_P, f'_* J_Q, f'_* J)`, such that the classes of the base change morphisms
`γ_{R_P}`, `γ_{R_Q}`, `γ_R` are the components of a morphism of triangles between them. Here
`γ_R = f'_*(q) ∘ β_I` is `etaleAbelianResolutionBaseChange f g g' f' h R.I R.q`, which is by
definition the morphism `(NatTrans.mapHomologicalComplex β _).app R.I ≫ f'_*(R.q)` of
`CochainComplex.ResolutionBaseChangeConeTriangle` for `β = etaleAbelianBaseChange f g g' f' h`. -/
@[weil "lem_fk106_base_change_cone_triangle"]
theorem resolutionBaseChangeConeTriangle_etaleAbelianBaseChange
    {P Q : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (θ : P ⟶ Q) (a b : ℤ) [P.IsGE a] [Q.IsGE b] :
    CochainComplex.ResolutionBaseChangeConeTriangle (etaleAbelianInverseImage.{u, v} g')
      (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g)
      (etaleAbelianDirectImage.{u, v} f') (etaleAbelianBaseChange.{u, v} f g g' f' h) θ :=
  CochainComplex.resolutionBaseChangeConeTriangle _ _ _ _ θ a b

end Stacks.EtaleCohomology

end
