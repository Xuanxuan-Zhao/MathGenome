import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitFrameTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralSmoothness
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.SplitFrameTorus

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits hiding mapPair
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs.SpinWeights
open SplitSpinSpecification SplitFrameTorusSpecification
open scoped CategoryTheory.MonObj MonoidAlgebra

noncomputable section

open private diagonalLift diagonalLift_injective diagonalLift_natural diagonalUnit_action
  diagonalUnit_wedge exteriorModel exteriorModel_vectors eBasis
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights

private def liftUnit (S : ScalarTest) :
    DiagonalPoints S →* (ScalarClifford 4 S)ˣ :=
  (SpinFunctor.spinSubgroup (integralForm 4) S (hyperbolicBasis ℤ 4)).subtype.comp diagonalLift

private theorem liftUnit_isDiagonalCliffordLift : IsDiagonalCliffordLift liftUnit := by
  refine ⟨fun S => Subtype.val_injective.comp diagonalLift_injective, ?_, ?_⟩
  · intro S T f t
    exact congrArg Subtype.val (diagonalLift_natural f.hom t).symm
  · intro S
    refine ⟨exteriorModel S, exteriorModel_vectors, fun t => ?_⟩
    refine ⟨(diagonalLift t).property, diagonalUnit_action t, fun I => ?_⟩
    change exteriorModel S (diagonalLift t).val (eBasis S I) =
      (Additive.toMul (evaluate t (exteriorWeight I)) : Sˣ).val • eBasis S I
    rw [(SpinWeights.weightEvaluation S t).2 I]
    exact diagonalUnit_wedge t I

theorem cliffordLift : CliffordLift := ⟨liftUnit, liftUnit_isDiagonalCliffordLift⟩

open private torusParam torusParam_apply epsilon_succ
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights

private def characterOfPoint {R : Type} [CommRing R] (t : DiagonalPoints R) :
    CharacterGroup →* Rˣ :=
  (evaluate t).toMultiplicative

private theorem characterOfPoint_apply {R : Type} [CommRing R] (t : DiagonalPoints R)
    (x : CharacterExponents) :
    characterOfPoint t (Multiplicative.ofAdd x) = Additive.toMul (evaluate t x) := rfl

private theorem scalarCharacter {R : Type} [CommRing R] (t : DiagonalPoints R) :
    characterOfPoint t (Multiplicative.ofAdd (-halfSum)) = scalar t := by
  change scalar t ^ (1 : ℤ) * (∏ i : Fin 3, scales t i.succ ^ (0 : ℤ)) = scalar t
  simp

private theorem exponentExpansion (x : CharacterExponents) :
    x = x.1 • (-halfSum) + ∑ i : Fin 3, x.2 i • epsilon i.succ := by
  simp only [epsilon_succ, halfSum]
  apply Prod.ext
  · change x.1 = x.1 * -(-1) +
      (LinearMap.fst ℤ ℤ (Fin 3 → ℤ)) (∑ i : Fin 3, x.2 i • (0, Pi.single i 1))
    simp
  · funext j
    change x.2 j = x.1 • (-(0 : Fin 3 → ℤ) j) +
      ((LinearMap.snd ℤ ℤ (Fin 3 → ℤ)) (∑ i : Fin 3, x.2 i • (0, Pi.single i 1))) j
    simp [Finset.sum_apply, Pi.single_apply]

private theorem character_ext {R : Type} [CommRing R] {f g : CharacterGroup →* Rˣ}
    (h₀ : f (Multiplicative.ofAdd (-halfSum)) = g (Multiplicative.ofAdd (-halfSum)))
    (h₁ : ∀ i : Fin 3, f (Multiplicative.ofAdd (epsilon i.succ)) =
      g (Multiplicative.ofAdd (epsilon i.succ))) : f = g := by
  let a : CharacterExponents →+ Additive Rˣ := f.toAdditive
  let b : CharacterExponents →+ Additive Rˣ := g.toAdditive
  apply MonoidHom.ext
  intro y
  let x : CharacterExponents := y.toAdd
  change a x = b x
  nth_rw 1 [exponentExpansion x]
  conv_rhs => rw [exponentExpansion x]
  simp only [map_add, map_sum, map_zsmul]
  exact congrArg₂ (· + ·) (congrArg (x.1 • ·) h₀)
    (Finset.sum_congr rfl fun i _ => congrArg (x.2 i • ·) (h₁ i))

private def characterPoints (R : Type) [CommRing R] :
    DiagonalPoints R ≃* (CharacterGroup →* Rˣ) := by
  let f : DiagonalPoints R →* (CharacterGroup →* Rˣ) :=
    { toFun := characterOfPoint
      map_one' := by
        apply MonoidHom.ext
        intro x
        change (1 : Rˣ) ^ x.toAdd.1 * (∏ i : Fin 3, (1 : Rˣ) ^ x.toAdd.2 i) = 1
        simp
      map_mul' := by
        intro t s
        apply MonoidHom.ext
        intro x
        change (scalar t * scalar s) ^ x.toAdd.1 *
          (∏ i : Fin 3, (scales t i.succ * scales s i.succ) ^ x.toAdd.2 i) =
          (scalar t ^ x.toAdd.1 * ∏ i : Fin 3, scales t i.succ ^ x.toAdd.2 i) *
          (scalar s ^ x.toAdd.1 * ∏ i : Fin 3, scales s i.succ ^ x.toAdd.2 i)
        simp only [mul_zpow, Finset.prod_mul_distrib]
        ac_rfl }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro t s h
    apply (torusParam R).injective
    rw [torusParam_apply, torusParam_apply]
    apply Prod.ext
    · simpa only [f, MonoidHom.coe_mk, OneHom.coe_mk, scalarCharacter] using
        DFunLike.congr_fun h (Multiplicative.ofAdd (-halfSum))
    · funext i
      simpa only [f, MonoidHom.coe_mk, OneHom.coe_mk, characterOfPoint_apply,
        (SpinWeights.weightEvaluation R t).1, (SpinWeights.weightEvaluation R s).1] using
        DFunLike.congr_fun h (Multiplicative.ofAdd (epsilon i.succ))
  · intro g
    let p := (g (Multiplicative.ofAdd (-halfSum)), fun i : Fin 3 =>
      g (Multiplicative.ofAdd (epsilon i.succ)))
    let t := (torusParam R).symm p
    have ht : (scalar t, fun i => scales t i.succ) = p :=
      (torusParam_apply t).symm.trans ((torusParam R).apply_symm_apply p)
    refine ⟨t, character_ext ((scalarCharacter t).trans (congrArg Prod.fst ht)) (fun i => ?_)⟩
    exact ((SpinWeights.weightEvaluation R t).1 i.succ).1.trans (congrFun (congrArg Prod.snd ht) i)

private def pointAlgebra (S : ScalarTest) :
    WithConv (LaurentRing →ₐ[ℤ] S) ≃* ScalarPoints diagonalTorus S :=
  Spec.mapMulEquiv

private def pointCharacters (S : ScalarTest) :
    ScalarPoints diagonalTorus S ≃* (CharacterGroup →* Sˣ) :=
  (pointAlgebra S).symm.trans ((MonoidAlgebra.liftMulEquiv ℤ S CharacterGroup).symm.trans
    MonoidHom.toHomUnitsMulEquiv)

private def diagonalPoints (S : ScalarTest) : ScalarPoints diagonalTorus S ≃* DiagonalPoints S :=
  (pointCharacters S).trans (characterPoints S).symm

private theorem pointAlgebra_apply (S : ScalarTest) (f : LaurentRing →ₐ[ℤ] S) :
    pointAlgebra S (WithConv.toConv f) = scalarSpec.map (CommAlgCat.ofHom f).op := by
  apply Over.OverMorphism.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem torusMonomial (S : ScalarTest) (f : LaurentRing →ₐ[ℤ] S)
    (x : CharacterExponents) :
    (Additive.toMul (evaluate (diagonalPoints S (scalarSpec.map (CommAlgCat.ofHom f).op)) x) :
      Sˣ).val = f (monomial x) := by
  change (characterPoints S (diagonalPoints S (scalarSpec.map (CommAlgCat.ofHom f).op))
    (Multiplicative.ofAdd x)).val = _
  rw [show characterPoints S (diagonalPoints S (scalarSpec.map (CommAlgCat.ofHom f).op)) =
    pointCharacters S (scalarSpec.map (CommAlgCat.ofHom f).op) from (characterPoints S).apply_symm_apply _]
  rw [← pointAlgebra_apply S f]
  change (((MonoidAlgebra.liftMulEquiv ℤ S CharacterGroup).symm
    ((pointAlgebra S).symm (pointAlgebra S (WithConv.toConv f))))
      (Multiplicative.ofAdd x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalPoints_natural {S T : ScalarTest} (f : S ⟶ T)
    (t : ScalarPoints diagonalTorus S) :
    diagonalPoints T (scalarSpec.map f.op ≫ t) =
      mapDiagonal f.hom.toRingHom (diagonalPoints S t) := by
  obtain ⟨g, rfl⟩ := (pointAlgebra S).surjective t
  change diagonalPoints T (scalarSpec.map f.op ≫
    pointAlgebra S (WithConv.toConv g.ofConv)) = _
  rw [pointAlgebra_apply S g.ofConv]
  have hcomp : scalarSpec.map f.op ≫ scalarSpec.map (CommAlgCat.ofHom g.ofConv).op =
      scalarSpec.map (CommAlgCat.ofHom (f.hom.comp g.ofConv)).op :=
    (Functor.map_comp _ _ _).symm
  rw [hcomp]
  apply (characterPoints T).injective
  apply MonoidHom.ext
  intro x
  apply Units.ext
  change (Additive.toMul (evaluate
    (diagonalPoints T (scalarSpec.map (CommAlgCat.ofHom (f.hom.comp g.ofConv)).op)) x.toAdd) :
    Tˣ).val = _
  rw [torusMonomial T (f.hom.comp g.ofConv)]
  have hg : g.ofConv (monomial x.toAdd) =
      (Additive.toMul (evaluate (diagonalPoints S
        (scalarSpec.map (CommAlgCat.ofHom g.ofConv).op)) x.toAdd) : Sˣ).val :=
    (torusMonomial S g.ofConv x.toAdd).symm
  change f.hom (g.ofConv (monomial x.toAdd)) =
    (Additive.toMul (evaluate
      (mapDiagonal f.hom.toRingHom (diagonalPoints S (scalarSpec.map (CommAlgCat.ofHom g.ofConv).op)))
      x.toAdd) : Tˣ).val
  rw [hg]
  let t := diagonalPoints S (scalarSpec.map (CommAlgCat.ofHom g.ofConv).op)
  let F := Units.map f.hom.toRingHom.toMonoidHom
  change f.hom ↑(scalar t ^ x.toAdd.1 * ∏ i : Fin 3, scales t i.succ ^ x.toAdd.2 i) =
    ↑((F (scalar t)) ^ x.toAdd.1 *
      ∏ i : Fin 3, (F (scales t i.succ)) ^ x.toAdd.2 i)
  simp only [← map_zpow, ← map_prod, ← map_mul]
  rfl

theorem torusCoordinates : TorusCoordinates :=
  ⟨diagonalPoints, diagonalPoints_natural, torusMonomial⟩

section IntegralPoints

private theorem integral_hom_ext {X Y : Over (Spec (CommRingCat.of ℤ))}
    (hX : IsAffine X.left) {f g : X ⟶ Y}
    (h : ∀ (S : ScalarTest) (x : scalarSpec.obj (op S) ⟶ X), x ≫ f = x ≫ g) :
    f = g := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  simpa using congrArg (e.inv ≫ ·) (h A.unop e.hom)

private theorem integral_point_map (D H : IntegralGroup) (hD : IsAffine D.X.left)
    (φ : ∀ S : ScalarTest, ScalarPoints D S →* ScalarPoints H S)
    (hφ : ∀ {S T : ScalarTest} (f : S ⟶ T) (x : ScalarPoints D S),
      φ T (scalarSpec.map f.op ≫ x) = scalarSpec.map f.op ≫ φ S x) :
    ∃ i : D ⟶ H, ∀ (S : ScalarTest) (x : ScalarPoints D S), x ≫ i.hom.hom = φ S x := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hD
  let i : D.X ⟶ H.X := e.inv ≫ φ A.unop e.hom
  have hi (S : ScalarTest) (x : ScalarPoints D S) : x ≫ i = φ S x := by
    let a : op S ⟶ A := (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).preimage (x ≫ e.inv)
    have ha : scalarSpec.map a = x ≫ e.inv :=
      (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).map_preimage _
    have hn := hφ a.unop e.hom
    change φ S (scalarSpec.map a ≫ e.hom) = scalarSpec.map a ≫ φ A.unop e.hom at hn
    simpa [ha, i, Category.assoc] using hn.symm
  have : IsMonHom i := by
    constructor
    · apply integral_hom_ext (X := 𝟙_ (Over (Spec (CommRingCat.of ℤ)))) (by
        change IsAffine (Spec (CommRingCat.of ℤ))
        infer_instance)
      intro S x
      rw [show x = toUnit (scalarSpec.obj (op S)) from toUnit_unique _ _]
      change (1 : ScalarPoints D S) ≫ i = (1 : ScalarPoints H S)
      exact (hi S 1).trans (map_one (φ S))
    · apply integral_hom_ext (X := D.X ⊗ D.X) (by
        let : IsAffine D.X.left := hD
        change IsAffine (pullback D.X.hom D.X.hom)
        infer_instance)
      intro S x
      let p : ScalarPoints D S := x ≫ fst D.X D.X
      let q : ScalarPoints D S := x ≫ snd D.X D.X
      calc
        x ≫ μ[D.X] ≫ i = (p * q) ≫ i := by simp [p, q, Hom.mul_def]
        _ = (p ≫ i) * (q ≫ i) := by simp only [hi, map_mul]
        _ = x ≫ (i ⊗ₘ i) ≫ μ[H.X] := by
          have hl : lift (p ≫ i) (q ≫ i) = x ≫ (i ⊗ₘ i) := by
            apply CartesianMonoidalCategory.hom_ext <;> simp [p, q]
          simp only [Hom.mul_def, hl, Category.assoc]
  exact ⟨Grp.homMk i, hi⟩

end IntegralPoints

section OrderedFrame

open IntegralSmoothnessSpecification
open ShortDirectionSpecification (IntegralPresentation)
open TrialitySpecification (Model modelOp frameStabilizer mapModel relatedTriples)
open IdempotentSpecification (IsSplitAutomorphism)
open FrameSpecification (frameAxis)
open CubicSpecification (cubicUnit)
open _root_.LinearAlgebraicGroups.Composition (Zorn)
open Composition.ZornSpecification (norm mapCoordinates)
open scoped TensorProduct

open private integralZornIsometry scalarIsometry scalarIsometry_spin scalarIsometry_natural
  zornBasis spinRelatedEquiv spinRelated_spec spinRelated_naturality
  extendedClifford extendedClifford_vector scalarOctonion map_scalarOctonion
  clifford_vector_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality
open private modelBaseChange_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic

private abbrev HyperbolicSpin (S : ScalarTest) :=
  SpinFunctor.Spin (integralForm 4) S (hyperbolicBasis ℤ 4)

private abbrev OctonionSpin (S : ScalarTest) :=
  SpinFunctor.Spin (norm ℤ) S (zornBasis ℤ)

private def hyperbolicToOctonion (S : ScalarTest) : HyperbolicSpin S ≃* OctonionSpin S := by
  let A := scalarIsometry S integralZornIsometry
  refine
    { toFun := fun s => ⟨Units.map A.toMonoidHom s.val, scalarIsometry_spin S _ s.property⟩
      invFun := fun s => ⟨Units.map A.symm.toMonoidHom s.val,
        scalarIsometry_spin S integralZornIsometry.symm s.property⟩
      left_inv := fun s => Subtype.ext (Units.ext (A.symm_apply_apply s.val.val))
      right_inv := fun s => Subtype.ext (Units.ext (A.apply_symm_apply s.val.val))
      map_mul' := fun s t => Subtype.ext (map_mul (Units.map A.toMonoidHom) s.val t.val) }

private theorem hyperbolicToOctonion_natural {S T : ScalarTest} (f : S ⟶ T)
    (s : HyperbolicSpin S) :
    hyperbolicToOctonion T (SpinFunctor.map _ _ f.hom s) =
      SpinFunctor.map _ _ f.hom (hyperbolicToOctonion S s) := by
  apply Subtype.ext
  apply Units.ext
  exact scalarIsometry_natural S integralZornIsometry f.hom s.val.val

private def spinTriple (S : ScalarTest) : HyperbolicSpin S ≃* relatedTriples (R := S) :=
  (hyperbolicToOctonion S).trans (spinRelatedEquiv ℤ S)

private def spinFrame (S : ScalarTest) : HyperbolicSpin S ≃* frameStabilizer (R := S) :=
  (spinTriple S).trans (Triality.frameTriality S).choose

private theorem spinFrame_action (S : ScalarTest) (s : HyperbolicSpin S) (x : Model S) :
    (spinFrame S s).val x = (x.1, fun i => (spinTriple S s).val i (x.2 i)) :=
  (Triality.frameTriality S).choose_spec _ _

private theorem spinFrame_natural {S T : ScalarTest} (f : S ⟶ T) (s : HyperbolicSpin S)
    (x : Model S) :
    mapModel f.hom.toRingHom ((spinFrame S s).val x) =
      (spinFrame T (SpinFunctor.map _ _ f.hom s)).val (mapModel f.hom.toRingHom x) := by
  rw [spinFrame_action, spinFrame_action]
  refine Prod.ext rfl ?_
  funext j
  change mapCoordinates f.hom.toRingHom
      ((spinRelatedEquiv ℤ S (hyperbolicToOctonion S s)).val j (x.2 j)) =
    (spinRelatedEquiv ℤ T (hyperbolicToOctonion T _)).val j
      (mapCoordinates f.hom.toRingHom (x.2 j))
  rw [hyperbolicToOctonion_natural]
  exact spinRelated_naturality ℤ f.hom (hyperbolicToOctonion S s) j (x.2 j)

private theorem splitAction_ext {S T : ScalarTest} (f : S ⟶ T)
    {g h : Model T ≃ₗ[T] Model T}
    (eqOn : ∀ x : Model S, g (mapModel f.hom.toRingHom x) =
      h (mapModel f.hom.toRingHom x)) : g = h := by
  let : Algebra S T := f.hom.toAlgebra
  apply LinearEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := (TrialitySpecification.modelBaseChange S T).surjective y
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    have hx : TrialitySpecification.modelBaseChange S T (r ⊗ₜ[S] x) =
        r • mapModel f.hom.toRingHom x := modelBaseChange_tmul r x
    rw [hx, map_smul, map_smul, eqOn]
  | add z w hz hw => simp only [map_add, hz, hw]

variable {P : IntegralPresentation} (G : SplitGroup P)

private theorem exists_spinAlbert (S : ScalarTest) (s : HyperbolicSpin S) :
    ∃ p, G.action S p = (spinFrame S s).val := by
  have h : (spinFrame S s).val ∈ {g | IsSplitAutomorphism g} := by
    refine ⟨?_, (spinFrame S s).property.2⟩
    rw [spinFrame_action]
    exact Prod.ext rfl (funext fun i => ((spinTriple S s).val i).map_zero)
  rw [← G.image S] at h
  exact h

private def spinAlbert (S : ScalarTest) : HyperbolicSpin S →* ScalarPoints G.group S where
  toFun s := (exists_spinAlbert G S s).choose
  map_one' := G.injective S (by
    rw [(exists_spinAlbert G S 1).choose_spec, map_one, Subgroup.coe_one, map_one])
  map_mul' s t := G.injective S (by
    rw [(exists_spinAlbert G S (s * t)).choose_spec, map_mul, Subgroup.coe_mul, map_mul,
      (exists_spinAlbert G S s).choose_spec, (exists_spinAlbert G S t).choose_spec])

private theorem spinAlbert_action (S : ScalarTest) (s : HyperbolicSpin S) :
    G.action S (spinAlbert G S s) = (spinFrame S s).val :=
  (exists_spinAlbert G S s).choose_spec

private theorem spinAlbert_injective (S : ScalarTest) : Function.Injective (spinAlbert G S) := by
  intro s t heq
  apply (spinFrame S).injective
  apply Subtype.ext
  simpa only [spinAlbert_action] using congrArg (G.action S) heq

private theorem spinAlbert_of_fixesFrame (S : ScalarTest) (g : ScalarPoints G.group S)
    (fixes : ∀ i, G.action S g (frameAxis i) = frameAxis i) :
    ∃ s, spinAlbert G S s = g := by
  have hg : G.action S g ∈ {g | IsSplitAutomorphism g} := by
    rw [← G.image S]
    exact Set.mem_range_self g
  obtain ⟨s, hs⟩ := (spinFrame S).surjective ⟨G.action S g, fixes, hg.2⟩
  refine ⟨s, G.injective S ?_⟩
  rw [spinAlbert_action]
  exact congrArg Subtype.val hs

private theorem spinAlbert_natural {S T : ScalarTest} (f : S ⟶ T) (s : HyperbolicSpin S) :
    spinAlbert G T (SpinFunctor.map _ _ f.hom s) =
      scalarSpec.map f.op ≫ spinAlbert G S s := by
  apply G.injective T
  apply splitAction_ext f
  intro x
  rw [← G.natural, spinAlbert_action, spinAlbert_action]
  exact (spinFrame_natural f s x).symm

open private diagonalLift_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights

private def torusPointMap (S : ScalarTest) : ScalarPoints diagonalTorus S →* ScalarPoints G.group S :=
  (spinAlbert G S).comp (diagonalLift.comp (diagonalPoints S).toMonoidHom)

private theorem torusPointMap_natural {S T : ScalarTest} (f : S ⟶ T)
    (t : ScalarPoints diagonalTorus S) :
    torusPointMap G T (scalarSpec.map f.op ≫ t) = scalarSpec.map f.op ≫ torusPointMap G S t := by
  change spinAlbert G T (diagonalLift (diagonalPoints T (scalarSpec.map f.op ≫ t))) =
    scalarSpec.map f.op ≫ spinAlbert G S (diagonalLift (diagonalPoints S t))
  rw [diagonalPoints_natural, ← diagonalLift_natural, spinAlbert_natural]

private theorem exists_torusInclusion : ∃ i : diagonalTorus ⟶ G.group,
    ∀ S t, t ≫ i.hom.hom = torusPointMap G S t :=
  integral_point_map _ _ (by change IsAffine (Spec (CommRingCat.of LaurentRing)); infer_instance)
    (torusPointMap G) (fun f t => torusPointMap_natural G f t)

private def torusInclusion := (exists_torusInclusion G).choose

private theorem torusInclusion_points (S : ScalarTest) (t : ScalarPoints diagonalTorus S) :
    t ≫ (torusInclusion G).hom.hom = spinAlbert G S (diagonalLift (diagonalPoints S t)) :=
  (exists_torusInclusion G).choose_spec S t

section WeightBases

open CliffordAlgebra Module
open _root_.LinearAlgebraicGroups.Composition (conjugate)
open Composition.ZornSpecification (first)
open scoped Matrix

open private splitBasis splitE splitF from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private middle_diagonal vectorEigenvalue creation contraction creation_operator contraction_operator
  coefficientMap_creation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights
open private create contract exteriorWord orderedIndices exteriorBasis_word
  wedgeProjector wedgeProjector_apply occupation matchingOccupation
  octonionBlock octonionBlock_zero octonionBlock_one octonionOperator_grade
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel
open private mapPair map_octonion_conj map_octonion_zero conjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality

private def vectorIdentification (S : ScalarTest) : ExtendedModule 4 S ≃ₗ[S] Zorn S :=
  (integralZornIsometry.toLinearEquiv.baseChange ℤ S _ _).trans (Zorn.baseChange ℤ S)

private def vectorBasis (S : ScalarTest) : Basis (PairIndex 4) S (Zorn S) :=
  ((splitBasis 4 S).reindex (ofLex : Lex (PairIndex 4) ≃ PairIndex 4)).map
    (vectorIdentification S)

private theorem vectorBasis_apply (S : ScalarTest) (i : PairIndex 4) :
    vectorBasis S i = vectorIdentification S ((splitBasis 4 S) (toLex i)) := by
  rw [vectorBasis, Basis.map_apply, Basis.reindex_apply]
  rfl

private theorem vectorBasis_repr (S : ScalarTest) (x : Zorn S) (i : PairIndex 4) :
    (vectorBasis S).repr x i =
      (splitBasis 4 S).repr ((vectorIdentification S).symm x) (toLex i) := by
  unfold vectorBasis
  rw [Basis.map_repr, LinearEquiv.trans_apply, Basis.repr_reindex, Finsupp.equivMapDomain_apply]
  rfl

private theorem vectorBasis_scalar (S : ScalarTest) (i : PairIndex 4) :
    vectorBasis S i = mapCoordinates (algebraMap ℤ S)
      (integralZornIsometry ((hyperbolicBasis ℤ 4) (toLex i))) := by
  rw [vectorBasis_apply]
  rw [Module.Basis.baseChange_apply]
  simp only [vectorIdentification, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    Zorn.baseChange_tmul, one_smul]
  rfl

private theorem vectorBasis_natural {S T : ScalarTest} (f : S ⟶ T) (i : PairIndex 4) :
    mapCoordinates f.hom.toRingHom (vectorBasis S i) = vectorBasis T i := by
  rw [vectorBasis_scalar, vectorBasis_scalar]
  generalize integralZornIsometry ((hyperbolicBasis ℤ 4) (toLex i)) = x
  rcases x with ⟨a, u, v, b⟩
  change (f.hom (algebraMap ℤ S a), f.hom ∘ (algebraMap ℤ S ∘ u),
      f.hom ∘ (algebraMap ℤ S ∘ v), f.hom (algebraMap ℤ S b)) =
    (algebraMap ℤ T a, algebraMap ℤ T ∘ u, algebraMap ℤ T ∘ v, algebraMap ℤ T b)
  simp [Function.comp_def]

private def octonionModel (S : ScalarTest) :
    ScalarClifford 4 S ≃ₐ[S] Module.End S (Zorn S × Zorn S) :=
  (scalarIsometry S integralZornIsometry).trans
    ((extendedClifford ℤ S).trans CliffordModel.octonionEquiv)

private theorem cliffordToOctonion_vector (S : ScalarTest) (x : ExtendedModule 4 S) :
    extendedClifford ℤ S (scalarIsometry S integralZornIsometry
      (SpinSpecification.vectors (integralForm 4) S x)) =
      CliffordAlgebra.ι (norm S) (vectorIdentification S x) := by
  let : Module ℤ S := Algebra.toModule
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change extendedClifford ℤ S (r ⊗ₜ[ℤ] CliffordAlgebra.map
      integralZornIsometry.toIsometry (CliffordAlgebra.ι (integralForm 4) x)) = _
    rw [map_apply_ι]
    exact extendedClifford_vector ℤ S (r ⊗ₜ[ℤ] integralZornIsometry x)
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem octonionModel_vector (S : ScalarTest) (x : ExtendedModule 4 S) :
    octonionModel S (SpinSpecification.vectors (integralForm 4) S x) =
      CliffordSpecification.octonionOperator (vectorIdentification S x) := by
  change CliffordModel.octonionEquiv (extendedClifford ℤ S
    (scalarIsometry S integralZornIsometry (SpinSpecification.vectors (integralForm 4) S x))) = _
  rw [cliffordToOctonion_vector, CliffordModel.octonionEquiv_ι]

private theorem spinVector_action (S : ScalarTest) (s : HyperbolicSpin S) :
    SpinSpecification.IsVectorAction (integralForm 4) S s.val
      ((vectorIdentification S).trans (((spinTriple S s).val 1).trans
        (vectorIdentification S).symm)) := by
  intro x
  apply (scalarIsometry S integralZornIsometry).injective
  apply (extendedClifford ℤ S).injective
  have h := (spinRelated_spec ℤ S (hyperbolicToOctonion S s)).2 (vectorIdentification S x)
  let C := ((scalarIsometry S integralZornIsometry).trans (extendedClifford ℤ S))
  let u := Units.map C.toMonoidHom s.val
  change C (SpinSpecification.vectors (integralForm 4) S
    (((vectorIdentification S).trans (((spinTriple S s).val 1).trans
      (vectorIdentification S).symm)) x)) =
    C (s.val.val * SpinSpecification.vectors (integralForm 4) S x * ↑s.val⁻¹)
  rw [map_mul, map_mul]
  change extendedClifford ℤ S (scalarIsometry S integralZornIsometry
    (SpinSpecification.vectors (integralForm 4) S _)) =
    u.val * extendedClifford ℤ S (scalarIsometry S integralZornIsometry
      (SpinSpecification.vectors (integralForm 4) S x)) * ↑u⁻¹
  rw [cliffordToOctonion_vector, cliffordToOctonion_vector]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change u.val * CliffordAlgebra.ι (norm S) (vectorIdentification S x) =
    CliffordAlgebra.ι (norm S) ((spinTriple S s).val 1 (vectorIdentification S x)) * u.val at h
  rw [h, mul_assoc, Units.mul_inv, mul_one]

set_option maxRecDepth 2048 in
private theorem spinVector_matrix (S : ScalarTest) (s : HyperbolicSpin S) :
    HasActionMatrix 4 s.val
      (LinearMap.toMatrix (vectorBasis S) (vectorBasis S) ((spinTriple S s).val 1).toLinearMap) := by
  refine ⟨_, spinVector_action S s, ?_⟩
  apply Matrix.ext (m := PairIndex 4) (n := PairIndex 4)
  intro i j
  change (LinearMap.toMatrix (splitBasis 4 S) (splitBasis 4 S) _) (toLex i) (toLex j) = _
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, vectorBasis_apply, vectorBasis_repr]
  rfl

open private action_matrix_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

private theorem diagonal_vectorWeight (S : ScalarTest) (t : DiagonalPoints S) (j : PairIndex 4) :
    (spinTriple S (diagonalLift t)).val 1 (vectorBasis S j) =
      (Additive.toMul (evaluate t (vectorWeight j)) : Sˣ).val • vectorBasis S j := by
  have h := action_matrix_unique (spinVector_matrix S (diagonalLift t)) (diagonalUnit_action t)
  rw [middle_diagonal] at h
  apply (vectorBasis S).repr.injective
  ext i
  have hi := congrFun (congrFun h i) j
  rw [LinearMap.toMatrix_apply] at hi
  change (vectorBasis S).repr ((spinTriple S (diagonalLift t)).val 1 (vectorBasis S j)) i =
    Matrix.diagonal (vectorEigenvalue t) i j at hi
  rw [hi, map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  have hv : (Additive.toMul (evaluate t (vectorWeight j)) : Sˣ).val = vectorEigenvalue t j := by
    cases j with
    | inl i => exact congrArg Units.val ((SpinWeights.weightEvaluation S t).1 i).1
    | inr i => exact congrArg Units.val ((SpinWeights.weightEvaluation S t).1 i).2
  rw [hv]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal_apply_ne _ hij, Ne.symm hij]

-- The cyclic vector for the exterior model sits in the first octonion block.
private def vacuum (S : ScalarTest) : Zorn S × Zorn S := (first S, 0)

private theorem contraction_vacuum (S : ScalarTest) (i : Fin 4) :
    octonionModel S (contraction i) (vacuum S) = 0 := by
  rw [octonionModel_vector]
  let x := integralZornIsometry ((hyperbolicBasis ℤ 4) (toLex (Sum.inr i)))
  have hx : (Zorn.hyperbolicCoordinates ℤ x).2 = 0 := by
    change (Zorn.hyperbolicIsometry ℤ
      (integralZornIsometry ((hyperbolicBasis ℤ 4) (toLex (Sum.inr i))))).2 = 0
    let f : (Fin 4 → ℤ) ≃ₗ[ℤ] (Option (Fin 3) → ℤ) :=
      LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivOfCardEq (by simp))
    change ((Zorn.hyperbolicIsometry ℤ) ((Zorn.hyperbolicIsometry ℤ).symm
      (f.symm.dualMap.prodCongr f ((hyperbolicBasis ℤ 4) (toLex (Sum.inr i)))))).2 = 0
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply]
    have hb : (hyperbolicBasis ℤ 4) (toLex (Sum.inr i)) =
        ((Pi.basisFun ℤ (Fin 4)).dualBasis i, 0) := by
      rw [hyperbolicBasis, Basis.reindex_apply]
      exact Prod.ext (Basis.prod_apply_inl_fst _ _ _) (Basis.prod_apply_inl_snd _ _ _)
    rw [hb]
    exact map_zero f
  have hv : vectorIdentification S (splitF i) = mapCoordinates (algebraMap ℤ S) x := by
    exact (vectorBasis_apply S (Sum.inr i)).symm.trans (vectorBasis_scalar S (Sum.inr i))
  rw [hv]
  obtain ⟨a, u, v, b⟩ := x
  have hb : b = 0 := congrFun hx none
  have hv' : v = 0 := funext fun j => neg_eq_zero.mp (congrFun hx (some j))
  subst b
  subst v
  apply Prod.ext
  · exact mul_zero _
  · change conjugate (norm S) (Zorn.ofCoordinates
      (algebraMap ℤ S a, algebraMap ℤ S ∘ u, algebraMap ℤ S ∘ 0, algebraMap ℤ S 0)) * first S = 0
    rw [Zorn.conjugate_formula]
    rw [show algebraMap ℤ S ∘ (0 : Fin 3 → ℤ) = 0 by funext j; exact map_zero _,
      map_zero, neg_zero]
    change Composition.Specification.zornProduct
      (0, -(algebraMap ℤ S ∘ u), 0, algebraMap ℤ S a) (1, 0, 0, 0) = 0
    simp [Composition.Specification.zornProduct]

private def compareModels (S : ScalarTest) :
    Module.End S (ExteriorSpace S) ≃ₐ[S] Module.End S (Zorn S × Zorn S) :=
  (exteriorModel S).symm.trans (octonionModel S)

private def vacuumRankOne (S : ScalarTest) (x : ExteriorSpace S) : Module.End S (ExteriorSpace S) :=
  (LinearMap.toSpanSingleton S _ x).comp ((eBasis S).coord ∅)

private def spinorMap (S : ScalarTest) : ExteriorSpace S →ₗ[S] Zorn S × Zorn S where
  toFun x := compareModels S (vacuumRankOne S x) (vacuum S)
  map_add' x y := by
    rw [show vacuumRankOne S (x + y) = vacuumRankOne S x + vacuumRankOne S y by
      apply LinearMap.ext
      intro z
      exact smul_add ((eBasis S).coord ∅ z) x y, map_add]
    rfl
  map_smul' r x := by
    rw [show vacuumRankOne S (r • x) = r • vacuumRankOne S x by
      apply LinearMap.ext
      intro z
      exact smul_comm ((eBasis S).coord ∅ z) r x, map_smul]
    rfl

private theorem spinorMap_intertwines (S : ScalarTest) (a : Module.End S (ExteriorSpace S))
    (x : ExteriorSpace S) :
    spinorMap S (a x) = compareModels S a (spinorMap S x) := by
  have h : a * vacuumRankOne S x = vacuumRankOne S (a x) := by
    apply LinearMap.ext
    intro z
    exact a.map_smul ((eBasis S).coord ∅ z) x
  change compareModels S (vacuumRankOne S (a x)) (vacuum S) = _
  rw [← h, map_mul, Module.End.mul_apply]
  rfl

private theorem spinorMap_clifford (S : ScalarTest) (c : ScalarClifford 4 S) (x : ExteriorSpace S) :
    spinorMap S (exteriorModel S c x) = octonionModel S c (spinorMap S x) := by
  rw [spinorMap_intertwines]
  change octonionModel S ((exteriorModel S).symm (exteriorModel S c)) (spinorMap S x) = _
  rw [AlgEquiv.symm_apply_apply]

private theorem spinorMap_one (S : ScalarTest) : spinorMap S 1 = vacuum S := by
  have hproj : vacuumRankOne S 1 = wedgeProjector (Pi.basisFun S (Fin 4)) ∅ := by
    apply (eBasis S).ext
    intro I
    rw [wedgeProjector_apply]
    have hb : eBasis S ∅ = 1 := by
      rw [show eBasis S ∅ = _ from ExteriorAlgebra.basis_apply _ _]
      exact ExteriorAlgebra.ιMulti_zero_apply _
    change (eBasis S).coord ∅ (eBasis S I) • (1 : ExteriorSpace S) =
      if ∅ = I then eBasis S I else 0
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases h : ∅ = I
    · simp [← h, hb]
    · simp [h, Ne.symm h]
  change compareModels S (vacuumRankOne S 1) (vacuum S) = _
  rw [hproj]
  let l := (Finset.univ : Finset (Fin 4)).toList
  change compareModels S ((l.map (matchingOccupation (Pi.basisFun S (Fin 4)) ∅)).prod)
    (vacuum S) = _
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]
    simp only [matchingOccupation, Finset.notMem_empty, ite_false, occupation, map_sub, map_one]
    rw [← creation_operator (K := S), ← contraction_operator (K := S), ← map_mul]
    change (1 - octonionModel S ((exteriorModel S).symm
      (exteriorModel S (creation i * contraction i)))) (vacuum S) = _
    rw [AlgEquiv.symm_apply_apply, map_mul]
    simp only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
      contraction_vacuum, map_zero, sub_zero]

private def spinorEquiv (S : ScalarTest) : ExteriorSpace S ≃ₗ[S] Zorn S × Zorn S := by
  let F := spinorMap S
  have hsurj : Function.Surjective F := by
    intro y
    let coord := (LinearMap.fst S S _).comp
      ((Zorn.coordinates S).toLinearMap.comp (LinearMap.fst S (Zorn S) (Zorn S)))
    let a := (LinearMap.toSpanSingleton S _ y).comp coord
    refine ⟨(compareModels S).symm a 1, ?_⟩
    change spinorMap S _ = y
    rw [spinorMap_intertwines, spinorMap_one, AlgEquiv.apply_symm_apply]
    change (1 : S) • y = y
    exact one_smul S y
  let b := eBasis S
  refine LinearEquiv.ofBijective F ?_
  by_cases hS : Subsingleton S
  · let := hS
    let := Module.subsingleton S (ExteriorSpace S)
    exact ⟨Function.injective_of_subsingleton _, hsurj⟩
  let : Nontrivial S := not_subsingleton_iff_nontrivial.mp hS
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  apply OrzechProperty.bijective_of_surjective_of_finrank_le F hsurj
  rw [Module.finrank_eq_card_basis b,
    Module.finrank_eq_card_basis ((Zorn.coordinateBasis S).prod (Zorn.coordinateBasis S))]
  simp [Fintype.card_finset]

private theorem spinorEquiv_word (S : ScalarTest) (l : List (Fin 4)) :
    spinorEquiv S (exteriorWord (Pi.basisFun S (Fin 4)) l) =
      octonionModel S ((l.map (creation (K := S))).prod) (vacuum S) := by
  induction l with
  | nil =>
    change spinorMap S 1 = octonionModel S 1 (vacuum S)
    rw [spinorMap_one, map_one, Module.End.one_apply]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← ih]
    change spinorMap S ((create (Pi.basisFun S (Fin 4) i))
      (exteriorWord (Pi.basisFun S (Fin 4)) l)) = _
    rw [← creation_operator (K := S), spinorMap_clifford]
    rfl

private def spinorBasis (S : ScalarTest) : Basis (Finset (Fin 4)) S (Zorn S × Zorn S) :=
  (eBasis S).map (spinorEquiv S)

private theorem spinorBasis_parity (S : ScalarTest) (I : Finset (Fin 4)) :
    spinorBasis S I ∈ octonionBlock S (I.card : ZMod 2) := by
  have hw (l : List (Fin 4)) : octonionModel S ((l.map (creation (K := S))).prod) (vacuum S) ∈
      octonionBlock S (l.length : ZMod 2) := by
    induction l with
    | nil => simp [vacuum, octonionBlock_zero]
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, octonionModel_vector]
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm] using
        octonionOperator_grade (l.length : ZMod 2) _ _ ih
  change spinorEquiv S (eBasis S I) ∈ _
  rw [exteriorBasis_word, spinorEquiv_word]
  exact (show (orderedIndices I).length = I.card by simp [orderedIndices]) ▸ hw (orderedIndices I)

private theorem spinorBasis_natural {S T : ScalarTest} (f : S ⟶ T) (I : Finset (Fin 4)) :
    mapPair f.hom.toRingHom (spinorBasis S I) = spinorBasis T I := by
  change mapPair f.hom.toRingHom (spinorEquiv S (eBasis S I)) = spinorEquiv T (eBasis T I)
  rw [exteriorBasis_word, exteriorBasis_word, spinorEquiv_word, spinorEquiv_word]
  let l := orderedIndices I
  let s := (l.map (creation (K := S))).prod
  let t := (l.map (creation (K := T))).prod
  have ht : SpinSpecification.coefficientMap (integralForm 4) S f.hom s = t := by
    dsimp only [s, t]
    rw [map_list_prod, List.map_map]
    simp only [Function.comp_def, coefficientMap_creation]
  have hv : mapPair f.hom.toRingHom (vacuum S) = vacuum T := by
    refine Prod.ext ?_ (map_octonion_zero _)
    simp [mapPair, vacuum, first, mapCoordinates, Function.comp_def]
    rfl
  change mapPair f.hom.toRingHom
    (scalarOctonion ℤ S (scalarIsometry S integralZornIsometry s) (vacuum S)) = _
  rw [map_scalarOctonion, ← scalarIsometry_natural, ht, hv]
  rfl

private def spinorProjection (S : ScalarTest) (p : Bool) : Zorn S × Zorn S →ₗ[S] Zorn S :=
  if p then LinearMap.snd S _ _ else
    (conjugation (R := S)).toLinearMap.comp (LinearMap.fst S _ _)

private def spinorInjection (S : ScalarTest) (p : Bool) : Zorn S →ₗ[S] Zorn S × Zorn S :=
  if p then LinearMap.inr S _ _ else
    (LinearMap.inl S _ _).comp (conjugation (R := S)).symm.toLinearMap

private theorem spinorProjection_injection (S : ScalarTest) (p : Bool) (x : Zorn S) :
    spinorProjection S p (spinorInjection S p x) = x := by
  cases p
  · exact (conjugation (R := S)).apply_symm_apply x
  · rfl

private theorem spinorBasis_injection (S : ScalarTest) (p : Bool) (I : WedgeIndex p) :
    spinorInjection S p (spinorProjection S p (spinorBasis S I.val)) = spinorBasis S I.val := by
  have h := spinorBasis_parity S I.val
  rw [← ZMod.natCast_mod I.val.card 2, I.property] at h
  cases p
  · have h₀ := (octonionBlock_zero _).mp h
    exact Prod.ext ((conjugation (R := S)).symm_apply_apply _) h₀.symm
  · exact Prod.ext ((octonionBlock_one _).mp h).symm rfl

private theorem spinorProjection_eq_zero (S : ScalarTest) (p : Bool) (I : Finset (Fin 4))
    (hI : I.card % 2 ≠ p.toNat) :
    spinorProjection S p (spinorBasis S I) = 0 := by
  have h := spinorBasis_parity S I
  rw [← ZMod.natCast_mod I.card 2] at h
  cases p
  · have hmod : I.card % 2 = 1 := by change I.card % 2 ≠ 0 at hI; omega
    rw [hmod] at h
    change (conjugation (R := S)) (spinorBasis S I).1 = 0
    rw [(octonionBlock_one _).mp h, map_zero]
  · have hmod : I.card % 2 = 0 := by change I.card % 2 ≠ 1 at hI; omega
    rw [hmod] at h
    exact (octonionBlock_zero _).mp h

private def halfBasis (S : ScalarTest) (p : Bool) : Basis (WedgeIndex p) S (Zorn S) := by
  classical
  let v (I : WedgeIndex p) := spinorProjection S p (spinorBasis S I.val)
  have hlin : LinearIndependent S v := by
    apply LinearIndependent.of_comp (spinorInjection S p)
    convert (spinorBasis S).linearIndependent.comp Subtype.val Subtype.val_injective using 1
    funext I
    exact spinorBasis_injection S p I
  refine Basis.mk hlin ?_
  intro x _
  have h := congrArg (spinorProjection S p)
    ((spinorBasis S).sum_repr (spinorInjection S p x))
  rw [spinorProjection_injection, map_sum] at h
  rw [← h]
  apply Submodule.sum_mem
  intro I _
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases hI : I.card % 2 = p.toNat
  · exact Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩
  · rw [spinorProjection_eq_zero S p I hI]
    exact Submodule.zero_mem _

set_option maxHeartbeats 900000 in
private theorem halfBasis_apply (S : ScalarTest) (p : Bool) (I : WedgeIndex p) :
    halfBasis S p I = spinorProjection S p (spinorBasis S I.val) := by
  unfold halfBasis
  exact Basis.mk_apply _ _ _

set_option maxHeartbeats 900000 in
private theorem halfBasis_natural {S T : ScalarTest} (f : S ⟶ T) (p : Bool)
    (I : WedgeIndex p) :
    mapCoordinates f.hom.toRingHom (halfBasis S p I) = halfBasis T p I := by
  simp only [halfBasis_apply]
  have h := spinorBasis_natural f I.val
  cases p
  · change mapCoordinates f.hom.toRingHom
      (conjugate (norm S) (spinorBasis S I.val).1) = conjugate (norm T) (spinorBasis T I.val).1
    rw [map_octonion_conj]
    have h₁ : mapCoordinates f.hom.toRingHom (spinorBasis S I.val).1 =
        (spinorBasis T I.val).1 := congrArg Prod.fst h
    rw [h₁]
  · exact congrArg Prod.snd h

open private conj_conj from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality

private theorem diagonal_halfWeight (S : ScalarTest) (t : DiagonalPoints S) (p : Bool)
    (I : WedgeIndex p) :
    (spinTriple S (diagonalLift t)).val (halfSpinBlock p) (halfBasis S p I) =
      (Additive.toMul (evaluate t (exteriorWeight I.val)) : Sˣ).val • halfBasis S p I := by
  simp only [halfBasis_apply]
  let s := diagonalLift t
  let w := (Additive.toMul (evaluate t (exteriorWeight I.val)) : Sˣ).val
  let v := spinorBasis S I.val
  have hw : exteriorModel S s.val (eBasis S I.val) = w • eBasis S I.val := by
    dsimp only [w]
    rw [(SpinWeights.weightEvaluation S t).2]
    exact diagonalUnit_wedge t I.val
  have hv := spinorMap_clifford S s.val.val (eBasis S I.val)
  rw [hw, map_smul] at hv
  change w • v = octonionModel S s.val.val v at hv
  have hrep := (spinRelated_spec ℤ S (hyperbolicToOctonion S s)).1 v.1 v.2
  change octonionModel S s.val.val v =
    (conjugate (norm S) ((spinTriple S s).val 0 (conjugate (norm S) v.1)),
      (spinTriple S s).val 2 v.2) at hrep
  rw [hrep] at hv
  cases p
  · change (spinTriple S s).val 0 (conjugate (norm S) v.1) = w • conjugate (norm S) v.1
    have h := congrArg (fun z : Zorn S × Zorn S => conjugate (norm S) z.1) hv
    change conjugate (norm S) (w • v.1) =
      conjugate (norm S) (conjugate (norm S) ((spinTriple S s).val 0 (conjugate (norm S) v.1))) at h
    rw [map_smul, conj_conj] at h
    exact h.symm
  · exact (congrArg Prod.snd hv).symm

end WeightBases

section ModelWeights

open Module
open CubicSpecification (singleBlockCoordinates)
open private map_octonion_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality
open private mapModel_add from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
open private mapModel_smul mapModel_axis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

private abbrev BlockIndex := WedgeIndex false ⊕ (PairIndex 4 ⊕ WedgeIndex true)
private abbrev ModelIndex := Fin 3 ⊕ BlockIndex

private def blockNumber : BlockIndex → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

private def blockVector (S : ScalarTest) : BlockIndex → Zorn S
  | .inl I => halfBasis S false I
  | .inr (.inl i) => vectorBasis S i
  | .inr (.inr I) => halfBasis S true I

private def modelWeight : ModelIndex → CharacterExponents
  | .inl _ => 0
  | .inr (.inl I) => exteriorWeight I.val
  | .inr (.inr (.inl i)) => vectorWeight i
  | .inr (.inr (.inr I)) => exteriorWeight I.val

private def threeBlocks (S : ScalarTest) :
    (Fin 3 → Zorn S) ≃ₗ[S] Zorn S × (Zorn S × Zorn S) where
  toFun c := (c 0, c 1, c 2)
  invFun c := ![c.1, c.2.1, c.2.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := by funext i; fin_cases i <;> rfl
  right_inv c := rfl

private def modelBasis (S : ScalarTest) : Basis ModelIndex S (Model S) :=
  ((Pi.basisFun S (Fin 3)).prod
    ((halfBasis S false).prod ((vectorBasis S).prod (halfBasis S true)))).map
    ((LinearEquiv.refl S (Fin 3 → S)).prodCongr (threeBlocks S).symm)

private theorem modelBasis_axis (S : ScalarTest) (i : Fin 3) :
    modelBasis S (.inl i) = frameAxis i := by
  rw [modelBasis, Basis.map_apply]
  simp only [LinearEquiv.prodCongr_apply, Basis.prod_apply_inl_fst,
    Basis.prod_apply_inl_snd, LinearEquiv.refl_apply, map_zero, Pi.basisFun_apply]
  rfl

private theorem modelBasis_block (S : ScalarTest) (i : BlockIndex) :
    modelBasis S (.inr i) = singleBlockCoordinates (blockNumber i) (blockVector S i) := by
  rw [modelBasis, Basis.map_apply, LinearEquiv.prodCongr_apply,
    Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd, LinearEquiv.refl_apply]
  refine Prod.ext rfl ?_
  apply (threeBlocks S).injective
  rw [LinearEquiv.apply_symm_apply]
  have hsingle (k : Fin 3) (v : Zorn S) :
      threeBlocks S (singleBlockCoordinates (R := S) k v).2 =
        (if k = 0 then v else 0, if k = 1 then v else 0, if k = 2 then v else 0) := by
    change (Pi.single (M := fun _ : Fin 3 => Zorn S) k v 0,
      Pi.single (M := fun _ : Fin 3 => Zorn S) k v 1,
      Pi.single (M := fun _ : Fin 3 => Zorn S) k v 2) = _
    fin_cases k <;> rfl
  rw [hsingle]
  rcases i with I | j | I
  · refine Prod.ext ?_ ?_
    · rw [Basis.prod_apply_inl_fst]
      simp [blockVector, blockNumber]
    · rw [Basis.prod_apply_inl_snd]
      rfl
  · simp only [blockNumber, blockVector]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [Basis.prod_apply_inr_fst]
      rfl
    · rw [Basis.prod_apply_inr_snd, Basis.prod_apply_inl_fst]
      simp
    · rw [Basis.prod_apply_inr_snd, Basis.prod_apply_inl_snd]
      simp
  · simp only [blockNumber, blockVector]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [Basis.prod_apply_inr_fst]
      rfl
    · rw [Basis.prod_apply_inr_snd, Basis.prod_apply_inr_fst]
      simp
    · rw [Basis.prod_apply_inr_snd, Basis.prod_apply_inr_snd]
      simp

private theorem mapModel_block {S T : ScalarTest} (f : S ⟶ T) (i : Fin 3) (x : Zorn S) :
    mapModel f.hom.toRingHom (singleBlockCoordinates i x) =
      singleBlockCoordinates i (mapCoordinates f.hom.toRingHom x) := by
  refine Prod.ext (funext fun j => map_zero f.hom) (funext fun j => ?_)
  change mapCoordinates f.hom.toRingHom (Pi.single (M := fun _ : Fin 3 => Zorn S) i x j) =
    Pi.single (M := fun _ : Fin 3 => Zorn T) i (mapCoordinates f.hom.toRingHom x) j
  by_cases h : j = i
  · simp [h]
  · simp [Pi.single_eq_of_ne h, map_octonion_zero]

private theorem modelBasis_natural {S T : ScalarTest} (f : S ⟶ T) (j : ModelIndex) :
    mapModel f.hom.toRingHom (modelBasis S j) = modelBasis T j := by
  cases j with
  | inl i => simp only [modelBasis_axis, mapModel_axis]
  | inr j =>
    rw [modelBasis_block, modelBasis_block, mapModel_block]
    rcases j with I | i | I
    · exact congrArg (singleBlockCoordinates 0) (halfBasis_natural f false I)
    · exact congrArg (singleBlockCoordinates 1) (vectorBasis_natural f i)
    · exact congrArg (singleBlockCoordinates 2) (halfBasis_natural f true I)

private def mapModelLinear {S T : ScalarTest} (f : S ⟶ T) :
    Model S →ₛₗ[f.hom.toRingHom] Model T where
  toFun := mapModel f.hom.toRingHom
  map_add' := mapModel_add _
  map_smul' := mapModel_smul _

private theorem modelBasis_repr_natural {S T : ScalarTest} (f : S ⟶ T) (x : Model S)
    (j : ModelIndex) :
    (modelBasis T).repr (mapModel f.hom.toRingHom x) j = f.hom ((modelBasis S).repr x j) := by
  classical
  have hx := congrArg (mapModelLinear f) ((modelBasis S).sum_repr x)
  rw [map_sum] at hx
  simp only [map_smulₛₗ] at hx
  change (∑ i : ModelIndex, f.hom ((modelBasis S).repr x i) •
      mapModel f.hom.toRingHom (modelBasis S i)) = mapModel f.hom.toRingHom x at hx
  simp only [modelBasis_natural] at hx
  rw [← hx, map_sum]
  simp only [Finsupp.finsetSum_apply, map_smul, Basis.repr_self, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable {P : IntegralPresentation} (G : SplitGroup P)

private theorem torus_blockAction (S : ScalarTest) (t : ScalarPoints diagonalTorus S)
    (x : Model S) :
    G.action S (t ≫ (torusInclusion G).hom.hom) x =
      (x.1, fun i => (spinTriple S (diagonalLift (diagonalPoints S t))).val i (x.2 i)) := by
  rw [torusInclusion_points, spinAlbert_action, spinFrame_action]

private theorem torus_action_basis (S : ScalarTest) (t : ScalarPoints diagonalTorus S)
    (i : ModelIndex) :
    G.action S (t ≫ (torusInclusion G).hom.hom) (modelBasis S i) =
      (Additive.toMul (evaluate (diagonalPoints S t) (modelWeight i)) : Sˣ).val • modelBasis S i := by
  let d := diagonalPoints S t
  let h := (spinTriple S (diagonalLift d)).val
  cases i with
  | inl i =>
    rw [modelBasis_axis, torusInclusion_points, spinAlbert_action, modelWeight, map_zero]
    change (spinFrame S (diagonalLift d)).val (frameAxis i) = (1 : S) • frameAxis i
    rw [one_smul]
    exact (spinFrame S (diagonalLift d)).property.1 i
  | inr j =>
    simp only [modelBasis_block, torus_blockAction]
    let w := (Additive.toMul (evaluate d (modelWeight (.inr j))) : Sˣ).val
    have hweight : h (blockNumber j) (blockVector S j) = w • blockVector S j := by
      rcases j with I | i | I
      · exact diagonal_halfWeight S d false I
      · exact diagonal_vectorWeight S d i
      · exact diagonal_halfWeight S d true I
    apply Prod.ext
    · change (0 : Fin 3 → S) = w • 0
      simp
    · funext i
      change h i (Pi.single (M := fun _ : Fin 3 => Zorn S) (blockNumber j) (blockVector S j) i) =
        w • Pi.single (M := fun _ : Fin 3 => Zorn S) (blockNumber j) (blockVector S j) i
      by_cases hi : i = blockNumber j
      · subst i
        simpa only [Pi.single_eq_same] using hweight
      · simp [Pi.single_eq_of_ne hi]

private theorem monomial_zero : monomial 0 = 1 :=
  (MonoidAlgebra.of ℤ CharacterGroup).map_one

private theorem monomial_add (a b : CharacterExponents) : monomial (a + b) = monomial a * monomial b :=
  (MonoidAlgebra.of ℤ CharacterGroup).map_mul _ _

private theorem monomials_generate {R : Type} [CommRing R] [Algebra ℤ R] (f : R →ₐ[ℤ] LaurentRing)
    (h : ∀ a ∈ insert (-halfSum) (Set.range (fun i : Fin 3 => epsilon i.succ)),
      monomial a ∈ f.range ∧ monomial (-a) ∈ f.range) : Function.Surjective f := by
  have hzero : monomial 0 ∈ f.range := monomial_zero.symm ▸ f.range.one_mem
  have hadd {a b : CharacterExponents} (ha : monomial a ∈ f.range) (hb : monomial b ∈ f.range) :
      monomial (a + b) ∈ f.range := monomial_add a b ▸ f.range.mul_mem ha hb
  have hzsmul (a : CharacterExponents) (ha : monomial a ∈ f.range ∧ monomial (-a) ∈ f.range)
      (n : ℤ) : monomial (n • a) ∈ f.range := by
    induction n using Int.induction_on with
    | zero => simpa only [zero_smul] using hzero
    | succ i ih => simpa only [add_zsmul, one_zsmul] using hadd ih ha.1
    | pred i ih => simpa only [sub_eq_add_neg, add_zsmul, neg_one_zsmul] using hadd ih ha.2
  have hsum (s : Finset (Fin 3)) (a : Fin 3 → CharacterExponents)
      (ha : ∀ i, monomial (a i) ∈ f.range) : monomial (∑ i ∈ s, a i) ∈ f.range := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert i s hi ih => simpa only [Finset.sum_insert hi] using hadd (ha i) ih
  have hexp (a : CharacterExponents) : monomial a ∈ f.range := by
    rw [exponentExpansion a]
    apply hadd (hzsmul _ (h _ (Set.mem_insert _ _)) _)
    exact hsum _ _ (fun i => hzsmul _ (h _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)) _)
  intro x
  change x ∈ f.range
  have hspan : Submodule.span ℤ (Set.range (MonoidAlgebra.basis CharacterGroup ℤ)) ≤
      f.range.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change monomial c.toAdd ∈ f.range
    exact hexp c.toAdd
  rw [(MonoidAlgebra.basis CharacterGroup ℤ).span_eq] at hspan
  exact hspan (Submodule.mem_top (x := x))

set_option backward.isDefEq.respectTransparency false in
private theorem torusMonomial_identity (x : CharacterExponents) :
    let L := CommAlgCat.of ℤ LaurentRing
    (Additive.toMul (evaluate (diagonalPoints L (𝟙 diagonalTorus.X)) x) : LaurentRingˣ).val =
      monomial x := by
  let L := CommAlgCat.of ℤ LaurentRing
  have h := torusMonomial L (AlgHom.id ℤ LaurentRing) x
  have hid : scalarSpec.map (CommAlgCat.ofHom (AlgHom.id ℤ LaurentRing)).op = 𝟙 diagonalTorus.X :=
    scalarSpec.map_id (op L)
  rw [hid] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem torusInclusion_closed : IsClosedImmersion (torusInclusion G).hom.hom.left := by
  let B := CommAlgCat.of ℤ P.Coordinates
  let L := CommAlgCat.of ℤ LaurentRing
  let fa := algSpec.fullyFaithful (R := CommRingCat.of ℤ)
  let i := (torusInclusion G).hom.hom
  let p : ScalarPoints G.group B := G.coordinates.inv
  let f : P.Coordinates →ₐ[ℤ] LaurentRing := (fa.preimage (i ≫ G.coordinates.hom)).unop.hom
  have hf : scalarSpec.map (CommAlgCat.ofHom f).op = i ≫ G.coordinates.hom := fa.map_preimage _
  have hp : scalarSpec.map (CommAlgCat.ofHom f).op ≫ p = i := by
    rw [hf, Category.assoc]
    simp [p]
  have hmem (j : ModelIndex) : monomial (modelWeight j) ∈ f.range := by
    let c := (modelBasis B).repr (G.action B p (modelBasis B j)) j
    refine ⟨c, ?_⟩
    have hnat := G.natural (CommAlgCat.ofHom f) p (modelBasis B j)
    rw [hp, modelBasis_natural] at hnat
    have hact : G.action L i (modelBasis L j) = monomial (modelWeight j) • modelBasis L j := by
      have he := torus_action_basis G L (𝟙 diagonalTorus.X) j
      have hid : (𝟙 diagonalTorus.X) ≫ i = i := Category.id_comp _
      change G.action L ((𝟙 diagonalTorus.X) ≫ i) (modelBasis L j) = _ at he
      rw [hid, torusMonomial_identity (modelWeight j)] at he
      exact he
    have hm := modelBasis_repr_natural (CommAlgCat.ofHom f) (G.action B p (modelBasis B j)) j
    rw [hnat, hact] at hm
    change (modelBasis L).repr (monomial (modelWeight j) • modelBasis L j) j = f c at hm
    rw [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at hm
    exact hm.symm
  have hsurj : Function.Surjective f := by
    apply monomials_generate
    intro a ha
    rcases ha with rfl | ⟨i, rfl⟩
    · have hempty : exteriorWeight ∅ = -halfSum := by simp [exteriorWeight]
      have huniv : exteriorWeight Finset.univ = halfSum := by
        have hh : ∑ i, epsilon i = (2 : ℤ) • halfSum := SpinWeights.halfSumRelation.symm
        rw [exteriorWeight, hh, two_zsmul, add_sub_cancel_right]
      refine ⟨?_, ?_⟩
      · simpa only [modelWeight, hempty] using hmem (.inr (.inl ⟨∅, by decide⟩))
      · simpa only [modelWeight, huniv, neg_neg] using hmem (.inr (.inl ⟨Finset.univ, by decide⟩))
    · exact ⟨hmem (.inr (.inr (.inl (.inl i.succ)))), hmem (.inr (.inr (.inl (.inr i.succ))))⟩
  have hcl : IsClosedImmersion (i.left ≫ G.coordinates.hom.left) := by
    rw [← Over.comp_left, ← hf]
    exact IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.toRingHom) hsurj
  exact IsClosedImmersion.of_comp_isClosedImmersion i.left G.coordinates.hom.left

private def doubledWeight : CharacterExponents →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun x i := Fin.cases (-x.1) (fun j => 2 * x.2 j - x.1) i
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change -(x.1 + y.1) = -x.1 + -y.1
      ring
    · change 2 * (x.2 j + y.2 j) - (x.1 + y.1) =
        2 * x.2 j - x.1 + (2 * y.2 j - y.1)
      ring
  map_smul' n x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change -(n * x.1) = n * (-x.1)
      ring
    · change 2 * (n * x.2 j) - n * x.1 = n * (2 * x.2 j - x.1)
      ring

private theorem doubled_epsilon (i j : Fin 4) :
    doubledWeight (epsilon i) j = if j = i then 2 else 0 := by
  have h (x : VectorExponents) (j : Fin 4) : doubledWeight (vectorPullback x) j = 2 * x j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · change -(-2 * x 0) = 2 * x 0
      ring
    · change 2 * (x j.succ - x 0) - (-2 * x 0) = 2 * x j.succ
      ring
  rw [epsilon, h]
  simp only [coordinate, Pi.single_apply]
  split <;> simp

private theorem doubled_exterior (I : Finset (Fin 4)) (i : Fin 4) :
    doubledWeight (exteriorWeight I) i = if i ∈ I then 1 else -1 := by
  have hhalf : doubledWeight halfSum i = 1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change 2 * 0 - (-1) = 1
      norm_num
  simp only [exteriorWeight, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, doubled_epsilon, hhalf]
  by_cases hi : i ∈ I <;> simp [hi]

private def vectorIndex : PairIndex 4 → Fin 4 := Sum.elim id id

private def vectorSign : PairIndex 4 → ℤ := Sum.elim (fun _ => 2) (fun _ => -2)

private theorem doubled_vector (i : PairIndex 4) (j : Fin 4) :
    doubledWeight (vectorWeight i) j = if j = vectorIndex i then vectorSign i else 0 := by
  cases i with
  | inl i => exact doubled_epsilon i j
  | inr i =>
    change doubledWeight (-epsilon i) j = _
    rw [map_neg, Pi.neg_apply, doubled_epsilon]
    by_cases h : j = i <;> simp [vectorIndex, vectorSign, h]

private theorem weight_exterior_injective : Function.Injective exteriorWeight := by
  intro I J h
  ext i
  have hh := congrArg (fun x => doubledWeight x i) h
  simp only [doubled_exterior] at hh
  by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp_all

private theorem weight_vector_injective : Function.Injective vectorWeight := by
  intro i j h
  have hval := congrArg (fun x => doubledWeight x (vectorIndex i)) h
  simp only [doubled_vector, ite_true] at hval
  have hind : vectorIndex i = vectorIndex j := by
    by_contra hn
    simp only [hn, ite_false] at hval
    cases i <;> norm_num [vectorSign] at hval
  rw [ite_eq_left hind] at hval
  rcases i with i | i <;> rcases j with j | j <;> simp_all [vectorIndex, vectorSign]

private theorem weight_vector_ne_exterior (i : PairIndex 4) (I : Finset (Fin 4)) :
    vectorWeight i ≠ exteriorWeight I := by
  intro h
  have hv : doubledWeight (vectorWeight i) 0 % 2 = 0 := by
    rw [doubled_vector]
    split
    · cases i <;> norm_num [vectorSign]
    · decide
  have he : doubledWeight (exteriorWeight I) 0 % 2 = 1 := by
    rw [doubled_exterior]
    split <;> decide
  rw [h, he] at hv
  exact Int.one_ne_zero hv

private theorem weight_vector_ne_zero (i : PairIndex 4) : vectorWeight i ≠ 0 := by
  intro h
  have hv := congrArg (fun x => doubledWeight x (vectorIndex i)) h
  simp only [doubled_vector, ite_true, map_zero, Pi.zero_apply] at hv
  cases i <;> norm_num [vectorSign] at hv

private theorem weight_exterior_ne_zero (I : Finset (Fin 4)) : exteriorWeight I ≠ 0 := by
  intro h
  have hv := congrArg (fun x => doubledWeight x 0) h
  simp only [doubled_exterior, map_zero, Pi.zero_apply] at hv
  split at hv <;> norm_num at hv

private theorem modelWeight_block_ne_zero (i : BlockIndex) : modelWeight (.inr i) ≠ 0 := by
  rcases i with I | i | I
  · exact weight_exterior_ne_zero I.val
  · exact weight_vector_ne_zero i
  · exact weight_exterior_ne_zero I.val

private theorem modelWeight_block_injective : Function.Injective (fun i : BlockIndex =>
    modelWeight (.inr i)) := by
  have incompatible (I : WedgeIndex false) (J : WedgeIndex true) :
      exteriorWeight I.val ≠ exteriorWeight J.val := by
    intro h
    have he := weight_exterior_injective h
    have hI := I.property
    rw [he, J.property] at hI
    exact Nat.one_ne_zero hI
  intro i j h
  rcases i with I | i | I <;> rcases j with J | j | J
  · exact congrArg Sum.inl (Subtype.ext (weight_exterior_injective h))
  · exact (weight_vector_ne_exterior _ _ h.symm).elim
  · exact (incompatible _ _ h).elim
  · exact (weight_vector_ne_exterior _ _ h).elim
  · exact congrArg (Sum.inr ∘ Sum.inl) (weight_vector_injective h)
  · exact (weight_vector_ne_exterior _ _ h).elim
  · exact (incompatible _ _ h.symm).elim
  · exact (weight_vector_ne_exterior _ _ h.symm).elim
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (weight_exterior_injective h))

private def markedTorus : FrameTorus G where
  inclusion := torusInclusion G
  closed := torusInclusion_closed G
  points := diagonalPoints
  natural := diagonalPoints_natural
  characters := torusMonomial
  vectorBasis := vectorBasis
  halfBasis := halfBasis
  vectorNatural := vectorBasis_natural
  halfNatural := halfBasis_natural
  blockAction S t :=
    ⟨spinTriple S (diagonalLift (diagonalPoints S t)), torus_blockAction G S t,
      diagonal_vectorWeight S _, diagonal_halfWeight S _⟩

open private spinUnitPoints spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem markedTorus_stabilizer : (markedTorus G).InOrderedStabilizer := by
  let H := SpinFunctor.spinScheme (integralForm 4) (hyperbolicBasis ℤ 4)
  let e (S : ScalarTest) := SpinFunctor.schemePoints (integralForm 4) (hyperbolicBasis ℤ 4) S
  let ρ := spinUnitPoints (integralForm 4) (hyperbolicBasis ℤ 4)
  have hρ := spinUnitPoints_represents (integralForm 4) (hyperbolicBasis ℤ 4)
  have he {S T : ScalarTest} (f : S ⟶ T) (p : ScalarPoints H S) :
      e T (scalarSpec.map f.op ≫ p) = SpinFunctor.map _ _ f.hom (e S p) :=
    SpinFunctor.schemePoints_naturality _ _ f p
  obtain ⟨j, hj⟩ := integral_point_map H G.group (SpinFunctor.spinScheme_affine _ _)
    (fun S => (spinAlbert G S).comp (e S).toMonoidHom) (by
      intro S T f p
      change spinAlbert G T (e T (scalarSpec.map f.op ≫ p)) = scalarSpec.map f.op ≫ spinAlbert G S (e S p)
      rw [he f p, spinAlbert_natural])
  obtain ⟨i, hi⟩ := integral_point_map diagonalTorus H (by
    change IsAffine (Spec (CommRingCat.of LaurentRing))
    infer_instance)
    (fun S => (e S).symm.toMonoidHom.comp (diagonalLift.comp (diagonalPoints S).toMonoidHom)) (by
      intro S T f t
      apply (e T).injective
      change e T ((e T).symm (diagonalLift (diagonalPoints T (scalarSpec.map f.op ≫ t)))) =
        e T (scalarSpec.map f.op ≫ (e S).symm (diagonalLift (diagonalPoints S t)))
      rw [he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, diagonalPoints_natural,
        diagonalLift_natural])
  have hJ (S : ScalarTest) (p : ScalarPoints H S) :
      p ≫ j.hom.hom = spinAlbert G S (e S p) := hj S p
  have hI (S : ScalarTest) (t : ScalarPoints diagonalTorus S) :
      t ≫ i.hom.hom = (e S).symm (diagonalLift (diagonalPoints S t)) := hi S t
  refine ⟨H, j, i, ρ, liftUnit, ?_, hρ, ?_, liftUnit_isDiagonalCliffordLift, ?_⟩
  · apply Grp.hom_ext
    apply integral_hom_ext (X := diagonalTorus.X) (by
      change IsAffine (Spec (CommRingCat.of LaurentRing))
      infer_instance)
    intro S t
    change t ≫ (i.hom.hom ≫ j.hom.hom) = t ≫ (torusInclusion G).hom.hom
    rw [← Category.assoc, hJ, hI, MulEquiv.apply_symm_apply, torusInclusion_points]
  · intro S
    constructor
    · intro x y hxy
      change x ≫ j.hom.hom = y ≫ j.hom.hom at hxy
      rw [hJ, hJ] at hxy
      exact (e S).injective (spinAlbert_injective G S hxy)
    · ext g
      constructor
      · rintro ⟨p, rfl⟩ a
        change G.action S (p ≫ j.hom.hom) (frameAxis a) = frameAxis a
        rw [hJ, spinAlbert_action]
        exact (spinFrame S (e S p)).property.1 a
      · intro hg
        obtain ⟨s, hs⟩ := spinAlbert_of_fixesFrame G S g hg
        refine ⟨(e S).symm s, ?_⟩
        change (e S).symm s ≫ j.hom.hom = g
        rw [hJ, MulEquiv.apply_symm_apply, hs]
  · intro S t
    rw [hI]
    change ((e S) ((e S).symm (diagonalLift (diagonalPoints S t)))).val =
      (diagonalLift (diagonalPoints S t)).val
    rw [MulEquiv.apply_symm_apply]

section Centralizer

private abbrev LaurentExtension (S : ScalarTest) := MonoidAlgebra S CharacterGroup

private def universalParameters (S : ScalarTest) : LaurentRing →ₐ[ℤ] LaurentExtension S :=
  MonoidAlgebra.lift ℤ (LaurentExtension S) CharacterGroup (MonoidAlgebra.of S CharacterGroup)

private theorem universalParameters_monomial (S : ScalarTest) (x : CharacterExponents) :
    universalParameters S (monomial x) = MonoidAlgebra.single (Multiplicative.ofAdd x) 1 := by
  rw [universalParameters, monomial, MonoidAlgebra.lift_of, MonoidAlgebra.of_apply]

private theorem diagonal_action_coordinate {R : Type*} [CommRing R] {V : Type*}
    [AddCommGroup V] [Module R V] {I : Type*} (b : Basis I R V) (h : V →ₗ[R] V)
    (w : I → R) (hw : ∀ j, h (b j) = w j • b j) (x : V) (i : I) :
    b.repr (h x) i = w i * b.repr x i := by
  classical
  have he : (b.coord i).comp h = w i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, hw, map_smul, Basis.coord_apply, Basis.repr_self,
      LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases h : j = i <;> simp [h]
  exact DFunLike.congr_fun he x

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
private theorem centralizer_coefficients (S : ScalarTest) (g : ScalarPoints G.group S)
    (hg : (markedTorus G).Centralizes g) (i j : ModelIndex) (hij : modelWeight i ≠ modelWeight j) :
    (modelBasis S).repr (G.action S g (modelBasis S j)) i = 0 := by
  classical
  let A := CommAlgCat.of ℤ (LaurentExtension S)
  let f : S ⟶ A := CommAlgCat.ofHom ((IsScalarTower.toAlgHom ℤ S A))
  let t : ScalarPoints diagonalTorus A := scalarSpec.map (CommAlgCat.ofHom (universalParameters S)).op
  let gA : ScalarPoints G.group A := scalarSpec.map f.op ≫ g
  let tA : ScalarPoints G.group A := t ≫ (torusInclusion G).hom.hom
  let m (k : ModelIndex) : A := MonoidAlgebra.single (Multiplicative.ofAdd (modelWeight k)) 1
  have ht (k : ModelIndex) : G.action A tA (modelBasis A k) = m k • modelBasis A k := by
    have h := torus_action_basis G A t k
    rw [torusMonomial A (universalParameters S), universalParameters_monomial] at h
    exact h
  have hgA : gA * tA = tA * gA := hg A f t
  have hcomm := congrArg (fun p : ScalarPoints G.group A => G.action A p (modelBasis A j)) hgA
  simp only [map_mul, LinearEquiv.mul_apply, ht, map_smul] at hcomm
  have hcoord := congrArg (fun v : Model A => (modelBasis A).repr v i) hcomm
  let c := (modelBasis S).repr (G.action S g (modelBasis S j)) i
  have hnat := G.natural f g (modelBasis S j)
  rw [modelBasis_natural] at hnat
  have hcoeff := modelBasis_repr_natural f (G.action S g (modelBasis S j)) i
  rw [hnat] at hcoeff
  have hdiag : (modelBasis A).repr (G.action A tA (G.action A gA (modelBasis A j))) i =
      m i * (modelBasis A).repr (G.action A gA (modelBasis A j)) i :=
    diagonal_action_coordinate (modelBasis A) (G.action A tA).toLinearMap m ht _ _
  change (modelBasis A).repr (G.action A gA (modelBasis A j)) i = f.hom c at hcoeff
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hdiag, hcoeff] at hcoord
  change m j * MonoidAlgebra.single (1 : CharacterGroup) c =
    m i * MonoidAlgebra.single (1 : CharacterGroup) c at hcoord
  have hmul (l : ModelIndex) : m l * MonoidAlgebra.single 1 c =
      (MonoidAlgebra.single (Multiplicative.ofAdd (modelWeight l)) c : LaurentExtension S) := by
    simpa only [mul_one, one_mul] using
      (MonoidAlgebra.single_mul_single (Multiplicative.ofAdd (modelWeight l)) 1 (1 : S) c)
  have heq := (hmul j).symm.trans (hcoord.trans (hmul i))
  have hc := congrArg (fun a : LaurentExtension S => a.coeff (Multiplicative.ofAdd (modelWeight j))) heq
  have hne : Multiplicative.ofAdd (modelWeight i) ≠ Multiplicative.ofAdd (modelWeight j) :=
    fun h => hij (Multiplicative.ofAdd.injective h)
  change (Finsupp.single (Multiplicative.ofAdd (modelWeight j)) c) (Multiplicative.ofAdd (modelWeight j)) =
    (Finsupp.single (Multiplicative.ofAdd (modelWeight i)) c) (Multiplicative.ofAdd (modelWeight j)) at hc
  simpa only [Finsupp.single_apply, ite_eq_left rfl, ite_true, ite_eq_right hne] using hc

private theorem centralizer_weight_line (S : ScalarTest) (g : ScalarPoints G.group S)
    (hg : (markedTorus G).Centralizes g) (j : BlockIndex) :
    G.action S g (modelBasis S (.inr j)) =
      (modelBasis S).repr (G.action S g (modelBasis S (.inr j))) (.inr j) • modelBasis S (.inr j) := by
  classical
  apply (modelBasis S).repr.injective
  ext i
  rw [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases h : Sum.inr j = i
  · subst i
    simp
  · rw [ite_eq_right h, smul_eq_mul, mul_zero]
    apply centralizer_coefficients G S g hg
    cases i with
    | inl i => exact (modelWeight_block_ne_zero j).symm
    | inr i =>
      exact fun he => h (congrArg Sum.inr (modelWeight_block_injective he).symm)

private def blockEmbedding (S : ScalarTest) (i : Fin 3) : Zorn S →ₗ[S] Model S :=
  (LinearMap.inr S _ _).comp (LinearMap.single S (fun _ : Fin 3 => Zorn S) i)

private theorem centralizer_preserves_block (S : ScalarTest) (g : ScalarPoints G.group S)
    (hg : (markedTorus G).Centralizes g) (i : Fin 3) (x : Zorn S) :
    ∃ y : Zorn S, G.action S g (singleBlockCoordinates i x) = singleBlockCoordinates i y := by
  have hB {J : Type} [Fintype J] (b : Basis J S (Zorn S)) (j : J → BlockIndex)
      (hj : ∀ n, modelBasis S (.inr (j n)) = blockEmbedding S i (b n)) :
      G.action S g (blockEmbedding S i x) ∈ LinearMap.range (blockEmbedding S i) := by
    rw [← b.sum_repr x, map_sum, map_sum]
    apply Submodule.sum_mem
    intro n _
    simp only [map_smul]
    apply Submodule.smul_mem
    rw [← hj, centralizer_weight_line G S g hg, hj]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  have hmem : G.action S g (blockEmbedding S i x) ∈ LinearMap.range (blockEmbedding S i) := by
    fin_cases i
    · apply hB (halfBasis S false) (fun j => .inl j)
      intro j
      exact modelBasis_block S (.inl j)
    · apply hB (vectorBasis S) (fun j => .inr (.inl j))
      intro j
      exact modelBasis_block S (.inr (.inl j))
    · apply hB (halfBasis S true) (fun j => .inr (.inr j))
      intro j
      exact modelBasis_block S (.inr (.inr j))
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy.symm⟩

open CubicSpecification (cubicAdjoint diagonalCoordinates blockWeight)
open private splitAuto_preserves from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IdempotentCharts

private theorem centralizer_fixesFrame (S : ScalarTest) (g : ScalarPoints G.group S)
    (hg : (markedTorus G).Centralizes g) (i : Fin 3) :
    G.action S g (frameAxis i) = frameAxis i := by
  let weights : Fin 3 → Sˣ := fun _ => 1
  let a := G.action S g
  have ha : a ∈ {g | IsSplitAutomorphism g} := by
    rw [← G.image S]
    exact Set.mem_range_self g
  have hAuto := splitAuto_preserves a ha
  obtain ⟨y, hy⟩ := centralizer_preserves_block G S g hg i 1
  have adjBlock (z : Zorn S) :
      CubicSpecification.cubicAdjoint (norm S) weights (CubicSpecification.singleBlockCoordinates i z) =
        -(norm S z) • frameAxis i := by
    have hh := (cubic_single_block_formulas (n := norm S) weights i z).2.1
    have hweight : CubicSpecification.blockWeight weights i = 1 := by
      simp [CubicSpecification.blockWeight, weights]
    rw [hh, hweight, one_mul]
    apply Prod.ext
    · funext j
      change Pi.single (M := fun _ : Fin 3 => S) i (-norm S z) j =
        (-norm S z) * Pi.single (M := fun _ : Fin 3 => S) i (1 : S) j
      by_cases hj : j = i <;> simp [hj]
    · exact (smul_zero _).symm
  have hh := hAuto.2 (singleBlockCoordinates i (1 : Zorn S))
  change CubicSpecification.cubicAdjoint (norm S) weights (a (CubicSpecification.singleBlockCoordinates i 1)) =
    a (CubicSpecification.cubicAdjoint (norm S) weights (CubicSpecification.singleBlockCoordinates i 1)) at hh
  rw [hy, adjBlock, adjBlock, Zorn.norm_one, map_smul, neg_one_smul] at hh
  have haxis : a (frameAxis i) = norm S y • frameAxis i := by
    apply neg_injective
    rw [← neg_smul]
    exact hh.symm
  have ht := hAuto.1 (frameAxis i)
  change CubicSpecification.linearTrace (norm S) weights (a (frameAxis i)) =
    CubicSpecification.linearTrace (norm S) weights (frameAxis i) at ht
  have ht₀ : CubicSpecification.linearTrace (norm S) weights (frameAxis i) = 1 := by
    rw [linearTrace_apply]
    change ∑ j, Pi.single i (1 : S) j = 1
    simp [Pi.single_apply]
  rw [haxis, map_smul, ht₀, smul_eq_mul, mul_one] at ht
  change a (frameAxis i) = frameAxis i
  rw [haxis, ht, one_smul]

open private diagonalLift_exists_of_matrix from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights

private theorem centralizer_lies_in_torus (S : ScalarTest) (g : ScalarPoints G.group S)
    (hg : (markedTorus G).Centralizes g) :
    ∃ t : ScalarPoints diagonalTorus S, t ≫ (torusInclusion G).hom.hom = g := by
  obtain ⟨s, rfl⟩ := spinAlbert_of_fixesFrame G S g (centralizer_fixesFrame G S g hg)
  have hmat := spinVector_matrix S s
  have hd (i j : PairIndex 4) (hij : i ≠ j) :
      (LinearMap.toMatrix (vectorBasis S) (vectorBasis S) ((spinTriple S s).val 1).toLinearMap) i j = 0 := by
    let k : BlockIndex := .inr (.inl j)
    let c := (modelBasis S).repr (G.action S (spinAlbert G S s) (modelBasis S (.inr k))) (.inr k)
    have hl : G.action S (spinAlbert G S s) (modelBasis S (.inr k)) = c • modelBasis S (.inr k) :=
      centralizer_weight_line G S (spinAlbert G S s) hg k
    rw [spinAlbert_action, spinFrame_action, modelBasis_block] at hl
    have he : (spinTriple S s).val 1 (vectorBasis S j) = c • vectorBasis S j := by
      have hh := congrArg (fun z : Model S => z.2 1) hl
      change (spinTriple S s).val 1
          (Pi.single (M := fun _ : Fin 3 => Zorn S) 1 (vectorBasis S j) 1) =
        c • Pi.single (M := fun _ : Fin 3 => Zorn S) 1 (vectorBasis S j) 1 at hh
      simpa only [Pi.single_eq_same] using hh
    rw [LinearMap.toMatrix_apply]
    change (vectorBasis S).repr ((spinTriple S s).val 1 (vectorBasis S j)) i = 0
    classical
    rw [he, map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      ite_eq_right hij.symm, smul_zero]
  obtain ⟨d, hd⟩ := diagonalLift_exists_of_matrix s hmat hd
  refine ⟨(diagonalPoints S).symm d, ?_⟩
  rw [torusInclusion_points, MulEquiv.apply_symm_apply, hd]

private theorem torus_point_centralizes (T : FrameTorus G) {S : ScalarTest}
    (t : ScalarPoints diagonalTorus S) : T.Centralizes (t ≫ T.inclusion.hom.hom) := by
  intro A f s
  let tA : ScalarPoints diagonalTorus A := scalarSpec.map f.op ≫ t
  have hcomm : tA * s = s * tA := by
    apply (T.points A).injective
    rw [map_mul, map_mul, mul_comm]
  have hc := congrArg (fun p : ScalarPoints diagonalTorus A => p ≫ T.inclusion.hom.hom) hcomm
  simpa only [MonObj.mul_comp, Category.assoc, tA] using hc

end Centralizer

end ModelWeights

section GeometricFibres

open _root_.LinearAlgebraicGroups (TestAlgebra Points testSpec mapPoints
  restrictTestAlgebra baseChangePointsSchemeNaturality baseChangePointsNaturality
  groupBaseChange groupPointsFunctor baseChangePointGroupEquiv)
open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open LinearAlgebraicGroups.Specs.GeometricRadicals (baseChangedSubgroup)
open LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)

private abbrev integerBaseMap (K : Type) [Field K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ K))

private abbrev integralBaseChange (K : Type) [Field K] :=
  Over.pullback (integerBaseMap K)

private abbrev integralFibreGroup (K : Type) [Field K] (H : IntegralGroup) :
    LinearAlgebraicGroups.Specs.GroupScheme K :=
  ((integralBaseChange K).mapGrp).obj H

private abbrev overIntegers {K : Type} [Field K] (R : TestAlgebra K) : ScalarTest :=
  CommAlgCat.of ℤ R

private abbrev overIntegersMap {K : Type} [Field K] {R S : TestAlgebra K} (f : R ⟶ S) :
    overIntegers R ⟶ overIntegers S :=
  CommAlgCat.ofHom (f.hom.restrictScalars ℤ)

private theorem scalarSpec_structure {K : Type} [Field K] (R : TestAlgebra K) :
    (scalarSpec.obj (op (overIntegers R))).hom = ((testSpec K).obj (op R)).hom ≫ integerBaseMap K := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) =
    Spec.map (CommRingCat.ofHom (algebraMap K R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ K))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq ℤ K R)

set_option backward.isDefEq.respectTransparency false in
private def projectIntegralPoint {K : Type} [Field K] (X : Over (Spec (CommRingCat.of ℤ)))
    (R : TestAlgebra K) (p : Points ((integralBaseChange K).obj X) R) :
    scalarSpec.obj (op (overIntegers R)) ⟶ X :=
  Over.homMk (p.left ≫ pullback.fst X.hom (integerBaseMap K)) (by
    change (p.left ≫ pullback.fst X.hom (integerBaseMap K)) ≫ X.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p.left ≫ ((integralBaseChange K).obj X).hom) ≫ integerBaseMap K = _
    rw [Over.w p, scalarSpec_structure])

private theorem projectIntegralPoint_bijective {K : Type} [Field K]
    (X : Over (Spec (CommRingCat.of ℤ))) (R : TestAlgebra K) :
    Function.Bijective (projectIntegralPoint X R) := by
  constructor
  · intro p q h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg Over.Hom.left h
    · exact (Over.w p).trans (Over.w q).symm
  · intro p
    let Y := (testSpec K).obj (op R)
    have hp : p.left ≫ X.hom = Y.hom ≫ integerBaseMap K :=
      (Over.w p).trans (scalarSpec_structure R)
    refine ⟨Over.homMk (pullback.lift p.left Y.hom hp) (pullback.lift_snd ..), ?_⟩
    apply Over.OverMorphism.ext
    exact pullback.lift_fst ..

private theorem projectIntegralPoint_comp {K : Type} [Field K]
    {X Y : Over (Spec (CommRingCat.of ℤ))} (f : X ⟶ Y)
    (R : TestAlgebra K) (p : Points ((integralBaseChange K).obj X) R) :
    projectIntegralPoint Y R (p ≫ (integralBaseChange K).map f) = projectIntegralPoint X R p ≫ f := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((integralBaseChange K).map f).left) ≫ pullback.fst Y.hom (integerBaseMap K) =
    (p.left ≫ pullback.fst X.hom (integerBaseMap K)) ≫ f.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

private theorem projectIntegralPoint_natural {K : Type} [Field K] (X : Over (Spec (CommRingCat.of ℤ)))
    {R S : TestAlgebra K} (f : R ⟶ S) (p : Points ((integralBaseChange K).obj X) R) :
    projectIntegralPoint X S (mapPoints f p) =
      scalarSpec.map (overIntegersMap f).op ≫ projectIntegralPoint X R p := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem projectIntegralPoint_mul {K : Type} [Field K] (H : IntegralGroup)
    (R : TestAlgebra K) (p q : Points (integralFibreGroup K H).X R) :
    projectIntegralPoint H.X R (p * q) =
      (projectIntegralPoint H.X R p : ScalarPoints H (overIntegers R)) *
      projectIntegralPoint H.X R q := by
  let F := integralBaseChange K
  let m := Functor.LaxMonoidal.μ F H.X H.X
  let p' : Points (F.obj H.X) R := p
  let q' : Points (F.obj H.X) R := q
  let a : Points (F.obj (H.X ⊗ H.X)) R := lift p' q' ≫ m
  let x := projectIntegralPoint H.X R p
  let y := projectIntegralPoint H.X R q
  have ha : projectIntegralPoint (H.X ⊗ H.X) R a = lift x y := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← projectIntegralPoint_comp, lift_fst]
      change projectIntegralPoint H.X R ((lift p' q' ≫ m) ≫ F.map (fst H.X H.X)) = x
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst p' q']
    · rw [← projectIntegralPoint_comp, lift_snd]
      change projectIntegralPoint H.X R ((lift p' q' ≫ m) ≫ F.map (snd H.X H.X)) = y
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd p' q']
  change projectIntegralPoint H.X R (lift p' q' ≫ (m ≫ F.map μ[H.X])) = lift x y ≫ μ[H.X]
  rw [← Category.assoc]
  change projectIntegralPoint H.X R (a ≫ F.map μ[H.X]) = _
  rw [projectIntegralPoint_comp, ha]

private def integralFibrePoints {K : Type} [Field K] (H : IntegralGroup) (R : TestAlgebra K) :
    Points (integralFibreGroup K H).X R ≃* ScalarPoints H (overIntegers R) where
  toEquiv := Equiv.ofBijective _ (projectIntegralPoint_bijective H.X R)
  map_mul' := projectIntegralPoint_mul H R

variable (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]

private abbrev geometricBaseGroup (H : IntegralGroup) :=
  (groupBaseChange k K).obj (integralFibreGroup k H)

private def geometricPoints (H : IntegralGroup) (R : TestAlgebra K) :
    Points (geometricBaseGroup k K H).X R ≃* ScalarPoints H (overIntegers R) :=
  (baseChangePointGroupEquiv K (integralFibreGroup k H) R).trans
    (integralFibrePoints H ((restrictTestAlgebra k K).obj R))

set_option backward.isDefEq.respectTransparency false in
private theorem geometricPoints_comp {D H : IntegralGroup} (f : D ⟶ H)
    (R : TestAlgebra K) (p : Points (geometricBaseGroup k K D).X R) :
    geometricPoints k K H R
      (p ≫ ((groupBaseChange k K).map (((integralBaseChange k).mapGrp).map f)).hom.hom) =
      geometricPoints k K D R p ≫ f.hom.hom := by
  let i : (integralFibreGroup k D).X ⟶ (integralFibreGroup k H).X :=
    (integralBaseChange k).map f.hom.hom
  let Q := (restrictTestAlgebra k K).obj R
  let p' : Points ((LinearAlgebraicGroups.baseChange k K).obj (integralFibreGroup k D).X) R := p
  change projectIntegralPoint H.X Q
    (LinearAlgebraicGroups.baseChangePoint k K (integralFibreGroup k H).X R
      (p' ≫ (LinearAlgebraicGroups.baseChange k K).map i)) = _
  rw [baseChangePointsSchemeNaturality k K i R p']
  rw [projectIntegralPoint_comp f.hom.hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem geometricPoints_natural (H : IntegralGroup) {R S : TestAlgebra K} (f : R ⟶ S)
    (p : Points (geometricBaseGroup k K H).X R) :
    geometricPoints k K H S (mapPoints f p) =
      scalarSpec.map (overIntegersMap f).op ≫ geometricPoints k K H R p := by
  let Q := (restrictTestAlgebra k K).obj S
  let p' : Points ((LinearAlgebraicGroups.baseChange k K).obj (integralFibreGroup k H).X) R := p
  change projectIntegralPoint H.X Q
    (LinearAlgebraicGroups.baseChangePoint k K (integralFibreGroup k H).X S (mapPoints f p')) = _
  rw [baseChangePointsNaturality k K (integralFibreGroup k H).X f p', projectIntegralPoint_natural]
  rfl

open private splitDiagonalGroup diagonalGroupPoints diagonalGroupPoints_natural
  diagonalGroup_affine splitDiagonalGroup_isTorus torusComm subgroupOf_of_testPoints
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights
open private groupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer

private def torusOfDiagonalPoints (D : LinearAlgebraicGroups.Specs.GroupScheme K) (hD : IsAffine D.X.left)
    (d : ∀ R : TestAlgebra K, Points D.X R ≃* DiagonalPoints R)
    (hn : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (p : Points D.X R),
      d S (mapPoints f p) = mapDiagonal f.hom.toRingHom (d R p)) :
    D ≅ splitDiagonalGroup K := by
  let : IsAffine D.X.left := hD
  let : IsAffine (splitDiagonalGroup K).X.left := diagonalGroup_affine K
  let e (R : TestAlgebra K) := (d R).trans (diagonalGroupPoints K R).symm
  refine groupIsoOfPoints _ _ (NatIso.ofComponents (fun R => (e R).toGrpIso) ?_)
  intro R S f
  apply GrpCat.ext
  intro p
  change Points D.X R at p
  change e S (mapPoints f p) = mapPoints f (e R p)
  apply (diagonalGroupPoints K S).injective
  change diagonalGroupPoints K S ((diagonalGroupPoints K S).symm (d S (mapPoints f p))) = _
  rw [MulEquiv.apply_symm_apply, diagonalGroupPoints_natural, hn f p]
  change _ = mapDiagonal f.hom.toRingHom (diagonalGroupPoints K R ((diagonalGroupPoints K R).symm (d R p)))
  rw [MulEquiv.apply_symm_apply]

private def geometricTorusIso :
    geometricBaseGroup k K diagonalTorus ≅ splitDiagonalGroup K :=
  torusOfDiagonalPoints K _ (by
    change IsAffine (pullback (integralFibreGroup k diagonalTorus).X.hom
      (LinearAlgebraicGroups.fieldSpecMap k K))
    have : IsAffine (integralFibreGroup k diagonalTorus).X.left := by
      have : IsAffine diagonalTorus.X.left := by
        change IsAffine (Spec (CommRingCat.of LaurentRing))
        infer_instance
      change IsAffine (pullback diagonalTorus.X.hom (integerBaseMap k))
      infer_instance
    infer_instance)
    (fun R => (geometricPoints k K diagonalTorus R).trans (diagonalPoints (overIntegers R))) (by
      intro R S f p
      change diagonalPoints (overIntegers S) (geometricPoints k K diagonalTorus S (mapPoints f p)) = _
      rw [geometricPoints_natural, diagonalPoints_natural]
      rfl)

variable {P : IntegralPresentation} (G : SplitGroup P)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
private theorem markedTorus_geometricallyMaximal : IsGeometricallyMaximal ((markedTorus G).fibre k) := by
  let K := AlgebraicClosure k
  let T := (markedTorus G).fibre k
  let hcl : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left :=
    LinearAlgebraicGroups.baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion
  let Tbar := baseChangedSubgroup K T hcl
  refine ⟨hcl, ?_⟩
  change LinearAlgebraicGroups.Specs.GeometricRadicals.IsMaximalTorus Tbar
  constructor
  · let e := geometricTorusIso k K
    obtain ⟨E, _, _, _, r, ⟨f⟩⟩ := splitDiagonalGroup_isTorus K
    exact ⟨E, inferInstance, inferInstance, inferInstance, r,
      ⟨(groupBaseChange K E).mapIso e ≪≫ f⟩⟩
  intro D hD hTD
  have hAffG : IsAffine (geometricBaseGroup k K G.group).X.left := by
    have : IsAffine (integralFibreGroup k G.group).X.left := (algebraicFiber G k).property.1
    change IsAffine (pullback (integralFibreGroup k G.group).X.hom (LinearAlgebraicGroups.fieldSpecMap k K))
    infer_instance
  have : IsAffine D.group.X.left := by
    have := D.isClosedImmersion
    exact isAffine_of_isAffineHom D.inclusion.hom.hom.left
  have hcomm : IsCommMonObj D.group.X := torusComm D.group inferInstance hD
  obtain ⟨i, hi⟩ := hTD
  have hincl : i.hom.hom ≫ D.inclusion.hom.hom = Tbar.inclusion.hom.hom :=
    congrArg (fun q : Tbar.group ⟶ geometricBaseGroup k K G.group => q.hom.hom) hi
  apply subgroupOf_of_testPoints (K := K) (hS := inferInstance)
  intro R p
  let E := geometricPoints k K G.group R
  let F := geometricPoints k K diagonalTorus R
  let g := E (p ≫ D.inclusion.hom.hom)
  have hg : (markedTorus G).Centralizes g := by
    intro A f t
    rcases A with @⟨A, hR, hZ⟩
    let : CommRing A := hR
    have hz : hZ = Ring.toIntAlgebra (R := A) := Subsingleton.elim _ _
    subst hZ
    let : Algebra K A := (f.hom.toRingHom.comp (algebraMap K R)).toAlgebra
    let Q := CommAlgCat.of K A
    let a : R ⟶ Q := CommAlgCat.ofHom
      { toRingHom := f.hom.toRingHom
        commutes' := fun _ => rfl }
    have ha : overIntegersMap a = f := by ext; rfl
    let s := (geometricPoints k K diagonalTorus Q).symm t
    let pQ := mapPoints a p
    have hQt : (pQ ≫ D.inclusion.hom.hom) * (s ≫ Tbar.inclusion.hom.hom) =
        (s ≫ Tbar.inclusion.hom.hom) * (pQ ≫ D.inclusion.hom.hom) := by
      rw [← hincl, ← Category.assoc, ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
    have h := congrArg (geometricPoints k K G.group Q) hQt
    rw [map_mul, map_mul] at h
    have ht : geometricPoints k K G.group Q (s ≫ Tbar.inclusion.hom.hom) =
        t ≫ (torusInclusion G).hom.hom := by
      have h := geometricPoints_comp k K (torusInclusion G) Q s
      change geometricPoints k K G.group Q (s ≫ Tbar.inclusion.hom.hom) =
        geometricPoints k K diagonalTorus Q s ≫ (torusInclusion G).hom.hom at h
      rw [h]
      exact congrArg (· ≫ (torusInclusion G).hom.hom)
        ((geometricPoints k K diagonalTorus Q).apply_symm_apply t)
    have hp : geometricPoints k K G.group Q (pQ ≫ D.inclusion.hom.hom) = scalarSpec.map f.op ≫ g := by
      change geometricPoints k K G.group Q (mapPoints a (p ≫ D.inclusion.hom.hom)) = _
      rw [geometricPoints_natural, ha]
    rw [hp, ht] at h
    exact h
  obtain ⟨t, ht⟩ := centralizer_lies_in_torus G (overIntegers R) g hg
  refine ⟨F.symm t, E.injective ?_⟩
  have h := geometricPoints_comp k K (torusInclusion G) R (F.symm t)
  change E (F.symm t ≫ Tbar.inclusion.hom.hom) = F (F.symm t) ≫ (torusInclusion G).hom.hom at h
  rw [h, MulEquiv.apply_symm_apply]
  exact ht

end GeometricFibres

/-- The integral frame torus with its normalized characters and Peirce bases. -/
theorem splitFrameTorus : Statement :=
  fun _ G => ⟨markedTorus G, markedTorus_stabilizer G, centralizer_fixesFrame G,
    fun S g => ⟨centralizer_lies_in_torus G S g, by
      rintro ⟨t, rfl⟩
      exact torus_point_centralizes G (markedTorus G) t⟩,
    fun k _ => markedTorus_geometricallyMaximal k G⟩

end OrderedFrame

end

end LinearAlgebraicGroups.Albert.SplitFrameTorus
