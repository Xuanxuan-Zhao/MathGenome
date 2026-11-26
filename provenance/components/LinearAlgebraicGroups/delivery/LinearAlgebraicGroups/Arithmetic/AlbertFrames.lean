import Specs.LinearAlgebraicGroups.Arithmetic.AlbertFrames
import LinearAlgebraicGroups.Albert.AutomorphismType
import LinearAlgebraicGroups.Albert.IntrinsicCubic
import LinearAlgebraicGroups.Albert.IdempotentCharts
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basis

namespace LinearAlgebraicGroups.Arithmetic.AlbertFrames

open LinearAlgebraicGroups.Albert hiding ParaQuadratic
open LinearAlgebraicGroups.Composition (Zorn)
open AlbertFramesSpecification SplitSpecification IntrinsicCubicSpecification
open AutomorphismTypeSpecification
open QuadraticOperatorSpecification (applyOperator)
open TensorProduct Algebra.TensorProduct
open scoped TensorProduct

universe u v

noncomputable section

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
variable {J : ParaQuadratic k M} {F : Coefficients k M}

open private pointMap pointMap_smul extendChart cover_point_injective adjoint_natural
  pairing_natural chart_adjoint chart_pairing chart_norm from
  LinearAlgebraicGroups.Albert.IntrinsicCubic

private abbrev modelNorm (B : Type u) [CommRing B] := SplitRank.norm B .octonion

/-- An injective comparison with the split model, retaining the scalar map. -/
private theorem withSplitChart (hJ : IsAlbert J) {P : Prop}
    (work : ∀ (B : Type u) [CommRing B] [Algebra k B] (f : k →ₐ[k] B),
      Function.Injective f → Function.Injective (pointMap (M := M) f) →
      SplitChart J B → P) : P := by
  obtain ⟨S, _, _, hflat, e, he, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  let := hflat
  exact work (k ⊗[k] S) (includeLeft : k →ₐ[k] k ⊗[k] S)
    (FaithfulSMul.algebraMap_injective _ _) cover_point_injective
    (extendChart (⟨e, he, hop⟩ : SplitChart J S) (includeRight : S →ₐ[k] k ⊗[k] S))

private theorem sharp_sharp (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (x : Ground k M) : sharp J F (sharp J F x) = norm F x • x := by
  apply withSplitChart hJ
  intro B _ _ f _ hf c
  let m := pointMap (M := M) f
  let n := modelNorm B
  let γ := LowerRankSpecification.untwisted B
  have hA (z : Ground k M) : c.coordinates (m (sharp J F z)) =
      CubicSpecification.cubicAdjoint n γ (c.coordinates (m z)) := by
    dsimp only [m, sharp]
    rw [adjoint_natural, chart_adjoint hF]
  have hN : f (norm F x) = CubicSpecification.cubicNorm n γ (c.coordinates (m x)) :=
    (F.norm.natural f x).symm.trans (chart_norm hF c _)
  apply hf
  apply c.coordinates.injective
  change c.coordinates (m (sharp J F (sharp J F x))) = c.coordinates (m (norm F x • x))
  rw [hA, hA, pointMap_smul, map_smul, hN]
  exact cubic_adjoint_identity γ (Zorn.isOctonion B) _

theorem zeroAdjointFromNorm : ZeroAdjointFromNorm.{u,v} := by
  intro k _ M _ _ J F hJ hF
  rintro ⟨x, hx, hNx⟩
  by_cases h : sharp J F x = 0
  · exact ⟨x, hx, h⟩
  · exact ⟨sharp J F x, h, by rw [sharp_sharp hJ hF, hNx, zero_smul]⟩


private theorem sharp_quadratic (hJ : IsAlbert J) (hF : IsCharacteristic J F) :
    ∃ A : QuadraticMap k (Ground k M) (Ground k M), ∀ x, A x = sharp J F x := by
  apply withSplitChart hJ
  intro B _ _ f _ hf c
  let m := pointMap (M := M) f
  let E (x : Ground k M) := c.coordinates (m x)
  have hE : Function.Injective E := c.coordinates.injective.comp hf
  obtain ⟨A, hA, _⟩ := cubicAdjoint_isQuadratic (n := modelNorm B) (LowerRankSpecification.untwisted B)
  have h (x : Ground k M) : E (sharp J F x) = A (E x) := by
    change c.coordinates (pointMap f (adjoint J F k x)) = _
    rw [adjoint_natural, chart_adjoint hF, hA]
  have hAdd (x y : Ground k M) : E (x + y) = E x + E y := by
    simp [E, map_add]
  have hSub (x y : Ground k M) : E (x - y) = E x - E y := by
    simp [E, map_sub]
  have hp (x y : Ground k M) :
      E (QuadraticMap.polar (sharp J F) x y) = QuadraticMap.polar A (E x) (E y) := by
    simp only [QuadraticMap.polar, hAdd, hSub, h]
  have hs (a : k) (x : Ground k M) : E (a • x) = f a • E x := by
    change c.coordinates (pointMap f (a • x)) = _
    rw [pointMap_smul, map_smul]
  refine ⟨QuadraticMap.ofPolar (sharp J F) ?_ ?_ ?_, fun _ => rfl⟩
  · intro a x
    apply hE
    simp only [h, hs, QuadraticMap.map_smul, map_mul]
  · intro x y z
    apply hE
    simp only [hp, hAdd, QuadraticMap.polar_add_left]
  · intro a x y
    apply hE
    simp only [hp, hs, QuadraticMap.polar_smul_left]

private theorem operatorSymmetryCovariance (hJ : IsAlbert J) (hF : IsCharacteristic J F) :
    (∀ x y z : Ground k M, pairing F k (U J x y) z = pairing F k y (U J x z)) ∧
    (∀ x y : Ground k M, sharp J F (U J x y) = U J (sharp J F x) (sharp J F y)) ∧
    (∀ y : Ground k M, QuadraticMap.polar (sharp J F) (unit J) y = trace F y • unit J - y) ∧
    trace F (unit J) = 3 := by
  apply withSplitChart hJ
  intro B _ _ f hi hf c
  let m := pointMap (M := M) f
  let n := modelNorm B
  let γ := LowerRankSpecification.untwisted B
  let u₀ : SplitRank.octonion.Model B := CubicSpecification.cubicUnit
  have hu : c.coordinates (m (unit J)) = u₀ := by
    change c.coordinates (pointMap f (1 ⊗ₜ[k] J.unit)) = _
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using c.unit
  have hA (z : Ground k M) : c.coordinates (m (sharp J F z)) =
      CubicSpecification.cubicAdjoint n γ (c.coordinates (m z)) := by
    dsimp only [m, sharp]
    rw [adjoint_natural, chart_adjoint hF]
  have hT (x y : Ground k M) : f (pairing F k x y) =
      CubicSpecification.tracePairing n γ (c.coordinates (m x)) (c.coordinates (m y)) :=
    (pairing_natural F f x y).trans (chart_pairing hF c _ _)
  have ht (x : Ground k M) : f (trace F x) =
      CubicSpecification.linearTrace n γ (c.coordinates (m x)) :=
    (F.trace.natural f x).symm.trans
      ((intrinsic_coefficients J hJ).2 F hF B c (m x)).1
  have hU (x y : Ground k M) : c.coordinates (m (U J x y)) =
      applyOperator n γ (c.coordinates (m x)) (c.coordinates (m y)) := by
    dsimp only [m, U]
    rw [J.natural, c.op]
  have hOp := cubic_operator_identities γ (Zorn.isOctonion B)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    apply hi
    rw [hT, hT, hU, hU]
    exact hOp.2.2.1 _ _ _
  · intro x y
    apply hf
    apply c.coordinates.injective
    change c.coordinates (m (sharp J F (U J x y))) = c.coordinates (m (U J (sharp J F x) (sharp J F y)))
    rw [hA, hU, hU, hA, hA]
    exact hOp.2.2.2.1 _ _
  · intro y
    apply hf
    apply c.coordinates.injective
    change c.coordinates (m (QuadraticMap.polar (sharp J F) (unit J) y)) =
      c.coordinates (m (trace F y • unit J - y))
    have hsm : m (trace F y • unit J) = f (trace F y) • m (unit J) := pointMap_smul f _ _
    simp only [QuadraticMap.polar, map_add, map_sub, hA, hsm, map_smul, ht, hu]
    exact (cubic_unit_identities (n := n) γ).2.2 _
  · apply hi
    rw [ht, hu, map_ofNat, linearTrace_apply]
    simp [u₀, CubicSpecification.cubicUnit]

section Corner

variable (hJ : IsAlbert J) (hF : IsCharacteristic J F)

include hJ hF in
private theorem cornerIdentities (e : Ground k M) (he : IsRankOne J F e) :
    let c := unit J - e
    (∀ z, U J c (U J c z) = U J c z) ∧
    ∃ hc : U J c c = c, trace F c = 2 ∧
    ∃ q : QuadraticForm k (PeirceZero J e),
      (∀ z : PeirceZero J e, (∀ w : PeirceZero J e, QuadraticMap.polar q z w = 0) → z = 0) ∧
      (∀ z, q z = cornerNorm J F e z) ∧
      q ⟨c, ⟨c, hc⟩⟩ = 1 ∧
      (∀ z : PeirceZero J e, sharp J F z.val = q z • e ∧
        U J z.val (unit J) = trace F z.val • z.val - q z • c) ∧
      (∀ z w : PeirceZero J e,
        QuadraticMap.polar q z w = trace F z.val * trace F w.val - pairing F k z.val w.val) ∧
      ∀ z : PeirceZero J e, pairing F k c z.val = trace F z.val ∧
        QuadraticMap.polar q ⟨c, ⟨c, hc⟩⟩ z = trace F z.val := by
  obtain ⟨A, hA⟩ := sharp_quadratic hJ hF
  obtain ⟨hSelf, hCov, hCross, hThree⟩ := operatorSymmetryCovariance hJ hF
  obtain ⟨⟨T, hTperf, hT⟩, _, hOne, hTrace, hQuadTrace, _, hOp⟩ :=
    intrinsic_cubic_recovery J F hJ hF k
  let t : Ground k M →ₗ[k] k := T.flip (unit J)
  have ht (x : Ground k M) : trace F x = t x := (hTrace x).trans (hT _ _).symm
  have hAsq (x : Ground k M) :
      U J x (unit J) = A x + t x • x - t (A x) • unit J := by
    have hs : F.quadraticTrace.eval k x = t (A x) := by
      rw [hQuadTrace, hA, ← ht]
    rw [← hs, hA, ← ht]
    change _ = (U J x (unit J) - trace F x • x + F.quadraticTrace.eval k x • unit J) + _ - _
    abel
  let c := unit J - e
  have hte : t e = 1 := (ht e).symm.trans he.1
  have hae : A e = 0 := (hA e).trans he.2
  have hac : A c = e := by
    have hp : QuadraticMap.polar A (unit J) e = unit J - e := by
      simpa only [QuadraticMap.polar, hA, he.1, one_smul] using hCross e
    have hm : A (-e) = A e := by simp [QuadraticMap.map_neg]
    calc
      A c = A (unit J) + A (-e) + QuadraticMap.polar A (unit J) (-e) :=
        (by simpa only [c, sub_eq_add_neg] using QuadraticMap.map_add A (unit J) (-e))
      _ = e := by rw [hm, QuadraticMap.polar_neg_right, hp, hae, hA, show sharp J F (unit J) = unit J from hOne]; abel
  have htc : t c = 2 := by rw [map_sub, ← ht, hThree, hte]; ring
  have hc : U J c (unit J) = c := by rw [hAsq, hac, hte, htc]; dsimp [c]; module
  have hProj (z : Ground k M) : U J c (U J c z) = U J c z := by
    have h := ((freudenthal_is_jordan J hJ.1) k).1 c (unit J)
    simpa only [hc, J.op_unit, mul_one, Module.End.mul_apply] using
      (congrArg (fun f : Module.End k (Ground k M) => f z) h).symm
  have hp (z : PeirceZero J e) : U J c z.val = z.val := by
    obtain ⟨w, hw⟩ := z.property
    change U J c w = z.val at hw
    rw [← hw, hProj]
  have hca : sharp J F c = e := (hA c).symm.trans hac
  have hOp' (x y : Ground k M) : U J x y = T x y • x - QuadraticMap.polar (sharp J F) (sharp J F x) y := by
    simpa only [QuadraticMap.polar, hT] using hOp x y
  have hOpE (z : Ground k M) : U J e z = T e z • e := by
    have hzero : QuadraticMap.polar (sharp J F) 0 z = 0 := by
      simpa only [QuadraticMap.polar, hA] using QuadraticMap.polar_zero_left A z
    rw [hOp', he.2, hzero, sub_zero]
  have hce : U J c e = 0 := by
    have hcc : T c e = 0 := by
      have hsym (x y : Ground k M) : T x y = T y x := by
        rw [hT, hT]
        simp only [pairing, add_comm x y]
        ring
      have hdiag : T e e = 1 := by
        have hsum : A (e + e) = 0 := by rw [QuadraticMap.map_add_self, hae, smul_zero]
        have hz (x : Ground k M) (hx : A x = 0) : F.quadraticTrace.eval k x = 0 := by
          rw [hQuadTrace]
          change trace F (sharp J F x) = 0
          rw [← hA, hx, ht, map_zero]
        have htr : F.trace.eval k e = 1 := he.1
        rw [hT, pairing, htr, hz _ hsum, hz _ hae]
        ring
      change T (unit J - e) e = 0
      rw [map_sub, LinearMap.sub_apply, hdiag, hsym (unit J) e]
      change t e - 1 = 0
      rw [hte, sub_self]
    have hzero : QuadraticMap.polar (sharp J F) e e = 0 := by
      simpa only [hae, he.2, smul_zero, QuadraticMap.polar, hA] using QuadraticMap.polar_self A e
    rw [hOp', hcc, hca, hzero, zero_smul, sub_zero]
  have hc' : U J c c = c := by rw [map_sub, hc, hce, sub_zero]
  let q : QuadraticForm k (PeirceZero J e) :=
    t.compQuadraticMap (A.comp (PeirceZero J e).subtype)
  have hq (z : PeirceZero J e) : q z = trace F (sharp J F z.val) := by
    change t (A z.val) = _
    rw [hA, ht]
  have hPolar (z w : PeirceZero J e) :
      QuadraticMap.polar q z w = trace F z.val * trace F w.val - pairing F k z.val w.val := by
    simp only [QuadraticMap.polar, hq, ← hQuadTrace, pairing, Submodule.coe_add]
    ring
  have hSelf' (x y : Ground k M) : T (U J c x) y = T x (U J c y) := by
    simp only [hT, hSelf]
  have htC (w : PeirceZero J e) : T c w.val = trace F w.val := by
    have hsym : T c w.val = T w.val c := by
      rw [hT, hT]
      simp only [pairing, add_comm c w.val]
      ring
    rw [hsym, ← hc, ← hSelf', hp, hT, ← hTrace]
  have htc' : trace F c = 2 := (ht c).trans htc
  let c₀ : PeirceZero J e := ⟨c, ⟨c, hc'⟩⟩
  have hq₀ : q c₀ = 1 := by
    rw [hq, show c₀.val = c from rfl, hca, he.1]
  refine ⟨hProj, hc', htc', q, ?_, hq, hq₀, ?_, hPolar, ?_⟩
  · intro z hz
    have hrad : ∀ x : Ground k M, T (z.val - t z.val • c) x = 0 := by
      intro x
      let w : PeirceZero J e := ⟨U J c x, ⟨x, rfl⟩⟩
      have hh := hz w
      rw [hPolar, ← hT, ht z.val, ← htC w, sub_eq_zero] at hh
      change t z.val * T c (U J c x) = T z.val (U J c x) at hh
      rw [← hSelf' c x, ← hSelf' z.val x, hc', hp] at hh
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ← hh, sub_self]
    have h_eq : z.val = t z.val • c := by
      apply sub_eq_zero.mp
      apply hTperf.bijective_left.injective
      apply LinearMap.ext
      intro x
      simpa using hrad x
    have htz := congrArg t h_eq
    rw [map_smul, htc, smul_eq_mul] at htz
    have hz0 : t z.val = 0 := by linear_combination -htz
    apply Subtype.ext
    simpa [hz0] using h_eq
  · intro z
    have hz := hCov c z.val
    rw [hp, hca, hOpE] at hz
    have hv := congrArg t hz
    rw [map_smul, hte, smul_eq_mul, mul_one] at hv
    have hs : sharp J F z.val = q z • e := by rw [hq, ht, hv, ← hz]
    refine ⟨hs, ?_⟩
    rw [hAsq, hA, hs, map_smul, hte, smul_eq_mul, mul_one, ← ht]
    module
  · intro z
    refine ⟨(hT _ _).symm.trans (htC z), ?_⟩
    change QuadraticMap.polar q c₀ z = trace F z.val
    rw [hPolar, show c₀.val = c from rfl, ← hT, htc', htC]
    ring

end Corner


section Squares

open scoped BigOperators

open private coordinate_ext adjointCross_diagonal adjointCross_block from
  LinearAlgebraicGroups.Albert.CubicIdentities
open private triple_formula from LinearAlgebraicGroups.Albert.QuadraticOperators

private theorem split_squares_separate {B : Type u} [CommRing B]
    (L : SplitRank.octonion.Model B →ₗ[B] B)
    (h : ∀ x, L (applyOperator (modelNorm B) (LowerRankSpecification.untwisted B) x cubicUnit) = 0) :
    L = 0 := by
  let n := modelNorm B
  let γ := LowerRankSpecification.untwisted B
  have hFrame := hermitian_frame (R := B) (A := Zorn B) n γ
  have hAxis (i : Fin 3) : L (FrameSpecification.frameAxis i) = 0 := by
    have hs := h (FrameSpecification.frameAxis (R := B) (A := Zorn B) i)
    change L (applyOperator n γ (FrameSpecification.frameAxis i) CubicSpecification.cubicUnit) = 0 at hs
    rw [hFrame.2.2.2.2.2.1 i] at hs
    exact hs
  have hBlock (i : Fin 3) (b : Zorn B) : L (CubicSpecification.singleBlockCoordinates i b) = 0 := by
    let e : SplitRank.octonion.Model B := FrameSpecification.frameAxis (cyclicNext i)
    let d : SplitRank.octonion.Model B := CubicSpecification.singleBlockCoordinates i b
    have hCross : CubicSpecification.adjointCross n γ e d = 0 := by
      have hi : i ≠ cyclicNext i := by fin_cases i <;> decide
      apply coordinate_ext
      · intro j
        simp [adjointCross_diagonal, e, d, FrameSpecification.frameAxis,
          CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates]
      · intro j
        by_cases hj : j = i
        · subst j
          simp [adjointCross_block, e, d, FrameSpecification.frameAxis,
            CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates,
            Pi.single_apply, hi, hi.symm]
        · simp [adjointCross_block, e, d, FrameSpecification.frameAxis,
            CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates,
            Pi.single_apply, hj]
    have hTraceE : CubicSpecification.tracePairing n γ e CubicSpecification.cubicUnit = 1 := by
      change CubicSpecification.linearTrace n γ e = 1
      rw [linearTrace_apply]
      simp [e, FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates]
    have hTraceD : CubicSpecification.tracePairing n γ d CubicSpecification.cubicUnit = 0 := by
      change CubicSpecification.linearTrace n γ d = 0
      rw [linearTrace_apply]
      simp [d, CubicSpecification.singleBlockCoordinates]
    have hp := triple_formula (n := n) γ e CubicSpecification.cubicUnit d
    change _ = _ + _ - CubicSpecification.adjointCross n γ (CubicSpecification.adjointCross n γ e d) CubicSpecification.cubicUnit at hp
    rw [hTraceE, hTraceD, hCross, one_smul, zero_smul, add_zero] at hp
    have h0 : CubicSpecification.adjointCross n γ 0 CubicSpecification.cubicUnit = 0 := by
      obtain ⟨q, _, hq⟩ := cubicAdjoint_isQuadratic (n := n) γ
      rw [← hq]
      exact QuadraticMap.polar_zero_left q _
    rw [h0, sub_zero] at hp
    change L d = 0
    rw [← hp]
    simp only [QuadraticOperatorSpecification.triple, map_sub]
    have hsq (x : SplitRank.octonion.Model B) : L (applyOperator n γ x CubicSpecification.cubicUnit) = 0 := h x
    simp [hsq]
  apply LinearMap.ext
  intro x
  have decomp := hFrame.2.2.2.2.2.2 x
  simp only [hFrame.2.2.1, hFrame.2.2.2.1] at decomp
  rw [LinearMap.zero_apply, ← decomp, map_sum]
  simp only [map_add, map_smul, hAxis, hBlock, smul_zero, add_zero, Finset.sum_const_zero]

private theorem exists_trace_operator (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (y : Ground k M) (hy : y ≠ 0) :
    ∃ a : Ground k M, trace F (U J a y) ≠ 0 := by
  obtain ⟨hSelf, _, _, _⟩ := operatorSymmetryCovariance hJ hF
  obtain ⟨_, _, _, hTrace, _, _, _⟩ := intrinsic_cubic_recovery J F hJ hF k
  by_contra! h
  have ha (a : Ground k M) : pairing F k y (U J a (unit J)) = 0 :=
    (hSelf a y (unit J)).symm.trans ((hTrace _).symm.trans (h a))
  apply withSplitChart hJ
  intro B _ _ f _ hf c
  let m := pointMap (M := M) f
  let n := modelNorm B
  let γ := LowerRankSpecification.untwisted B
  let L := CubicSpecification.tracePairing n γ (c.coordinates (m y))
  let R := J.op B
  let Q := (L.comp c.coordinates.toLinearMap).compQuadraticMap
    ((LinearMap.applyₗ (1 ⊗ₜ[k] J.unit : B ⊗[k] M) : Module.End B (B ⊗[k] M) →ₗ[B] B ⊗[k] M).compQuadraticMap R)
  have hQ : Q = 0 := by
    apply baseChange_ext
    intro x
    have hx : m (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by simp [m]
    have hu : m (unit J) = (1 ⊗ₜ[k] J.unit) := by simp [m]
    have hm := (pairing_natural F f y (U J (1 ⊗ₜ[k] x) (unit J))).trans
      (chart_pairing hF c _ _)
    rw [ha, map_zero] at hm
    change Q (1 ⊗ₜ[k] x) = 0
    change L (c.coordinates (J.op B (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] J.unit))) = 0
    rw [← hx, ← hu, ← J.natural]
    exact hm.symm
  have hL : L = 0 := by
    apply split_squares_separate
    intro x
    obtain ⟨z, rfl⟩ := c.coordinates.surjective x
    change L (applyOperator _ _ (c.coordinates z) CubicSpecification.cubicUnit) = 0
    rw [← c.unit, ← c.op]
    have hz := congrArg (fun q : QuadraticForm B (B ⊗[k] M) => q z) hQ
    exact hz
  have hPerfect := tracePairing_perfect (n := n) γ (Zorn.isOctonion B).perfect
  have h0 : c.coordinates (m y) = 0 := by
    apply hPerfect.bijective_left.injective
    rw [map_zero]
    exact hL
  apply hy
  apply hf
  apply c.coordinates.injective
  simpa using h0

/-- Trace against squares is a quadratic law. Its values on ground-field vectors
determine it after scalar extension, including over finite fields. -/
private theorem rankOneIdempotentOfNormZero
    (J : ParaQuadratic k M) (F : Coefficients k M) (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (hNorm : ∃ x : Ground k M, x ≠ 0 ∧ norm F x = 0) :
    ∃ e : Ground k M, IsRankOne J F e ∧ U J e (unit J) = e := by
  obtain ⟨y, hy, hyA⟩ := zeroAdjointFromNorm J F hJ hF hNorm
  obtain ⟨a, ha⟩ := exists_trace_operator hJ hF y hy
  obtain ⟨_, hCov, _, _⟩ := operatorSymmetryCovariance hJ hF
  obtain ⟨A, hA⟩ := sharp_quadratic hJ hF
  obtain ⟨⟨T, _, hT⟩, _, _, hTrace, hS, _, _⟩ := intrinsic_cubic_recovery J F hJ hF k
  have ht (x : Ground k M) : trace F x = T x (unit J) := (hTrace x).trans (hT _ _).symm
  let z := U J a y
  have hz : sharp J F z = 0 := by rw [hCov, hyA, map_zero]
  let e := (trace F z)⁻¹ • z
  have he₁ : trace F e = 1 := by
    rw [ht, show e = (trace F z)⁻¹ • z from rfl, map_smul, LinearMap.smul_apply, smul_eq_mul, ← ht]
    exact inv_mul_cancel₀ ha
  have he₂ : sharp J F e = 0 := by
    rw [← hA, show e = (trace F z)⁻¹ • z from rfl, QuadraticMap.map_smul, hA, hz, smul_zero]
  refine ⟨e, ⟨he₁, he₂⟩, ?_⟩
  have hs : F.quadraticTrace.eval k e = 0 := by
    rw [hS]
    change trace F (sharp J F e) = 0
    rw [he₂, ht, map_zero, LinearMap.zero_apply]
  have hh := he₂
  change U J e (unit J) - trace F e • e + F.quadraticTrace.eval k e • unit J = 0 at hh
  simpa [he₁, hs, sub_eq_zero] using hh

theorem idempotentFromNorm : IdempotentFromNorm.{u,v} := by
  intro k _ _ M _ _ J F
  exact rankOneIdempotentOfNormZero J F

end Squares

section Hyperbolic

variable {V : Type v} [AddCommGroup V] [Module k V]

private theorem linear_ne_zero_on_isotropic (Q : QuadraticForm k V)
    (hB : ∀ x : V, (∀ y : V, QuadraticMap.polar Q x y = 0) → x = 0)
    (hIso : ∃ u : V, u ≠ 0 ∧ Q u = 0)
    (l : V →ₗ[k] k) (hl : l ≠ 0) :
    ∃ x : V, Q x = 0 ∧ l x ≠ 0 := by
  let B : LinearMap.BilinForm k V := Q.polarBilin
  have hSym (x y : V) : B x y = B y x := QuadraticMap.polar_comm Q _ _
  have hAdd (x y : V) : Q (x + y) = Q x + Q y + B x y := QuadraticMap.map_add Q _ _
  have hSmul (a : k) (x : V) : Q (a • x) = a * a * Q x := QuadraticMap.map_smul Q _ _
  obtain ⟨u, hu, hu0⟩ := hIso
  have h := mt (hB u) hu
  push Not at h
  obtain ⟨y, hy⟩ := h
  change B u y ≠ 0 at hy
  let v₀ := (B u y)⁻¹ • y
  have huv₀ : B u v₀ = 1 := by simp [v₀, map_smul, inv_mul_cancel₀ hy]
  have huu : B u u = 0 := by
    change QuadraticMap.polar Q u u = 0
    simp [QuadraticMap.polar_self, hu0]
  let v := v₀ + (-Q v₀) • u
  have hv0 : Q v = 0 := by
    dsimp only [v]
    rw [hAdd, hSmul (-Q v₀) u, hu0, map_smul (B v₀), hSym v₀ u, huv₀]
    simp
  have huv : B u v = 1 := by simp [v, map_add, map_smul, huv₀, huu]
  have hvv : B v v = 0 := by
    change QuadraticMap.polar Q v v = 0
    simp [QuadraticMap.polar_self, hv0]
  by_contra! hn
  have hlu := hn u hu0
  have hlv := hn v hv0
  apply hl
  ext x
  let w := x - B x v • u - B x u • v
  have hwu : B w u = 0 := by
    simp [w, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hSym v u, huu, huv]
  have hwv : B w v = 0 := by
    simp [w, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, huv, hvv]
  let z := w + u + (-Q w) • v
  have hz : Q z = 0 := by
    dsimp only [z]
    have hb : B (w + u) v = 1 := by rw [map_add B, LinearMap.add_apply, hwv, huv, zero_add]
    rw [hAdd, hAdd w u, hSmul (-Q w) v, hu0, hv0, map_smul (B (w + u)), hwu, hb]
    simp
  have hlz := hn z hz
  simpa [z, w, map_add, map_sub, map_smul, hlu, hlv] using hlz

end Hyperbolic

/-- An isotropic Peirce-zero form supplies the other two members of the frame. -/
theorem frameCompletion : FrameCompletion.{u,v} := by
  intro k _ M _ _ J F hJ hF e he hIso
  obtain ⟨hproj, hc, htc, Q, hB, hQ, hq₀, hSharp, _, hCorner⟩ := cornerIdentities hJ hF e he
  obtain ⟨A, hA⟩ := sharp_quadratic hJ hF
  obtain ⟨_, _, hCross, _⟩ := operatorSymmetryCovariance hJ hF
  obtain ⟨⟨T, _, hT⟩, _, hOne, hTrace, hS, _, hOp⟩ :=
    intrinsic_cubic_recovery J F hJ hF k
  let c := unit J - e
  let c₀ : PeirceZero J e := ⟨c, ⟨c, hc⟩⟩
  let t : Ground k M →ₗ[k] k := T.flip (unit J)
  have ht (x : Ground k M) : trace F x = t x := (hTrace x).trans (hT _ _).symm
  have hSym (x y : Ground k M) : T x y = T y x := by
    rw [hT, hT]
    simp only [pairing, add_comm x y]
    ring
  have hAc (x : Ground k M) (hx : IsRankOne J F x) : A (unit J - x) = x := by
    have hi : QuadraticMap.polar A (unit J) x = unit J - x := by
      simpa [QuadraticMap.polar, hA, hx.1] using hCross x
    rw [sub_eq_add_neg, QuadraticMap.map_add A, QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right, hi, hA, show sharp J F (unit J) = unit J from hOne, hA, hx.2]
    abel
  have hSquare (x : Ground k M) (hx : IsRankOne J F x) : U J x (unit J) = x := by
    have hh := hx.2
    change U J x (unit J) - trace F x • x + F.quadraticTrace.eval k x • unit J = 0 at hh
    have hs : F.quadraticTrace.eval k x = 0 := by
      rw [hS]
      change trace F (sharp J F x) = 0
      rw [hx.2, ht, map_zero]
    simpa [hx.1, hs, sub_eq_zero] using hh
  have hFix (z : PeirceZero J e) : U J c z.val = z.val := by
    obtain ⟨x, hx⟩ := z.property
    change U J c x = z.val at hx
    rw [← hx, hproj]
  have hTc (z : PeirceZero J e) : T z.val c = trace F z.val :=
    (hSym _ _).trans ((hT _ _).trans (hCorner z).1)
  have hPc (z : PeirceZero J e) : QuadraticMap.polar Q c₀ z = trace F z.val :=
    (hCorner z).2
  have hl : t.comp (PeirceZero J e).subtype ≠ 0 := by
    intro hzero
    have hcZ := hB c₀ (by
      intro z
      rw [hPc, ht]
      exact LinearMap.congr_fun hzero z)
    have hq := congrArg (fun z : PeirceZero J e => Q z) hcZ
    rw [hq₀, QuadraticMap.map_zero] at hq
    exact one_ne_zero hq
  have hIsoQ : ∃ u : PeirceZero J e, u ≠ 0 ∧ Q u = 0 := by
    simpa only [hQ] using hIso
  obtain ⟨z₀, hzQ, hzT⟩ := linear_ne_zero_on_isotropic (k := k) (V := PeirceZero J e) Q hB hIsoQ
      (t.comp (PeirceZero J e).subtype) hl
  let z : PeirceZero J e := (t z₀.val)⁻¹ • z₀
  have hz₁ : trace F z.val = 1 := by
    rw [ht]
    change t ((t z₀.val)⁻¹ • z₀.val) = 1
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hzT
  have hz₂ : Q z = 0 := by simp [z, QuadraticMap.map_smul, hzQ]
  have hz : IsRankOne J F z.val := ⟨hz₁, by rw [(hSharp z).1, hz₂, zero_smul]⟩
  let w := c₀ - z
  have hw₁ : trace F w.val = 1 := by
    rw [ht]
    change t (c - z.val) = 1
    rw [map_sub, ← ht, ← ht, htc, hz₁]
    ring
  have hw₂ : Q w = 0 := by
    dsimp only [w]
    have hs : c₀ - z = c₀ + -z := Subtype.ext (sub_eq_add_neg c₀.val z.val)
    have hneg : (-z : PeirceZero J e) = (-1 : k) • z :=
      Subtype.ext (neg_one_smul k z.val).symm
    have hp : QuadraticMap.polar Q c₀ ((-1 : k) • z) = (-1 : k) • QuadraticMap.polar Q c₀ z :=
      QuadraticMap.polar_smul_right (R := k) (M := ↥(PeirceZero J e)) (N := k) Q (-1) c₀ z
    rw [hs, QuadraticMap.map_add Q, hneg, QuadraticMap.map_smul Q,
      hp, hPc, hq₀, hz₁, hz₂]
    simp
  have hw : IsRankOne J F w.val := ⟨hw₁, by rw [(hSharp w).1, hw₂, zero_smul]⟩
  have hTez : T e z.val = 0 := by
    have hl := hTc z
    rw [ht] at hl
    change T z.val (unit J - e) = T z.val (unit J) at hl
    rw [map_sub, sub_eq_self] at hl
    rw [hSym, hl]
  have hTew : T e w.val = 0 := by
    have hl := hTc w
    rw [ht] at hl
    change T w.val (unit J - e) = T w.val (unit J) at hl
    rw [map_sub, sub_eq_self] at hl
    rw [hSym, hl]
  have hDiag (x : Ground k M) (hx : IsRankOne J F x) : T x x = 1 := by
    have ha : A x = 0 := (hA x).trans hx.2
    have hsum : A (x + x) = 0 := by rw [QuadraticMap.map_add_self, ha, smul_zero]
    have hz (y : Ground k M) (hy : A y = 0) : F.quadraticTrace.eval k y = 0 := by
      rw [hS]
      change trace F (sharp J F y) = 0
      rw [← hA, hy, ht, map_zero]
    have hx₁ : F.trace.eval k x = 1 := hx.1
    rw [hT, pairing, hx₁, hz _ hsum, hz _ ha]
    ring
  have hTzw : T z.val w.val = 0 := by
    change T z.val (c - z.val) = 0
    rw [map_sub, hTc, hDiag _ hz, hz₁, sub_self]
  have hOperator (x y : Ground k M) :
      U J x y = T x y • x - QuadraticMap.polar A (A x) y := by
    simpa only [QuadraticMap.polar, hA, hT] using hOp x y
  have hCrossEz : QuadraticMap.polar A e z.val = w.val := by
    have h := hOperator c z.val
    have hAc' : A c = e := hAc e he
    rw [hFix, hSym c, hTc, hz₁, one_smul, hAc'] at h
    change _ = c - z.val
    calc
      _ = c - (c - QuadraticMap.polar A e z.val) := by abel
      _ = c - z.val := congrArg (fun x => c - x) h.symm
  have hCrossOne (x : Ground k M) : QuadraticMap.polar A (unit J) x = trace F x • unit J - x := by
    simpa only [QuadraticMap.polar, hA] using hCross x
  have hCrossEw : QuadraticMap.polar A e w.val = z.val := by
    change QuadraticMap.polar A e (unit J - e - z.val) = _
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_comm A e (unit J), hCrossOne, he.1, one_smul,
      QuadraticMap.polar_self, hA, he.2, smul_zero, sub_zero, hCrossEz]
    change c - (c - z.val) = _
    abel
  have hCrossZw : QuadraticMap.polar A z.val w.val = e := by
    change QuadraticMap.polar A z.val (unit J - e - z.val) = _
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_comm A z.val (unit J), hCrossOne, hz₁, one_smul,
      QuadraticMap.polar_comm A z.val e, hCrossEz,
      QuadraticMap.polar_self, hA, hz.2, smul_zero, sub_zero]
    change unit J - z.val - (unit J - e - z.val) = _
    abel
  let f : Fin 3 → Ground k M := ![e, z.val, w.val]
  have hf (i : Fin 3) : IsRankOne J F (f i) := by
    fin_cases i <;> first | exact he | exact hz | exact hw
  have hPairs (i j : Fin 3) (hij : i ≠ j) :
      T (f i) (f j) = 0 ∧ QuadraticMap.polar A (f i) (f j) =
        (unit J - f i) - f j := by
    have hsw (x y : Ground k M) :
        (unit J - x) - y = (unit J - y) - x := by abel
    have hEZ : QuadraticMap.polar A e z.val = unit J - e - z.val := hCrossEz
    have hEW : QuadraticMap.polar A e w.val = unit J - e - w.val := by
      rw [hCrossEw]
      change z.val = c - (c - z.val)
      abel
    have hZW : QuadraticMap.polar A z.val w.val = unit J - z.val - w.val := by
      rw [hCrossZw]
      change e = unit J - z.val - (unit J - e - z.val)
      abel
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact ⟨hTez, hEZ⟩
    · exact ⟨hTew, hEW⟩
    · exact ⟨(hSym _ _).trans hTez,
        (QuadraticMap.polar_comm A _ _).trans (hEZ.trans (hsw _ _))⟩
    · exact ⟨hTzw, hZW⟩
    · exact ⟨(hSym _ _).trans hTew,
        (QuadraticMap.polar_comm A _ _).trans (hEW.trans (hsw _ _))⟩
    · exact ⟨(hSym _ _).trans hTzw,
        (QuadraticMap.polar_comm A _ _).trans (hZW.trans (hsw _ _))⟩
  refine ⟨f, rfl, rfl, ⟨(fun i => ⟨hf i, hSquare _ (hf i)⟩), ?_, ?_⟩,
    z, rfl, hz₁, (hQ z).symm.trans hz₂⟩
  · intro i j hij
    obtain ⟨hijT, hijA⟩ := hPairs i j hij
    constructor
    · rw [hOperator, hAc _ (hf i)]
      have hh : T (unit J - f i) (f j) = 1 := by
        rw [map_sub, LinearMap.sub_apply, hijT, sub_zero, hSym, hT, ← hTrace]
        exact (hf j).1
      rw [hh, one_smul, hijA]
      abel
    · have hi : A (f i) = 0 := (hA _).trans (hf i).2
      rw [hOperator, hijT, hi, QuadraticMap.polar_zero_left, zero_smul, sub_zero]
  · change e + z.val + (unit J - e - z.val) = _
    abel

section ProjectorRank

private theorem range_retraction {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P : V →ₗ[R] V) (hP : ∀ x, P (P x) = P x) :
    P.rangeRestrict.comp (LinearMap.range P).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change P x.val = x.val
  rw [← hy, hP]

private def rangeBaseChange {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] (P : V →ₗ[R] V) (hP : ∀ x, P (P x) = P x) :
    (S ⊗[R] LinearMap.range P) ≃ₗ[S] LinearMap.range (P.baseChange S) := by
  let i := (LinearMap.range P).subtype.baseChange S
  let p := P.rangeRestrict.baseChange S
  have hp : p.comp i = LinearMap.id := by
    dsimp only [i, p]
    rw [← LinearMap.baseChange_comp, range_retraction P hP, LinearMap.baseChange_id]
  have hi : i.comp p = P.baseChange S := by
    dsimp only [i, p]
    rw [← LinearMap.baseChange_comp]
    rfl
  let j : (S ⊗[R] LinearMap.range P) →ₗ[S] LinearMap.range (P.baseChange S) :=
    i.codRestrict _ fun x => ⟨i x, by
      rw [← LinearMap.congr_fun hi (i x), LinearMap.comp_apply,
        ← LinearMap.comp_apply p i, hp, LinearMap.id_apply]⟩
  apply LinearEquiv.ofBijective j
  constructor
  · intro x y h
    have h' : i x = i y := congrArg Subtype.val h
    simpa only [← LinearMap.comp_apply, hp, LinearMap.id_apply] using congrArg p h'
  · intro x
    obtain ⟨y, hy⟩ := x.property
    refine ⟨p y, Subtype.ext ?_⟩
    change i (p y) = x.val
    rw [← LinearMap.comp_apply, hi, hy]

private def rangeCongr {R V W : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] (P : V →ₗ[R] V) (Q : W →ₗ[R] W) (e : V ≃ₗ[R] W)
    (h : ∀ x, e (P x) = Q (e x)) :
    LinearMap.range P ≃ₗ[R] LinearMap.range Q := by
  let E := (e.toLinearMap.comp (LinearMap.range P).subtype).codRestrict (LinearMap.range Q)
    (fun x => by obtain ⟨y, hy⟩ := x.property; exact ⟨e y, (h y).symm.trans (congrArg e hy)⟩)
  refine LinearEquiv.ofBijective E ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
  · intro x
    obtain ⟨y, hy⟩ := x.property
    refine ⟨⟨P (e.symm y), ⟨e.symm y, rfl⟩⟩, Subtype.ext ?_⟩
    change e (P (e.symm y)) = _
    rw [h, e.apply_symm_apply, hy]

private theorem rankAtEvaluation {R S V : Type*} [CommRing R] [Field S] [Algebra R S]
    [AddCommGroup V] [Module R V] (P : V →ₗ[R] V)
    [Module.Flat R (LinearMap.range P)] [Module.Finite R (LinearMap.range P)]
    (hP : ∀ x, P (P x) = P x) :
    Module.finrank S (LinearMap.range (P.baseChange S)) =
      Module.rankAtStalk (LinearMap.range P)
        (PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S)) := by
  rw [← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free, (rangeBaseChange P hP).finrank_eq]
  rfl

private theorem intertwines_baseChange {R S V W : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    (P : V →ₗ[R] V) (Q : W →ₗ[S] W) (E : S ⊗[R] V ≃ₗ[S] W)
    (h : ∀ x, E (1 ⊗ₜ[R] P x) = Q (E (1 ⊗ₜ[R] x))) :
    ∀ x, E (P.baseChange S x) = Q (E x) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, ← mul_one a, ← smul_eq_mul,
      ← smul_tmul', ← smul_tmul', map_smul, map_smul, map_smul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

open TrialitySpecification (Model modelOp)
open IdempotentSpecification (IdempotentPoint IsRankOneIdempotent IdempotentRing
  idempotentOfHom firstScheme)
open private opEnd opEnd_apply from LinearAlgebraicGroups.Albert.QuadraticOperators
open private modelBaseChange modelBaseChange_tmul from LinearAlgebraicGroups.Albert.IntrinsicCubic
open private mapModel modelOfVariables_map modelOp_map mapModel_unit mapModel_sub
  second_projector axis_rank_one from
  LinearAlgebraicGroups.Albert.IdempotentCharts

private abbrev splitProjector {R : Type u} [CommRing R] (e : Model R) : Module.End R (Model R) :=
  opEnd (n := modelNorm R) (LowerRankSpecification.untwisted R) (cubicUnit - e)

private theorem splitProjector_apply {R : Type u} [CommRing R] (e x : Model R) :
    splitProjector e x = modelOp (cubicUnit - e) x :=
  opEnd_apply (LowerRankSpecification.untwisted R) _ _

private theorem splitProjector_idempotent {R : Type u} [CommRing R] (e : IdempotentPoint R) :
    ∀ x, splitProjector e.val (splitProjector e.val x) = splitProjector e.val x := by
  let n := modelNorm R
  let γ := LowerRankSpecification.untwisted R
  let c : Model R := cubicUnit - e.val
  obtain ⟨A, hA, hPolar⟩ := cubicAdjoint_isQuadratic (n := n) γ
  obtain ⟨heT, heA⟩ := e.property
  change CubicSpecification.linearTrace n γ e.val = 1 at heT
  change CubicSpecification.cubicAdjoint n γ e.val = 0 at heA
  obtain ⟨_, hUnit, hCross⟩ := cubic_unit_identities (n := n) γ
  have hAC : CubicSpecification.cubicAdjoint n γ c = e.val := by
    rw [← hA]
    change A (cubicUnit - e.val) = _
    have hp : QuadraticMap.polar A cubicUnit e.val = cubicUnit - e.val := by
      rw [← QuadraticMap.polarBilin_apply_apply, hPolar, hCross, heT, one_smul]
    rw [sub_eq_add_neg, QuadraticMap.map_add A, QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right, hp, hA, hA, heA, hUnit]
    abel
  have hTrace : CubicSpecification.linearTrace n γ c = 2 := by
    change CubicSpecification.linearTrace n γ (cubicUnit - e.val) = 2
    rw [map_sub, heT, linearTrace_apply]
    simp [CubicSpecification.cubicUnit]
    ring
  have hIds := cubic_operator_identities γ (Zorn.isOctonion R)
  have hC : modelOp c cubicUnit = c := by
    have h := hIds.2.2.2.2.2.2.2.2.1 c
    change modelOp c cubicUnit = CubicSpecification.cubicAdjoint n γ c +
      CubicSpecification.linearTrace n γ c • c -
      CubicSpecification.linearTrace n γ (CubicSpecification.cubicAdjoint n γ c) • cubicUnit at h
    rw [h, hAC, hTrace, heT, one_smul, two_smul]
    dsimp [c]
    abel
  intro x
  simp only [splitProjector_apply]
  change modelOp c (modelOp c x) = modelOp c x
  have h := hIds.2.2.2.2.2.2.1 c cubicUnit x
  change modelOp (modelOp c cubicUnit) x = modelOp c (modelOp cubicUnit (modelOp c x)) at h
  have hUnitOp (y : Model R) : modelOp cubicUnit y = y := hIds.1 y
  rw [hC, hUnitOp] at h
  exact h.symm

private theorem standardProjector_rank (K : Type u) [Field K] :
    Module.finrank K (LinearMap.range (splitProjector (frameAxis 0 : Model K))) = 10 := by
  let P := splitProjector (frameAxis 0 : Model K)
  let L : Model K →ₗ[K] (K × K) × Zorn K :=
    (((LinearMap.proj 1).comp (LinearMap.fst K _ _)).prod
      ((LinearMap.proj 2).comp (LinearMap.fst K _ _))).prod
      ((LinearMap.proj 0).comp (LinearMap.snd K _ _))
  let f := L.comp (LinearMap.range P).subtype
  have hP (x : Model K) :
      P x = ((fun i => if i = 0 then 0 else x.1 i), Pi.single 0 (x.2 0)) :=
    (splitProjector_apply _ _).trans (second_projector x)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, ⟨p, rfl⟩⟩ ⟨y, ⟨q, rfl⟩⟩ h
      have h' : (((P p).1 1, (P p).1 2), (P p).2 0) =
          (((P q).1 1, (P q).1 2), (P q).2 0) := h
      simp only [hP, Fin.reduceEq, ↓reduceIte, Pi.single_eq_same, Prod.mk.injEq] at h'
      apply Subtype.ext
      change P p = P q
      rw [hP, hP, h'.2]
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact h'.1.1
      · exact h'.1.2
    · rintro ⟨⟨a,b⟩,d⟩
      let z : Model K := (![0,a,b], Pi.single 0 d)
      refine ⟨⟨P z, ⟨z, rfl⟩⟩, ?_⟩
      change (((P z).1 1, (P z).1 2), (P z).2 0) = _
      simp [hP, z]
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, (Zorn.pairedColumns K).finrank_eq, Module.finrank_prod,
    Module.finrank_pi]
  rfl

private theorem splitProjector_rank (K : Type u) [Field K] [IsAlgClosed K]
    (e : IdempotentPoint K) :
    Module.finrank K (LinearMap.range (splitProjector e.val)) = 10 := by
  let R := IdempotentRing K
  obtain ⟨rep, hrep⟩ := IdempotentCharts.firstRepresentation K R
  let E : IdempotentPoint R := rep (AlgHom.id K R)
  let P := splitProjector E.val
  have hp := splitProjector_idempotent E
  letI : Module.Flat R (LinearMap.range P) :=
    Module.Flat.of_retract _ _ (range_retraction P hp)
  have hSpec := (IdempotentCharts.firstGeometry K).2.1
  change IrreducibleSpace (PrimeSpectrum R) at hSpec
  letI := hSpec
  let hIrred := IrreducibleSpace.isIrreducible_univ (PrimeSpectrum R)
  have hgen (p : PrimeSpectrum R) : hIrred.genericPoint ≤ p :=
    (PrimeSpectrum.le_iff_specializes _ _).2
      ((hIrred.isGenericPoint_genericPoint isClosed_univ).specializes (Set.mem_univ p))
  have rankCompare (y : IdempotentPoint K) :
      Module.finrank K (LinearMap.range (splitProjector y.val)) =
        Module.rankAtStalk (LinearMap.range P) hIrred.genericPoint := by
    obtain ⟨repK, hrepK⟩ := IdempotentCharts.firstRepresentation K K
    obtain ⟨f, hf⟩ := repK.surjective y
    letI : Algebra R K := f.toRingHom.toAlgebra
    let C := modelBaseChange R K
    have hEval : mapModel f.toRingHom E.val = y.val := by
      rw [hrep, ← hf, hrepK]
      exact (modelOfVariables_map f.toRingHom _).symm
    have hComm := intertwines_baseChange P (splitProjector y.val) C (by
      intro x
      simp only [C, modelBaseChange_tmul, one_smul, P, splitProjector_apply]
      change mapModel f.toRingHom (modelOp (cubicUnit - E.val) x) =
        modelOp (cubicUnit - y.val) (mapModel f.toRingHom x)
      rw [← hEval, ← mapModel_unit f.toRingHom, ← mapModel_sub, ← modelOp_map])
    rw [← (rangeCongr _ _ C hComm).finrank_eq, rankAtEvaluation P hp]
    exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (hgen _)).symm
  exact (rankCompare e).trans ((rankCompare ⟨frameAxis 0, axis_rank_one 0⟩).symm.trans
    (standardProjector_rank K))

private theorem corner_rank (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (e : Ground k M) (he : IsRankOne J F e) (hP : ∀ z, U J (unit J - e) (U J (unit J - e) z) =
      U J (unit J - e) z) : Module.finrank k (PeirceZero J e) = 10 := by
  obtain ⟨B, _, _, hflat, d, hd, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  letI := hflat
  letI : Nontrivial B := (FaithfulSMul.algebraMap_injective k B).nontrivial
  obtain ⟨I, hI⟩ := Ideal.exists_maximal B
  letI := hI
  let L := B ⧸ I
  letI : Field L := Ideal.Quotient.field I
  let K := AlgebraicClosure L
  let b : B →+* K := (algebraMap L K).comp (Ideal.Quotient.mk I)
  letI : Algebra k K := (b.comp (algebraMap k B)).toAlgebra
  let f : B →ₐ[k] K := ⟨b, fun _ => rfl⟩
  let c := extendChart (⟨d, hd, hop⟩ : SplitChart J B) f
  let m := pointMap (M := M) (Algebra.ofId k K)
  let a := c.coordinates (m e)
  have hUnit : m (unit J) = (1 ⊗ₜ[k] J.unit) := by simp [m]
  have ha : IsRankOneIdempotent a := by
    change CubicSpecification.linearTrace (modelNorm K) (LowerRankSpecification.untwisted K) a = 1 ∧
      CubicSpecification.cubicAdjoint (modelNorm K) (LowerRankSpecification.untwisted K) a = 0
    refine ⟨?_, ?_⟩
    · have h := ((intrinsic_coefficients J hJ).2 F hF K c (m e)).1
      rw [← h]
      exact (F.trace.natural (Algebra.ofId k K) e).trans (by
        change Algebra.ofId k K (trace F e) = 1
        rw [he.1, map_one])
    · have h := chart_adjoint hF c (m e)
      rw [← h]
      have hh := adjoint_natural (J := J) (F := F) (Algebra.ofId k K) e
      change m (sharp J F e) = _ at hh
      rw [← hh, he.2, map_zero, map_zero]
  let P := U J (unit J - e)
  let C := (AlgebraTensorModule.cancelBaseChange k k K K M).trans c.coordinates
  have hC (x : Ground k M) : C (1 ⊗ₜ[k] x) = c.coordinates (m x) := by
    apply congrArg c.coordinates
    change AlgebraTensorModule.cancelBaseChange k k K K M (1 ⊗ₜ[k] x) = m x
    induction x using TensorProduct.inductionOn with
    | tmul b x => simp [AlgebraTensorModule.cancelBaseChange_tmul, m, Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  have hComm := intertwines_baseChange P (splitProjector a) C (by
    intro x
    rw [hC, hC, splitProjector_apply]
    change c.coordinates (m (J.op k (unit J - e) x)) = _
    dsimp only [m]
    rw [J.natural, c.op]
    change modelOp (c.coordinates (m (unit J - e))) (c.coordinates (m x)) = _
    rw [map_sub, map_sub, hUnit, c.unit])
  change Module.finrank k (LinearMap.range P) = 10
  letI : Module.Free k (LinearMap.range P) :=
    Module.Free.of_divisionRing k (LinearMap.range P)
  rw [← Module.finrank_baseChange (R := K) (M' := LinearMap.range P), (rangeBaseChange P hP).finrank_eq,
    (rangeCongr _ _ C hComm).finrank_eq]
  exact splitProjector_rank K ⟨a, ha⟩

theorem peirceZeroStructure : PeirceZeroStructure.{u,v} := by
  intro k _ M _ _ J F hJ hF e he
  obtain ⟨hproj, hc, ht, q, hB, hQ, hq₀, hSharp, hPolar, hCorner⟩ :=
    cornerIdentities hJ hF e he
  exact ⟨hproj, hc, ht, corner_rank hJ hF e he hproj, q, hB, hQ, hq₀, hSharp, hPolar, hCorner⟩

end ProjectorRank

section NormAction

open private albert_baseChange characteristic_baseChange changeScalars_norm_eval from
  LinearAlgebraicGroups.Albert.IntrinsicCubic

private theorem norm_homogeneous (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (S : Type u) [CommRing S] [Algebra k S] (r : S) (x : S ⊗[k] M) :
    F.norm.eval S (r • x) = r ^ 3 * F.norm.eval S x := by
  obtain ⟨B, _, _, hflat, e, he, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  letI := hflat
  let E := S ⊗[k] B
  let f : S →ₐ[k] E := includeLeft
  let C := extendChart (⟨e, he, hop⟩ : SplitChart J B) (includeRight : B →ₐ[k] E)
  apply (FaithfulSMul.algebraMap_injective S E : Function.Injective f)
  change f (F.norm.eval S (r • x)) = f (r ^ 3 * F.norm.eval S x)
  rw [map_mul, map_pow, ← F.norm.natural f, ← F.norm.natural f]
  change F.norm.eval E (pointMap f (r • x)) = f r ^ 3 * F.norm.eval E (pointMap f x)
  rw [pointMap_smul, chart_norm hF C, chart_norm hF C, map_smul]
  exact cubicNorm_smul _ _ _

private theorem point_preserves_norm (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (S : Type u) [CommRing S] [Algebra k S] (g : S ⊗[k] M ≃ₗ[S] S ⊗[k] M)
    (hu : g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit)
    (hop : ∀ x y, g (J.op S x y) = J.op S (g x) (g y)) (x : S ⊗[k] M) :
    F.norm.eval S (g x) = F.norm.eval S x := by
  let L := J.baseChange S
  have hg : L.IsGroundIso L g := ⟨hu, by
    intro y z
    rw [J.groundOp_baseChange, J.groundOp_baseChange]
    exact hop y z⟩
  have h := ((intrinsic_norm_automorphisms L (F.changeScalars S) (albert_baseChange hJ)
    (characteristic_baseChange hF) g).mp ((L.isIso_iff_ground L g).mpr hg)).2
      S (1 ⊗ₜ[S] x)
  rw [LinearMap.baseChange_tmul, changeScalars_norm_eval, changeScalars_norm_eval] at h
  have ht (z : S ⊗[k] M) : AlgebraTensorModule.cancelBaseChange k S S S M (1 ⊗ₜ[S] z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul a m => simp [AlgebraTensorModule.cancelBaseChange_tmul]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  simpa only [ht, LinearEquiv.coe_coe] using h

end NormAction

section SplitCocharacter

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups (testSpec TestAlgebra specGroup)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)
open private pointsIso_spec from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

set_option backward.isDefEq.respectTransparency false

private abbrev Exponent := IntegerCharacters.{0}

private abbrev TorusAlgebra (k : Type) [Field k] := MonoidAlgebra k Exponent

private abbrev SplitTorus (k : Type) [Field k] := specGroup (groupAlgebra k Exponent)

private def torusPoint {k : Type} [Field k] (S : TestAlgebra k)
    (f : TorusAlgebra k →ₐ[k] S) : SpinSpecification.SchemePoints (SplitTorus k) S :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private def torusCharacters {k : Type} [Field k] (S : TestAlgebra k) :
    SpinSpecification.SchemePoints (SplitTorus k) S ≃* (Exponent →* Sˣ) :=
  ((groupAlgebraPointsIso k Exponent).app S).groupIsoToMulEquiv

private theorem torusPoint_character {k : Type} [Field k] (S : TestAlgebra k)
    (f : TorusAlgebra k →ₐ[k] S) (m : Exponent) :
    (torusCharacters S (torusPoint S f) m : S) =
      f (MonoidAlgebra.of k Exponent m) :=
  pointsIso_spec Exponent S f m

private theorem torusPoint_counit {k : Type} [Field k] :
    torusPoint (CommAlgCat.of k k) (Bialgebra.counitAlgHom k (TorusAlgebra k)) = 1 := by
  apply (torusCharacters (CommAlgCat.of k k)).injective
  rw [map_one]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change (torusCharacters _ (torusPoint (CommAlgCat.of k k) _) m : k) = 1
  rw [torusPoint_character]
  exact (MonoidAlgebra.isGroupLikeElem_of (R := k) m).counit_eq_one

private abbrev torusMap (k : Type) [Field k] (f : Exponent →* Exponent × Exponent) :=
  MonoidAlgebra.mapDomainAlgHom k k f

private theorem torusMap_monomial {k : Type} [Field k] (f : Exponent →* Exponent × Exponent)
    (m : Exponent) :
    torusMap k f (MonoidAlgebra.of k Exponent m) = MonoidAlgebra.of k _ (f m) := by
  exact MonoidAlgebra.mapDomain_single

private theorem torusPoint_diagonal {k : Type} [Field k] :
    let S := CommAlgCat.of k (MonoidAlgebra k (Exponent × Exponent))
    torusPoint S (torusMap k ((MonoidHom.id Exponent).prod (MonoidHom.id Exponent))) =
      torusPoint S (torusMap k (MonoidHom.inl Exponent Exponent)) *
        torusPoint S (torusMap k (MonoidHom.inr Exponent Exponent)) := by
  dsimp only
  let S := CommAlgCat.of k (MonoidAlgebra k (Exponent × Exponent))
  apply (torusCharacters S).injective
  rw [map_mul]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change _ = _ * _
  rw [torusPoint_character, torusPoint_character, torusPoint_character]
  rw [torusMap_monomial, torusMap_monomial, torusMap_monomial, ← map_mul]
  apply congrArg (MonoidAlgebra.of k (Exponent × Exponent))
  change (m, m) = (m, 1) * (1, m)
  simp

private theorem norm_zero_of_cocharacter {k M : Type} [Field k] [AddCommGroup M] [Module k M]
    {J : ParaQuadratic k M} {F : Coefficients k M} (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    {G : SpinSpecification.GroupScheme k} (hG : RepresentsAutomorphisms J G)
    (c : LinearAlgebraicGroups.Specs.CharacterDescent.Cocharacter G) (hc : c.hom.hom ≠ 1) :
    ∃ x : Ground k M, x ≠ 0 ∧ norm F x = 0 := by
  classical
  obtain ⟨a, ha, haNat⟩ := hG
  let A := TorusAlgebra k
  let B := MonoidAlgebra k (Exponent × Exponent)
  let RA := CommAlgCat.of k A
  let RB := CommAlgCat.of k B
  let g : SpinSpecification.SchemePoints G RA := c.hom.hom
  let u : M → A ⊗[k] M := fun x =>
    a RA g (1 ⊗ₜ[k] x)
  let b := MonoidAlgebra.basis Exponent k
  let coord : A ⊗[k] M ≃ₗ[k] Exponent →₀ M := TensorProduct.equivFinsuppOfBasisLeft b
  let v : M → Exponent →₀ M := fun x => coord (u x)
  have hv (x : M) : u x = ∑ m ∈ (v x).support, MonoidAlgebra.of k Exponent m ⊗ₜ[k] v x m := by
    conv_lhs => rw [← coord.symm_apply_apply (u x)]
    exact TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (v x)
  have hNat (S : TestAlgebra k) (f : A →ₐ[k] S) (x : M) :
      pointMap f (u x) = a S (torusPoint S f ≫ c.hom.hom) (1 ⊗ₜ[k] x) := by
    have h := haNat (CommAlgCat.ofHom f) g (1 ⊗ₜ[k] x)
    change pointMap f (u x) =
      a S (torusPoint S f ≫ c.hom.hom) (pointMap f (1 ⊗ₜ[k] x)) at h
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      map_one] using h
  obtain ⟨x, hx⟩ : ∃ x : M, u x ≠ 1 ⊗ₜ[k] x := by
    by_contra! h
    apply hc
    apply (ha RA).1
    rw [map_one (a RA)]
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro r y
    have hp : r ⊗ₜ[k] y = r • (1 ⊗ₜ[k] y : A ⊗[k] M) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    have hh := h y
    change a RA g (1 ⊗ₜ[k] y) = (1 : A) ⊗ₜ[k] y at hh
    change a RA c.hom.hom (r ⊗ₜ[k] y) = r ⊗ₜ[k] y
    conv_lhs => rw [hp, map_smul, hh]
    exact hp.symm
  obtain ⟨n, hn, hw⟩ : ∃ n : Exponent, n ≠ 1 ∧ v x n ≠ 0 := by
    by_contra! h
    have hsingle : v x = Finsupp.single 1 (v x 1) := by
      ext m
      by_cases hm : m = 1
      · subst m; rw [Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne hm]
        exact h m hm
    have hu : u x = 1 ⊗ₜ[k] v x 1 := by
      rw [← coord.symm_apply_apply (u x), show coord (u x) = v x from rfl, hsingle,
        TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      simp [b, MonoidAlgebra.basis]
      rfl
    let f := Bialgebra.counitAlgHom k A
    have hspec := hNat (CommAlgCat.of k k) f x
    rw [torusPoint_counit, MonObj.one_comp, map_one, hu, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one] at hspec
    change 1 ⊗ₜ[k] v x 1 = 1 ⊗ₜ[k] x at hspec
    have hEq : v x 1 = x := by
      simpa only [TensorProduct.lid_tmul, one_smul] using
        congrArg (TensorProduct.lid k M) hspec
    exact hx (hu.trans (congrArg (fun y : M => (1 : A) ⊗ₜ[k] y) hEq))
  let i := torusMap k (MonoidHom.inl Exponent Exponent)
  let j := torusMap k (MonoidHom.inr Exponent Exponent)
  let d := torusMap k ((MonoidHom.id Exponent).prod (MonoidHom.id Exponent))
  let monomB := MonoidAlgebra.of k (Exponent × Exponent)
  have mapped (f : Exponent →* Exponent × Exponent) (y : M) :
      pointMap (torusMap k f) (u y) = ∑ m ∈ (v y).support, monomB (f m) ⊗ₜ[k] v y m := by
    rw [hv, map_sum]
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, torusMap_monomial, monomB]
  have heq : ∑ m ∈ (v x).support, monomB (m,m) ⊗ₜ[k] v x m =
      ∑ m ∈ (v x).support, monomB (1,m) • pointMap i (u (v x m)) := by
    calc
      _ = pointMap d (u x) := (mapped _ x).symm
      _ = a RB (torusPoint RB i ≫ c.hom.hom)
          (a RB (torusPoint RB j ≫ c.hom.hom) (1 ⊗ₜ[k] x)) := by
        rw [hNat RB d x, torusPoint_diagonal, MonObj.mul_comp, map_mul]
        rfl
      _ = _ := by
        rw [← hNat RB j, mapped, map_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [MonoidHom.inr_apply]
        have ht : monomB (1,m) ⊗ₜ[k] v x m =
            monomB (1,m) • ((1 : B) ⊗ₜ[k] v x m) := by
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [ht, map_smul, ← hNat RB i]
  let extract : B →ₗ[k] A := (MonoidAlgebra.basis (Exponent × Exponent) k).constr k
    (fun p => if p.2 = n then MonoidAlgebra.of k Exponent p.1 else 0)
  have hxtr (p : Exponent × Exponent) :
      extract (monomB p) = if p.2 = n then MonoidAlgebra.of k Exponent p.1 else 0 :=
    (MonoidAlgebra.basis (Exponent × Exponent) k).constr_basis k _ p
  let E := extract.rTensor M
  have hdiag (m : Exponent) :
      E (monomB (m,m) ⊗ₜ[k] v x m) =
        if m = n then MonoidAlgebra.of k Exponent m ⊗ₜ[k] v x m else 0 := by
    change extract.rTensor M _ = _
    rw [LinearMap.rTensor_tmul, hxtr]
    by_cases h : m = n <;> simp [h]
  have hsep (m : Exponent) (y : M) :
      E (monomB (1,m) • pointMap i (u y)) = if m = n then u y else 0 := by
    have hmap := mapped (MonoidHom.inl Exponent Exponent) y
    change pointMap i (u y) = _ at hmap
    rw [hmap, Finset.smul_sum, map_sum]
    by_cases hm : m = n
    · rw [if_pos hm, hv]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [MonoidHom.inl_apply, smul_tmul', smul_eq_mul, ← map_mul, Prod.mk_mul_mk,
        one_mul, mul_one, E, LinearMap.rTensor_tmul, hxtr, hm, ↓reduceIte]
    · rw [if_neg hm]
      apply Finset.sum_eq_zero
      intro l _
      simp only [MonoidHom.inl_apply, smul_tmul', smul_eq_mul, ← map_mul, Prod.mk_mul_mk,
        one_mul, mul_one, E, LinearMap.rTensor_tmul, hxtr, hm, ↓reduceIte, zero_tmul]
  have hweight := congrArg E heq
  have hm : n ∈ (v x).support := Finsupp.mem_support_iff.mpr hw
  simp only [map_sum, hdiag, hsep, Finset.sum_ite_eq', hm, ↓reduceIte] at hweight
  let y := (1 : k) ⊗ₜ[k] v x n
  have hy : y ≠ 0 := by
    intro hy
    apply hw
    simpa only [y, TensorProduct.lid_tmul, one_smul, map_zero] using
      congrArg (TensorProduct.lid k M) hy
  refine ⟨y, hy, ?_⟩
  have hf := (ha RA).2
  have hg := hf ▸ Set.mem_range_self (f := a RA) g
  change a RA g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
    ∀ x y, a RA g (J.op A x y) = J.op A (a RA g x) (a RA g y) at hg
  have hNorm := point_preserves_norm hJ hF A (a RA g) hg.1 hg.2 (1 ⊗ₜ[k] v x n)
  change F.norm.eval A (u (v x n)) = F.norm.eval A (1 ⊗ₜ[k] v x n) at hNorm
  have ho : F.norm.eval A (1 ⊗ₜ[k] v x n) = algebraMap k A (norm F y) := by
    change F.norm.eval A (1 ⊗ₜ[k] v x n) = Algebra.ofId k A (norm F y)
    simpa only [y, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using
      F.norm.natural (Algebra.ofId k A) y
  have hpow : n ^ 3 ≠ 1 := by
    intro he
    apply hn
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    have hz := congrArg (fun m : Exponent => Multiplicative.toAdd m.down) he
    change (3 : ℕ) • Multiplicative.toAdd n.down = 0 at hz
    change Multiplicative.toAdd n.down = 0
    rw [nsmul_eq_mul] at hz
    omega
  have hsmul : MonoidAlgebra.of k Exponent n • ((1 : A) ⊗ₜ[k] v x n) =
      MonoidAlgebra.of k Exponent n ⊗ₜ[k] v x n := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [← hweight, ← hsmul, norm_homogeneous hJ hF A, ho, ← map_pow] at hNorm
  have hz := congrArg (fun q : A => q.coeff (n ^ 3)) hNorm
  change ((MonoidAlgebra.single (n ^ 3) 1 : A) * MonoidAlgebra.single 1 (norm F y)).coeff
    (n ^ 3) = (MonoidAlgebra.single (1 : Exponent) (norm F y)).coeff (n ^ 3) at hz
  simpa [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single_apply, hpow.symm] using hz

end SplitCocharacter

section SplitAutomorphisms

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.AutomorphismSequence
open LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum BasedIso AttachedDatum PinnedGroup PinnedIso)
open private basedIso_ext_weight from LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem cartan_preserving_permutation (p : Fin 4 → Fin 4)
    (h : ∀ i j, cartanMatrix (p i) (p j) = cartanMatrix i j) : ∀ i, p i = i := by
  have h12 : ∀ i j, cartanMatrix i j = -2 → i = 1 ∧ j = 2 := by decide
  have ⟨h1, h2⟩ := h12 (p 1) (p 2) (h 1 2)
  have h0' : ∀ j, cartanMatrix 1 j = -1 → j = 0 := by decide
  have h0 : p 0 = 0 := h0' (p 0)
    ((congrArg (fun j => cartanMatrix j (p 0)) h1).symm.trans (h 1 0))
  have h3' : ∀ j, cartanMatrix 2 j = -1 → cartanMatrix j 2 = -1 → j = 3 := by decide
  have h3 : p 3 = 3 := h3' (p 3)
    ((congrArg (fun j => cartanMatrix j (p 3)) h2).symm.trans (h 2 3))
    ((congrArg (cartanMatrix (p 3)) h2).symm.trans (h 3 2))
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem based_automorphisms_trivial {D : BasedRootDatum.{0}} (C : DatumCoordinates D)
    (hRoots : RootLatticeCalculation) (hCoroots : CorootCalculation) (a : Aut D) : a = 1 := by
  classical
  let f : BasedIso D D := a.asIso.hom
  let s (i : Fin 4) := C.roots.symm (simpleIndex i)
  have hs (i : Fin 4) : C.roots (s i) = simpleIndex i := C.roots.apply_symm_apply _
  have hs' (i : Fin 4) : s i ∈ D.base.support := by
    rw [C.simple_eq, hs]
    exact Set.mem_range_self i
  have hperm (i : Fin 4) : ∃ j, f.val.indexEquiv (s i) = s j := by
    have hf : f.val.indexEquiv (s i) ∈ D.base.support := by
      have h := Set.mem_image_of_mem f.val.indexEquiv (hs' i)
      rwa [f.property] at h
    obtain ⟨j, hj⟩ := (C.simple_eq _).mp hf
    exact ⟨j, C.roots.injective (hj.symm.trans (hs j).symm)⟩
  choose p hp using hperm
  have hCartan (i j : Fin 4) :
      D.datum.toLinearMap (D.datum.root (s i)) (D.datum.coroot (s j)) = cartanMatrix i j := by
    rw [C.pair_eq, C.root_eq, C.coroot_eq, hs, hs]
    exact hCoroots.2.2.1 i j
  have hPair (i j : D.I) :
      D.datum.toLinearMap (D.datum.root (f.val.indexEquiv i))
          (D.datum.coroot (f.val.indexEquiv j)) =
        D.datum.toLinearMap (D.datum.root i) (D.datum.coroot j) := by
    have hr := f.val.toHom.root_weightMap_apply D.datum D.datum i
    change f.val.weightEquiv (D.datum.root i) = D.datum.root (f.val.indexEquiv i) at hr
    have hc := f.val.toHom.coroot_coweightMap_apply D.datum D.datum (f.val.indexEquiv j)
    change f.val.coweightEquiv (D.datum.coroot (f.val.indexEquiv j)) =
      D.datum.coroot (f.val.indexEquiv.symm (f.val.indexEquiv j)) at hc
    rw [Equiv.symm_apply_apply] at hc
    rw [← hr, ← hc]
    exact DFunLike.congr_fun
      (f.val.toHom.weight_coweight_transpose_apply D.datum D.datum
        (D.datum.coroot (f.val.indexEquiv j))) _
  have hpCartan (i j : Fin 4) : cartanMatrix (p i) (p j) = cartanMatrix i j := by
    rw [← hCartan, ← hCartan, ← hp, ← hp, hPair]
  have hfix i (hi : i ∈ D.base.support) : f.val.weightEquiv (D.datum.root i) = D.datum.root i := by
    obtain ⟨j, hj⟩ := (C.simple_eq i).mp hi
    have hi' : i = s j := C.roots.injective (hj.symm.trans (hs j).symm)
    subst i
    have he := f.val.toHom.root_weightMap_apply D.datum D.datum (s j)
    change f.val.weightEquiv (D.datum.root (s j)) =
      D.datum.root (f.val.indexEquiv (s j)) at he
    rw [hp j, cartan_preserving_permutation p hpCartan j] at he
    exact he
  have hSpan : Submodule.span ℤ (Set.range D.datum.root) = ⊤ := by
    apply (Submodule.map_injective_of_injective C.characters.injective)
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr C.characters.surjective]
    have hImage : C.characters '' Set.range D.datum.root = Set.range rootCharacter := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨C.roots i, (C.root_eq i).symm⟩
      · rintro ⟨r, rfl⟩
        exact ⟨_, Set.mem_range_self (C.roots.symm r), (C.root_eq (C.roots.symm r)).trans
          (congrArg rootCharacter (C.roots.apply_symm_apply r))⟩
    change Submodule.span ℤ (C.characters '' Set.range D.datum.root) = ⊤
    rw [hImage]
    exact hRoots.2.2.2.2.2.2
  apply Aut.ext
  apply Iso.ext
  apply basedIso_ext_weight
  intro x
  change f.val.weightEquiv x = x
  have hx : x ∈ Submodule.span ℤ (D.datum.root '' (D.base.support : Set D.I)) := by
    rw [D.base.span_int_root_support, hSpan]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact hfix i hi
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, hx]

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private conjugationMap groupSectionsMap groupSectionsMap_locallySurjective
  groupSections_isSheaf descends_locallySurjective hom_ext_of_locallySurjective
  from LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem centerless_of_iso {k : Type} [Field k] {G H : GroupScheme k}
    (e : G ≅ H) (h : IsCenterless G) : IsCenterless H := by
  intro X z hz
  let i : G.X ≅ H.X := (Grp.forget (SchemeOver k)).mapIso e
  letI : IsMonHom i.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  letI : IsMonHom i.inv := inferInstanceAs (IsMonHom e.inv.hom.hom)
  have hz' : z ≫ i.inv = 1 := by
    apply h X
    intro Y f g
    apply (cancel_mono i.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    simpa only [Category.assoc, i.inv_hom_id, Category.comp_id] using hz Y f (g ≫ i.hom)
  apply (cancel_mono i.inv).mp
  rw [MonObj.one_comp]
  exact hz'

private theorem inner_injective {k : Type} [Field k] {G : GroupScheme k}
    (hG : IsCenterless G) (U : SchemeOver k) :
    Function.Injective (fun z : U ⟶ G.X => innerAut z) := by
  intro x y hxy
  have h := (injective_iff_map_eq_one ((conjugationMap G).app (op U)).hom).2 (by
    intro z hz
    apply ULift.ext
    apply hG U
    have hh := (Descent.AutomorphismSequence.innerAut_eq_one_iff z.down).mp hz
    intro V f g
    have hg := (centralizes_iff (𝟙 G) (show U ⟶ G.X from z.down)).1 hh V f g
    simpa only [CategoryTheory.Grp.id_hom_hom, Category.comp_id] using hg.eq)
  exact congrArg ULift.down (h (show (conjugationMap G).app (op U) ⟨x⟩ =
    (conjugationMap G).app (op U) ⟨y⟩ from hxy))

private theorem conjugation_surjective_of_sequence {k : Type} [Field k]
    {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G)
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{1}}
    (E : ExactSequence G Q O) (hG : IsCenterless G.val)
    (hOuter : ∀ U : (SchemeOver k)ᵒᵖ, Subsingleton (O.obj U)) :
    ∀ (U : SchemeOver k) (a : RelativeAut G.val U),
      ∃ g : U ⟶ G.val.X, innerAut g = a := by
  let p := groupSectionsMap Q.projection
  have hp := groupSectionsMap_locallySurjective Q.projection Q.fppf
  have hinj (U : (SchemeOver k)ᵒᵖ) : Function.Injective (p.app U) := by
    intro x y hxy
    apply ULift.ext
    apply inner_injective hG U.unop
    have h := congrArg (E.inner.app U) hxy
    change E.inner.app U ⟨x.down ≫ Q.projection.hom.hom⟩ =
      E.inner.app U ⟨y.down ≫ Q.projection.hom.hom⟩ at h
    simpa only [E.onLift] using h
  let idSections : groupSections G.val ⟶ groupSections G.val := 𝟙 _
  obtain ⟨r, hr⟩ := descends_locallySurjective p idSections hp (groupSections_isSheaf G.val)
    (fun U x y h => congrArg (fun z => idSections.app U z) (hinj U h))
  have hr' : r ≫ p = 𝟙 _ := by
    apply hom_ext_of_locallySurjective p hp (groupSections_isSheaf Q.quotient.val)
    rw [← Category.assoc, hr, show idSections = 𝟙 _ from rfl, Category.id_comp, Category.comp_id]
  intro U a
  letI := hOuter (op U)
  obtain ⟨q, hq⟩ := (E.exact (op U) a).1 (Subsingleton.elim _ _)
  let x := r.app (op U) q
  have hx : p.app (op U) x = q :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hr' (op U)) q
  refine ⟨x.down, ?_⟩
  rw [← E.onLift U x.down]
  change E.inner.app (op U) (p.app (op U) x) = a
  rw [hx]
  exact hq

private theorem split_group_conjugation {k : Type} [Field k] {A : RootGroups.AdditiveLine k}
    (P : PinnedGroup A) (D : BasedRootDatum.{0}) (C : DatumCoordinates D)
    (D₀ : AttachedDatum P.pair) (d : BasedIso D D₀.toBased)
    (hRoots : RootLatticeCalculation) (hCoroots : CorootCalculation)
    (hG : IsCenterless P.pair.G.val) :
    ∀ (U : SchemeOver k) (a : RelativeAut P.pair.G.val U),
      ∃ g : U ⟶ P.pair.G.val.X, innerAut g = a := by
  obtain ⟨D₁, l, Q, E, _, _⟩ := Descent.QuasiSplitInnerForms.automorphismSequences P
  let c := Classification.Pinning.inducedBasedIso (PinnedIso.refl P) D₀ D₁
  let e : D ≅ D₁.toBased := asIso (show D ⟶ D₁.toBased from d ≫ c)
  let i := Aut.autMulEquivOfIso e
  have hD : Subsingleton (Aut D₁.toBased) := by
    refine ⟨fun x y => i.symm.injective ?_⟩
    rw [based_automorphisms_trivial C hRoots hCoroots (i.symm x),
      based_automorphisms_trivial C hRoots hCoroots (i.symm y)]
  letI := hD
  apply conjugation_surjective_of_sequence Q E.toExactSequence hG
  intro U
  change Subsingleton (ULift (LocallyConstant U.unop.left (Aut D₁.toBased)))
  refine ⟨fun x y => ULift.ext ?_⟩
  exact LocallyConstant.ext (fun _ => Subsingleton.elim _ _)

end SplitAutomorphisms

section FixedLaw

open Descent (SemilinearAction)

variable {L V : Type} [Field L] [AddCommGroup V]
variable {k : Type} [Field k] [Module k V]

private def extendEnd (S : Type) [CommRing S] [Algebra k S] :
    S ⊗[k] Module.End k V →ₗ[S] Module.End S (S ⊗[k] V) :=
  (LinearMap.baseChangeHom k S V V).liftBaseChange S

private def extendOperator (b : Module.Basis ι k V) [LinearOrder ι]
    (Q : QuadraticMap k V (Module.End k V)) (S : Type) [CommRing S] [Algebra k S] :
    QuadraticMap S (S ⊗[k] V) (Module.End S (S ⊗[k] V)) :=
  (extendEnd S).compQuadraticMap ((Q.toBilin b).baseChange S).toQuadraticMap

private theorem extendOperator_one_tmul (b : Module.Basis ι k V) [LinearOrder ι]
    (Q : QuadraticMap k V (Module.End k V)) (S : Type) [CommRing S] [Algebra k S] (x : V) :
    extendOperator b Q S (1 ⊗ₜ[k] x) = (Q x).baseChange S := by
  have h : Q.toBilin b x x = Q x :=
    DFunLike.congr_fun (QuadraticMap.toQuadraticMap_toBilin Q b) x
  simp only [extendOperator, LinearMap.compQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.baseChange_tmul, mul_one, h, extendEnd,
    LinearMap.liftBaseChange_one_tmul, LinearMap.baseChangeHom_apply]

private theorem extendOperator_natural (b : Module.Basis ι k V) [LinearOrder ι]
    (Q : QuadraticMap k V (Module.End k V)) {S T : Type} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (x y : S ⊗[k] V) :
    pointMap f (extendOperator b Q S x y) =
      extendOperator b Q T (pointMap f x) (pointMap f y) := by
  let B := Q.toBilin b
  have h (x z y : S ⊗[k] V) :
      pointMap f (extendEnd S (B.baseChange S x z) y) =
        extendEnd T (B.baseChange T (pointMap f x) (pointMap f z)) (pointMap f y) := by
    induction x using TensorProduct.inductionOn with
    | tmul a u =>
      induction z using TensorProduct.inductionOn with
      | tmul b v =>
        induction y using TensorProduct.inductionOn with
        | tmul c w =>
          simp only [extendEnd, LinearMap.BilinMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
            LinearMap.baseChangeHom_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
            smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_mul]
        | add _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
      | add _ _ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | add _ _ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  exact h x x y

private def pointedOperatorOfGround (e : V) (Q : QuadraticMap k V (Module.End k V))
    (hUnit : Q e = 1) : ParaQuadratic k V := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex k V) k V := Module.Free.chooseBasis k V
  let order : LinearOrder (Module.Free.ChooseBasisIndex k V) :=
    IsWellOrder.linearOrder WellOrderingRel
  letI := order
  exact
    { unit := e
      op := fun S _ _ => extendOperator b Q S
      natural := fun f x y => extendOperator_natural b Q f x y
      op_unit := fun S _ _ => by
        change extendOperator b Q S (1 ⊗ₜ[k] e) = _
        rw [extendOperator_one_tmul, hUnit, LinearMap.baseChange_one] }

private theorem pointedOperatorOfGround_tmul (e : V) (Q : QuadraticMap k V (Module.End k V))
    (hUnit : Q e = 1) (S : Type) [CommRing S] [Algebra k S] (x : V) :
    (pointedOperatorOfGround e Q hUnit).op S (1 ⊗ₜ[k] x) = (Q x).baseChange S := by
  letI : LinearOrder (Module.Free.ChooseBasisIndex k V) :=
    IsWellOrder.linearOrder WellOrderingRel
  exact extendOperator_one_tmul (Module.Free.chooseBasis k V) Q S x

variable [Algebra k L] [Module L V] [IsScalarTower k L V]

private def fixedOperators (ρ : SemilinearAction k L V)
    (Q : QuadraticMap L V (Module.End L V))
    (hQ : ∀ σ x y, ρ.act σ (Q x y) = Q (ρ.act σ x) (ρ.act σ y))
    (x : ρ.fixed) : Module.End k ρ.fixed :=
  (((Q x.val).restrictScalars k).comp ρ.fixed.subtype).codRestrict ρ.fixed (fun y σ => by
    change ρ.act σ (Q x.val y.val) = Q x.val y.val
    rw [hQ, x.property σ, y.property σ])

private def fixedQuadratic (ρ : SemilinearAction k L V)
    (Q : QuadraticMap L V (Module.End L V))
    (hQ : ∀ σ x y, ρ.act σ (Q x y) = Q (ρ.act σ x) (ρ.act σ y)) :
    QuadraticMap k ρ.fixed (Module.End k ρ.fixed) := by
  let q := fixedOperators ρ Q hQ
  refine QuadraticMap.ofPolar q ?_ ?_ ?_
  · intro r x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change Q (r • x.val) y.val = (r * r) • Q x.val y.val
    rw [← IsScalarTower.algebraMap_smul L r x.val, QuadraticMap.map_smul,
      LinearMap.smul_apply, ← map_mul, IsScalarTower.algebraMap_smul]
  · intro x y z
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (QuadraticMap.polar Q (x.val + y.val) z.val) w.val =
      (QuadraticMap.polar Q x.val z.val + QuadraticMap.polar Q y.val z.val) w.val
    rw [QuadraticMap.polar_add_left]
  · intro r x y
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change (QuadraticMap.polar Q (r • x.val) y.val) z.val =
      r • (QuadraticMap.polar Q x.val y.val) z.val
    rw [← IsScalarTower.algebraMap_smul L r x.val, QuadraticMap.polar_smul_left,
      LinearMap.smul_apply, IsScalarTower.algebraMap_smul]

/-- Descend an equivariant pointed quadratic law on a finite Galois extension. -/
private theorem fixed_law [FiniteDimensional k L] [IsGalois k L]
    (ρ : SemilinearAction k L V) (e : V) (Q : QuadraticMap L V (Module.End L V))
    (he : ∀ σ, ρ.act σ e = e) (hOne : Q e = 1)
    (hQ : ∀ σ x y, ρ.act σ (Q x y) = Q (ρ.act σ x) (ρ.act σ y)) :
    ∃ J : ParaQuadratic k ρ.fixed,
      ρ.descentEquiv (1 ⊗ₜ[k] J.unit) = e ∧
      ∀ x y, ρ.descentEquiv (J.op L x y) = Q (ρ.descentEquiv x) (ρ.descentEquiv y) := by
  let e₀ : ρ.fixed := ⟨e, he⟩
  let q := fixedQuadratic ρ Q hQ
  have hq : q e₀ = 1 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change Q e y.val = y.val
    rw [hOne, Module.End.one_apply]
  let J := pointedOperatorOfGround e₀ q hq
  let C := ρ.descentEquiv
  have hC (r : L) (x : ρ.fixed) : C (r ⊗ₜ[k] x) = r • x.val := rfl
  refine ⟨J, ?_, ?_⟩
  · change C (1 ⊗ₜ[k] e₀) = e
    rw [hC, one_smul]
  · have hOp : C.conj.toLinearMap.compQuadraticMap (J.op L) = Q.comp C.toLinearMap := by
      apply baseChange_ext
      intro x
      apply (LinearMap.ext fun y => ?_)
      obtain ⟨z, rfl⟩ := C.surjective y
      change C ((J.op L (1 ⊗ₜ[k] x)) (C.symm (C z))) = Q (C (1 ⊗ₜ[k] x)) (C z)
      rw [C.symm_apply_apply, pointedOperatorOfGround_tmul, hC, one_smul]
      induction z using TensorProduct.inductionOn with
      | tmul r y =>
        rw [LinearMap.baseChange_tmul, hC, hC, map_smul]
        rfl
      | add y z hy hz => simp only [map_add, hy, hz]
    intro x y
    have h := congrArg (fun f : QuadraticMap L (L ⊗[k] ρ.fixed) (Module.End L V) =>
      f x (C y)) hOp
    change C (J.op L x (C.symm (C y))) = Q (C x) (C y) at h
    rw [C.symm_apply_apply] at h
    exact h

end FixedLaw

section FiniteForms

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.AutomorphismSequence
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest fieldMap transportedAut)
open LinearAlgebraicGroups.Descent
open LinearAlgebraicGroups.Descent.Forms (spectrumIso)
open private spectrumIsoEquiv from LinearAlgebraicGroups.Descent.Forms
open private schemeIsoEquiv from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private innerAut_mul restrict_innerAut conjugationMap
  from LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false

private theorem finite_trivialization {k S : Type} [Field k] [Field S] [Algebra k S]
    [IsSepClosure k S] (G H : AffineAlgebraicGroup k)
    (i : (groupChange k S).obj G.val ≅ (groupChange k S).obj H.val) :
    ∃ L : FiniteGaloisIntermediateField k S,
      Nonempty (relativePoints G.val (fieldTest k L) ≅ relativePoints H.val (fieldTest k L)) := by
  obtain ⟨A, hA, jA, t, _⟩ := Forms.schemeComparison (K := S) G
  obtain ⟨B, hB, jB, _⟩ := Forms.schemeComparison (K := S) H
  let iA := t A ≪≫ (groupChange k S).mapIso jA
  let iB := t B ≪≫ (groupChange k S).mapIso jB
  let j := (spectrumIsoEquiv (extendedHopf S A) (extendedHopf S B)).symm
    (iA ≪≫ i ≪≫ iB.symm)
  obtain ⟨L, jL, _, _⟩ := Forms.finiteLevelIsomorphisms A B hA hB ⊥ j
  obtain ⟨_, _, _, tL, _⟩ := Forms.schemeComparison (K := L) G
  let iL : (groupChange k L).obj G.val ≅ (groupChange k L).obj H.val :=
    (tL A ≪≫ (groupChange k L).mapIso jA).symm ≪≫ spectrumIso jL ≪≫ tL B ≪≫
      (groupChange k L).mapIso jB
  exact ⟨L, ⟨schemeIsoEquiv L G.val H.val iL⟩⟩

private theorem displacement {k L : Type} [Field k] [Field L] [Algebra k L]
    {G H : GroupScheme k} (hG : IsCenterless G)
    (hInner : ∀ a : RelativeAut G (fieldTest k L),
      ∃ g : fieldTest k L ⟶ G.X, innerAut g = a)
    (i : relativePoints G (fieldTest k L) ≅ relativePoints H (fieldTest k L)) :
    ∃ c : Gal(L/k) → (fieldTest k L ⟶ G.X),
      (∀ σ, innerAut (c σ) = transportedAut k L i σ) ∧ c 1 = 1 ∧
        ∀ σ τ, c (σ * τ) = c σ * (fieldMap k L σ ≫ c τ) := by
  classical
  choose c hc using fun σ : Gal(L/k) => hInner (transportedAut k L i σ)
  refine ⟨c, hc, ?_, ?_⟩
  · apply inner_injective hG (fieldTest k L)
    change innerAut (c 1) = innerAut (1 : fieldTest k L ⟶ G.X)
    have hOne : innerAut (1 : fieldTest k L ⟶ G.X) = 1 :=
      map_one ((conjugationMap G).app (op (fieldTest k L))).hom
    rw [hOne]
    rw [hc, transportedAut, RelativeFormComparison.fieldMap_one]
    have hres : restrictIso (𝟙 (fieldTest k L)) i = i := by
      apply Iso.ext
      apply NatTrans.ext
      funext U
      apply GrpCat.ext
      intro x
      let W := (Over.map (𝟙 (fieldTest k L))).obj U.unop
      let α : W ⟶ U.unop := (Over.mapId _).hom.app U.unop
      let x' : U.unop.left ⟶ G.X := x
      have hn := NatTrans.naturality_apply i.hom α.op x'
      change i.hom.app (op W) (𝟙 U.unop.left ≫ x') =
        𝟙 U.unop.left ≫ i.hom.app U x' at hn
      have hx : 𝟙 U.unop.left ≫ x' = x' := Category.id_comp x'
      rw [hx] at hn
      exact hn.trans (Category.id_comp (show U.unop.left ⟶ H.X from i.hom.app U x'))
    rw [hres]
    apply Aut.ext
    apply Iso.ext
    exact i.hom_inv_id
  · intro σ τ
    apply inner_injective hG (fieldTest k L)
    change innerAut (c (σ * τ)) = innerAut (c σ * (fieldMap k L σ ≫ c τ))
    rw [innerAut_mul, ← restrict_innerAut, hc (σ * τ), hc σ, hc τ]
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    let Uσ := (Over.map (fieldMap k L σ)).obj U.unop
    let Uστ := (Over.map (fieldMap k L τ)).obj Uσ
    change i.inv.app U (i.hom.app (op ((Over.map (fieldMap k L (σ * τ))).obj U.unop)) x) =
      i.inv.app U (i.hom.app (op Uσ) (i.inv.app (op Uσ) (i.hom.app (op Uστ) x)))
    have hcancel := (i.app (op Uσ)).groupIsoToMulEquiv.apply_symm_apply (i.hom.app (op Uστ) x)
    change i.hom.app (op Uσ) (i.inv.app (op Uσ) (i.hom.app (op Uστ) x)) =
      i.hom.app (op Uστ) x at hcancel
    rw [hcancel]
    let W := (Over.map (fieldMap k L (σ * τ))).obj U.unop
    let α : W ⟶ Uστ := Over.homMk (𝟙 U.unop.left) (by
      change 𝟙 U.unop.left ≫ ((U.unop.hom ≫ fieldMap k L σ) ≫ fieldMap k L τ) =
        U.unop.hom ≫ fieldMap k L (σ * τ)
      rw [Category.id_comp, Category.assoc, RelativeFormComparison.fieldMap_mul])
    let x' : U.unop.left ⟶ G.X := x
    have hn := NatTrans.naturality_apply i.hom α.op x'
    change i.hom.app (op W) (𝟙 U.unop.left ≫ x') =
      𝟙 U.unop.left ≫ i.hom.app (op Uστ) x' at hn
    have hh : i.hom.app (op W) x' = i.hom.app (op Uστ) x' := by
      have hx : 𝟙 U.unop.left ≫ x' = x' := Category.id_comp x'
      rw [hx] at hn
      exact hn.trans (Category.id_comp (show U.unop.left ⟶ H.X from i.hom.app (op Uστ) x'))
    exact congrArg (fun y : U.unop.left ⟶ H.X => i.inv.app U y) hh

end FiniteForms

section TwistedLaw

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest fieldMap)
open LinearAlgebraicGroups.Descent (SemilinearAction)

set_option backward.isDefEq.respectTransparency false

private def semilinearTwist {k L M : Type} [Field k] [Field L] [Algebra k L]
    [AddCommGroup M] [Module k M] {G : GroupScheme k}
    (a : ∀ S : CommAlgCat k, SpinSpecification.SchemePoints G S →* (S ⊗[k] M ≃ₗ[S] S ⊗[k] M))
    (hNat : ∀ {S T : CommAlgCat k} (f : S ⟶ T) (g : SpinSpecification.SchemePoints G S) (x : S ⊗[k] M),
      pointMap f.hom (a S g x) = a T ((algSpec (CommRingCat.of k)).map f.op ≫ g) (pointMap f.hom x))
    (c : Gal(L/k) → (fieldTest k L ⟶ G.X)) (hc : c 1 = 1)
    (hMul : ∀ σ τ, c (σ * τ) = c σ * (fieldMap k L σ ≫ c τ)) :
    SemilinearAction k L (L ⊗[k] M) := by
  let S := CommAlgCat.of k L
  let s := SemilinearAction.scalarExtension (k := k) (K := L) M
  have hPt (σ : Gal(L/k)) (x : L ⊗[k] M) : pointMap σ.toAlgHom x = s.act σ x := rfl
  have hAct (σ : Gal(L/k)) (g : SpinSpecification.SchemePoints G S) (x : L ⊗[k] M) :
      s.act σ (a S g x) = a S (fieldMap k L σ ≫ g) (s.act σ x) := by
    rw [← hPt, ← hPt]
    exact hNat (CommAlgCat.ofHom σ.toAlgHom) g x
  exact
    { act := fun σ => (s.act σ).trans (a S (c σ)).toAddEquiv
      one_act := fun x => by
        change a S (c 1) (s.act 1 x) = x
        rw [hc, s.one_act, map_one]
        rfl
      mul_act := fun σ τ x => by
        change a S (c (σ * τ)) (s.act (σ * τ) x) = a S (c σ) (s.act σ (a S (c τ) (s.act τ x)))
        rw [hMul, s.mul_act, hAct, map_mul]
        rfl
      map_smul := fun σ r x => by
        change a S (c σ) (s.act σ (r • x)) = σ r • a S (c σ) (s.act σ x)
        rw [s.map_smul, map_smul] }

private theorem twisted_law {k L M : Type} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] [AddCommGroup M] [Module k M]
    {J : ParaQuadratic k M} {G : GroupScheme k}
    (a : ∀ S : CommAlgCat k, SpinSpecification.SchemePoints G S →* (S ⊗[k] M ≃ₗ[S] S ⊗[k] M))
    (hRange : ∀ S, Set.range (a S) =
      {g | g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
        ∀ x y, g (J.op S x y) = J.op S (g x) (g y)})
    (hNat : ∀ {S T : CommAlgCat k} (f : S ⟶ T) (g : SpinSpecification.SchemePoints G S) (x : S ⊗[k] M),
      pointMap f.hom (a S g x) = a T ((algSpec (CommRingCat.of k)).map f.op ≫ g) (pointMap f.hom x))
    (c : Gal(L/k) → (fieldTest k L ⟶ G.X)) (hc : c 1 = 1)
    (hMul : ∀ σ τ, c (σ * τ) = c σ * (fieldMap k L σ ≫ c τ))
    (chart : SplitChart J L) :
    let ρ := semilinearTwist a hNat c hc hMul
    ∃ J' : ParaQuadratic k ρ.fixed, IsAlbert J' ∧
      ρ.descentEquiv (1 ⊗ₜ[k] J'.unit) = 1 ⊗ₜ[k] J.unit ∧
      ∀ x y, ρ.descentEquiv (J'.op L x y) = J.op L (ρ.descentEquiv x) (ρ.descentEquiv y) := by
  let ρ := semilinearTwist a hNat c hc hMul
  let S := CommAlgCat.of k L
  have hAut (σ : Gal(L/k)) :
      a S (c σ) (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
        ∀ x y : L ⊗[k] M, a S (c σ) (J.op L x y) = J.op L (a S (c σ) x) (a S (c σ) y) := by
    have h : a S (c σ) ∈ Set.range (a S) := Set.mem_range_self _
    rw [hRange S] at h
    exact h
  have hUnit (σ : Gal(L/k)) : ρ.act σ (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit := by
    change a S (c σ) (pointMap σ.toAlgHom (1 ⊗ₜ[k] J.unit)) = _
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, (hAut σ).1]
  have hOp (σ : Gal(L/k)) (x y : L ⊗[k] M) :
      ρ.act σ (J.op L x y) = J.op L (ρ.act σ x) (ρ.act σ y) := by
    change a S (c σ) (pointMap σ.toAlgHom (J.op L x y)) =
      J.op L (a S (c σ) (pointMap σ.toAlgHom x)) (a S (c σ) (pointMap σ.toAlgHom y))
    rw [J.natural, (hAut σ).2]
  obtain ⟨J', hU, hQ⟩ := fixed_law ρ (1 ⊗ₜ[k] J.unit) (J.op L) hUnit (J.op_unit L) hOp
  refine ⟨J', ?_, hU, hQ⟩
  apply (albert_iff_split_octonion_after_cover J').mpr
  exact ⟨L, inferInstance, inferInstance, inferInstance, ρ.descentEquiv.trans chart.coordinates,
    (congrArg chart.coordinates hU).trans chart.unit,
    fun x y => (congrArg chart.coordinates (hQ x y)).trans (chart.op _ _)⟩

end TwistedLaw

section IteratedComparison

variable {k L V W : Type} [Field k] [Field L] [Algebra k L]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def extendComparison {S : Type} [CommRing S] [Algebra k S] (f : L →ₐ[k] S)
    (C : L ⊗[k] W ≃ₗ[L] L ⊗[k] V) : S ⊗[k] W ≃ₗ[S] S ⊗[k] V := by
  letI : Algebra L S := f.toRingHom.toAlgebra
  letI : IsScalarTower k L S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let DW := AlgebraTensorModule.cancelBaseChange k L S S W
  let DV := AlgebraTensorModule.cancelBaseChange k L S S V
  exact DW.symm.trans ((C.baseChange L S _ _).trans DV)

private theorem extendComparison_natural_field {S : Type} [CommRing S] [Algebra k S]
    (f : L →ₐ[k] S) (C : L ⊗[k] W ≃ₗ[L] L ⊗[k] V) (x : L ⊗[k] W) :
    extendComparison f C (pointMap f x) = pointMap f (C x) := by
  letI : Algebra L S := f.toRingHom.toAlgebra
  letI : IsScalarTower k L S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hCancel {Z : Type} [AddCommGroup Z] [Module k Z] (z : L ⊗[k] Z) :
      AlgebraTensorModule.cancelBaseChange k L S S Z (1 ⊗ₜ[L] z) = pointMap f z := by
    induction z using TensorProduct.inductionOn with
    | tmul a y =>
      simp only [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, Algebra.smul_def, mul_one]
      rfl
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  rw [← hCancel x, ← hCancel (C x)]
  change AlgebraTensorModule.cancelBaseChange k L S S V
    ((C.baseChange L S _ _) ((AlgebraTensorModule.cancelBaseChange k L S S W).symm
      (AlgebraTensorModule.cancelBaseChange k L S S W (1 ⊗ₜ[L] x)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

private theorem extendComparison_tmul {S : Type} [CommRing S] [Algebra k S]
    (f : L →ₐ[k] S) (C : L ⊗[k] W ≃ₗ[L] L ⊗[k] V) (a : S) (w : W) :
    extendComparison f C (a ⊗ₜ[k] w) = a • pointMap f (C (1 ⊗ₜ[k] w)) := by
  have h := extendComparison_natural_field f C (1 ⊗ₜ[k] w)
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at h
  rw [← h, ← map_smul, smul_tmul', smul_eq_mul, mul_one]

private theorem pointMap_compose {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    [Algebra k R] [Algebra k S] [Algebra k T] (g : S →ₐ[k] T) (f : R →ₐ[k] S)
    (x : R ⊗[k] V) : pointMap g (pointMap f x) = pointMap (g.comp f) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem extendComparison_natural {S T : Type} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : L →ₐ[k] S) (g : S →ₐ[k] T)
    (C : L ⊗[k] W ≃ₗ[L] L ⊗[k] V) (x : S ⊗[k] W) :
    pointMap g (extendComparison f C x) = extendComparison (g.comp f) C (pointMap g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    rw [extendComparison_tmul f, pointMap_smul, pointMap_compose]
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, extendComparison_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem extendComparison_preserves {S : Type} [CommRing S] [Algebra k S]
    (f : L →ₐ[k] S) (C : L ⊗[k] W ≃ₗ[L] L ⊗[k] V)
    (J : ParaQuadratic k V) (K : ParaQuadratic k W)
    (hUnit : C (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] J.unit)
    (hOp : ∀ x y, C (K.op L x y) = J.op L (C x) (C y)) :
    let E := extendComparison f C
    E (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] J.unit ∧
      ∀ x y, E (K.op S x y) = J.op S (E x) (E y) := by
  let E := extendComparison f C
  refine ⟨?_, ?_⟩
  · rw [extendComparison_tmul, hUnit, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      map_one, one_smul]
  · have h : E.conj.toLinearMap.compQuadraticMap (K.op S) = (J.op S).comp E.toLinearMap := by
      apply baseChange_ext (R := k) (A := S) (M₂ := W) (N₁ := Module.End S (S ⊗[k] V))
      intro x
      apply LinearMap.ext
      intro y
      obtain ⟨z, rfl⟩ := E.surjective y
      change E (K.op S (1 ⊗ₜ[k] x) (E.symm (E z))) = J.op S (E (1 ⊗ₜ[k] x)) (E z)
      rw [E.symm_apply_apply]
      induction z using TensorProduct.inductionOn with
      | tmul a w =>
        have e (w : W) : pointMap f (1 ⊗ₜ[k] w) = 1 ⊗ₜ[k] w := by
          rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
        have ha : (a ⊗ₜ[k] w : S ⊗[k] W) = a • ((1 : S) ⊗ₜ[k] w) := by
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [ha, map_smul, map_smul, map_smul, ← e, ← e, ← K.natural,
          extendComparison_natural_field, extendComparison_natural_field,
          extendComparison_natural_field, hOp, J.natural]
        rw [map_smul]
      | add z w hz hw => simp only [map_add, hz, hw]
    intro x y
    have hh := congrArg (fun Q : QuadraticMap S (S ⊗[k] W) (Module.End S (S ⊗[k] V)) =>
      Q x (E y)) h
    change E (K.op S x (E.symm (E y))) = J.op S (E x) (E y) at hh
    rwa [E.symm_apply_apply] at hh

end IteratedComparison

section PointComparisons

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs

set_option backward.isDefEq.respectTransparency false

private def changePointGroup {k : Type} [Field k] {G H : GroupScheme k} (e : G ≅ H)
    (S : CommAlgCat k) :
    SpinSpecification.SchemePoints G S ≃* SpinSpecification.SchemePoints H S :=
  (((groupPointsFunctor k).mapIso e).app S).groupIsoToMulEquiv

private theorem represents_of_iso {k M : Type} [Field k] [AddCommGroup M] [Module k M]
    {J : ParaQuadratic k M} {G H : GroupScheme k} (h : RepresentsAutomorphisms J G)
    (e : H ≅ G) : RepresentsAutomorphisms J H := by
  obtain ⟨a, ha, hNat⟩ := h
  let b (S : CommAlgCat k) := (a S).comp (changePointGroup e S).toMonoidHom
  refine ⟨b, fun S => ⟨(ha S).1.comp (changePointGroup e S).injective, ?_⟩, ?_⟩
  · rw [show Set.range (b S) = Set.range (a S) from
      (changePointGroup e S).surjective.range_comp (a S), (ha S).2]
  · intro S T f g x
    have h := hNat f (changePointGroup e S g) x
    change pointMap f.hom (a S (g ≫ e.hom.hom.hom) x) =
      a T ((algSpec (CommRingCat.of k)).map f.op ≫ (g ≫ e.hom.hom.hom)) (pointMap f.hom x) at h
    change pointMap f.hom (a S (g ≫ e.hom.hom.hom) x) =
      a T (((algSpec (CommRingCat.of k)).map f.op ≫ g) ≫ e.hom.hom.hom) (pointMap f.hom x)
    rwa [Category.assoc]

variable {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable {G H : GroupScheme k}
variable (J : ParaQuadratic k V) (K : ParaQuadratic k W) (S : CommAlgCat k)
variable (a : SpinSpecification.SchemePoints G S →* (S ⊗[k] V ≃ₗ[S] S ⊗[k] V))
variable (b : SpinSpecification.SchemePoints H S →* (S ⊗[k] W ≃ₗ[S] S ⊗[k] W))

private theorem actions_conjugated
    (ha : Function.Injective a ∧ Set.range a =
      {g | g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
        ∀ x y, g (J.op S x y) = J.op S (g x) (g y)})
    (hb : Function.Injective b ∧ Set.range b =
      {g | g (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] K.unit ∧
        ∀ x y, g (K.op S x y) = K.op S (g x) (g y)})
    (E : S ⊗[k] W ≃ₗ[S] S ⊗[k] V)
    (hUnit : E (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] J.unit)
    (hOp : ∀ x y, E (K.op S x y) = J.op S (E x) (E y)) :
    ∃ φ : SpinSpecification.SchemePoints G S ≃* SpinSpecification.SchemePoints H S,
      ∀ g x, E (b (φ g) x) = a g (E x) := by
  classical
  let Cg (g : SpinSpecification.SchemePoints G S) := (E.trans (a g)).trans E.symm
  have exists_image (g : SpinSpecification.SchemePoints G S) : ∃ h, b h = Cg g := by
    have hg : a g ∈ Set.range a := Set.mem_range_self g
    rw [ha.2] at hg
    change a g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
      ∀ x y, a g (J.op S x y) = J.op S (a g x) (a g y) at hg
    change Cg g ∈ Set.range b
    rw [hb.2]
    constructor
    · apply E.injective
      change E (E.symm (a g (E (1 ⊗ₜ[k] K.unit)))) = E (1 ⊗ₜ[k] K.unit)
      rw [E.apply_symm_apply, hUnit, hg.1]
    · intro x y
      apply E.injective
      change E (E.symm (a g (E (K.op S x y)))) = E (K.op S (Cg g x) (Cg g y))
      rw [E.apply_symm_apply, hOp, hg.2, hOp]
      simp only [Cg, LinearEquiv.trans_apply, E.apply_symm_apply]
  choose φ hφ using exists_image
  have hInter (g : SpinSpecification.SchemePoints G S) (x : S ⊗[k] W) :
      E (b (φ g) x) = a g (E x) := by
    rw [hφ]
    exact E.apply_symm_apply _
  let f : SpinSpecification.SchemePoints G S →* SpinSpecification.SchemePoints H S :=
    { toFun := φ
      map_one' := by
        apply hb.1
        rw [map_one]
        ext x
        apply E.injective
        rw [hInter, map_one]
        rfl
      map_mul' := by
        intro g h
        apply hb.1
        rw [map_mul]
        apply LinearEquiv.ext
        intro x
        apply E.injective
        change E (b (φ (g * h)) x) = E (b (φ g) (b (φ h) x))
        rw [hInter, hInter, hInter, map_mul]
        rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro g h hh
      apply ha.1
      apply LinearEquiv.ext
      intro y
      obtain ⟨x, rfl⟩ := E.surjective y
      change φ g = φ h at hh
      rw [← hInter, hh, hInter]
    · intro h
      have hh : b h ∈ Set.range b := Set.mem_range_self h
      rw [hb.2] at hh
      change b h (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] K.unit ∧
        ∀ x y, b h (K.op S x y) = K.op S (b h x) (b h y) at hh
      let g := (E.symm.trans (b h)).trans E
      have hg : g ∈ Set.range a := by
        rw [ha.2]
        constructor
        · change E (b h (E.symm (1 ⊗ₜ[k] J.unit))) = _
          rw [← hUnit, E.symm_apply_apply, hh.1]
        · intro x y
          obtain ⟨x, rfl⟩ := E.surjective x
          obtain ⟨y, rfl⟩ := E.surjective y
          change E (b h (E.symm (J.op S (E x) (E y)))) =
            J.op S (E (b h (E.symm (E x)))) (E (b h (E.symm (E y))))
          rw [← hOp, E.symm_apply_apply, E.symm_apply_apply, E.symm_apply_apply, hh.2, hOp]
      obtain ⟨x, hx⟩ := hg
      refine ⟨x, hb.1 ?_⟩
      apply LinearEquiv.ext
      intro y
      apply E.injective
      change E (b (φ x) y) = E (b h y)
      rw [hInter, hx]
      change E (b h (E.symm (E y))) = E (b h y)
      rw [E.symm_apply_apply]
  exact ⟨MulEquiv.ofBijective f hf, hInter⟩

end PointComparisons

section RelativePoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.AutomorphismSequence (relativePoints restrictIso)
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest fieldMap)
open private schemeIsoEquiv from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private relativeSectionEquiv from LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false

private def fieldPoint {k L : Type} [Field k] [Field L] [Algebra k L] (S : TestAlgebra k)
    (f : L →ₐ[k] S) : (testSpec k).obj (op S) ⟶ fieldTest k L :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private def scalarPointMap {k L : Type} [Field k] [Field L] [Algebra k L] (S : TestAlgebra L) :
    L →ₐ[k] (restrictTestAlgebra k L).obj S :=
  ⟨algebraMap L S, fun _ => rfl⟩

private theorem scalar_test_surjective {k L : Type} [Field k] [Field L] [Algebra k L] :
    Function.Surjective (fun R : TestAlgebra L => (⟨(restrictTestAlgebra k L).obj R,
      scalarPointMap R⟩ : Σ R : TestAlgebra k, L →ₐ[k] R)) := by
  rintro ⟨@⟨S, rS, aS⟩, f⟩
  rcases f with ⟨f, hf⟩
  change L →+* S at f
  let R : TestAlgebra L := @CommAlgCat.of L _ S rS f.toAlgebra
  have he : (f.comp (algebraMap k L)).toAlgebra = aS :=
    Algebra.algebra_ext _ _ hf
  refine ⟨R, ?_⟩
  subst aS
  rfl

private theorem affine_scalar_extension {k L : Type} [Field k] [Field L] [Algebra k L]
    (G : GroupScheme k) (h : IsAffine G.X.left) :
    IsAffine ((groupBaseChange k L).obj G).X.left := by
  letI := h
  have : IsAffineHom G.X.hom := inferInstance
  change IsAffine (pullback G.X.hom (fieldSpecMap k L))
  exact isAffine_of_isAffineHom (pullback.snd G.X.hom (fieldSpecMap k L))

private theorem relative_equivalence_from_points {k L : Type} [Field k] [Field L] [Algebra k L]
    {G H : GroupScheme k} (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (φ : ∀ (R : TestAlgebra k), (L →ₐ[k] R) →
      SpinSpecification.SchemePoints G R ≃* SpinSpecification.SchemePoints H R)
    (hφ : ∀ {R S : TestAlgebra k} (b : R ⟶ S) (f : L →ₐ[k] R)
      (x : SpinSpecification.SchemePoints G R),
      mapPoints b (φ R f x) = φ S (b.hom.comp f) (mapPoints b x)) :
    ∃ i : relativePoints G (fieldTest k L) ≅ relativePoints H (fieldTest k L),
      ∀ (R : TestAlgebra k) (f : L →ₐ[k] R) (x : SpinSpecification.SchemePoints G R),
        i.hom.app (op (Over.mk (fieldPoint R f))) x = φ R f x := by
  let G₁ := (groupBaseChange k L).obj G
  let H₁ := (groupBaseChange k L).obj H
  let ψ (R : TestAlgebra L) :=
    (baseChangePointGroupEquiv L G R).trans
      ((φ _ (scalarPointMap R)).trans (baseChangePointGroupEquiv L H R).symm)
  let n : (groupPointsFunctor L).obj G₁ ≅ (groupPointsFunctor L).obj H₁ :=
    NatIso.ofComponents (fun R => (ψ R).toGrpIso) (by
      intro R S b
      apply GrpCat.ext
      intro x
      change SpinSpecification.SchemePoints G₁ R at x
      change ψ S (mapPoints b x) = mapPoints b (ψ R x)
      apply (baseChangePointGroupEquiv L H S).injective
      change baseChangePoint k L H.X S (ψ S (mapPoints b x)) =
        baseChangePoint k L H.X S (mapPoints b (ψ R x))
      rw [baseChangePointsNaturality k L H.X]
      have hmap : ((restrictTestAlgebra k L).map b).hom.comp (scalarPointMap R) = scalarPointMap S :=
        AlgHom.ext (fun t => b.hom.commutes t)
      have hp (R : TestAlgebra L) (p : SpinSpecification.SchemePoints G₁ R) :
          baseChangePoint k L H.X R (ψ R p) =
            φ _ (scalarPointMap R) (baseChangePoint k L G.X R p) :=
        (baseChangePointGroupEquiv L H R).apply_symm_apply _
      rw [hp S (mapPoints b x), hp R x, hφ, hmap]
      exact congrArg (φ _ (scalarPointMap S)) (baseChangePointsNaturality k L G.X b x))
  let f := (groupHomEquiv G₁ H₁ (affine_scalar_extension G hG)).symm n.hom
  let g := (groupHomEquiv H₁ G₁ (affine_scalar_extension H hH)).symm n.inv
  have hf : (groupPointsFunctor L).map f = n.hom :=
    (groupHomEquiv G₁ H₁ (affine_scalar_extension G hG)).apply_symm_apply _
  have hg : (groupPointsFunctor L).map g = n.inv :=
    (groupHomEquiv H₁ G₁ (affine_scalar_extension H hH)).apply_symm_apply _
  let j : G₁ ≅ H₁ :=
    { hom := f
      inv := g
      hom_inv_id := by
        apply (groupHomComparison L _ _ (affine_scalar_extension G hG)).1
        change (groupPointsFunctor L).map (f ≫ g) = (groupPointsFunctor L).map (𝟙 G₁)
        rw [Functor.map_comp, hf, hg, n.hom_inv_id]
        exact ((groupPointsFunctor L).map_id G₁).symm
      inv_hom_id := by
        apply (groupHomComparison L _ _ (affine_scalar_extension H hH)).1
        change (groupPointsFunctor L).map (g ≫ f) = (groupPointsFunctor L).map (𝟙 H₁)
        rw [Functor.map_comp, hf, hg, n.inv_hom_id]
        exact ((groupPointsFunctor L).map_id H₁).symm }
  let i := schemeIsoEquiv L G H j
  refine ⟨i, ?_⟩
  have eval_restricted (R : TestAlgebra L)
      (x : SpinSpecification.SchemePoints G ((restrictTestAlgebra k L).obj R)) :
      i.hom.app (op (Over.mk (fieldPoint _ (scalarPointMap R)))) x =
        φ _ (scalarPointMap R) x := by
    let p := (baseChangePointGroupEquiv L G R).symm x
    have hp : baseChangePoint k L G.X R p = x :=
      (baseChangePointGroupEquiv L G R).apply_symm_apply x
    let U : Over (fieldTest k L) :=
      Over.mk (fieldPoint ((restrictTestAlgebra k L).obj R) (scalarPointMap R))
    have hp' : (relativeSectionEquiv U G.X).symm x = p :=
      (Equiv.symm_apply_eq _).mpr hp.symm
    change relativeSectionEquiv U H.X ((relativeSectionEquiv U G.X).symm x ≫ j.hom.hom.hom) =
      φ _ (scalarPointMap R) x
    rw [hp']
    let q : SpinSpecification.SchemePoints H₁ R := p ≫ j.hom.hom.hom
    have hq : q = ψ R p :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hf R) p
    change baseChangePoint k L H.X R q = φ _ (scalarPointMap R) x
    rw [hq]
    have ht : baseChangePoint k L H.X R (ψ R p) =
        φ _ (scalarPointMap R) (baseChangePoint k L G.X R p) :=
      (baseChangePointGroupEquiv L H R).apply_symm_apply _
    rw [ht, hp]
  intro R a
  obtain ⟨S, hS⟩ := scalar_test_surjective (⟨R, a⟩ : Σ R : TestAlgebra k, L →ₐ[k] R)
  let P (p : Σ R : TestAlgebra k, L →ₐ[k] R) :=
    ∀ x : SpinSpecification.SchemePoints G p.1,
      i.hom.app (op (Over.mk (fieldPoint p.1 p.2))) x = φ p.1 p.2 x
  change P ⟨R, a⟩
  exact Eq.mp (congrArg P hS) (eval_restricted S)

end RelativePoints

section DescentComparison

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.AutomorphismSequence
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest fieldMap transportedAut)
open LinearAlgebraicGroups.Descent
open private relativeHom_ext_affine from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private restrict_trans from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private descend_standard_iso from LinearAlgebraicGroups.Descent.Forms

set_option backward.isDefEq.respectTransparency false

private theorem same_displacement_descends {k L : Type} [Field k] [Field L] [Algebra k L]
    [IsGalois k L] {G : GroupScheme k} (H K : AffineAlgebraicGroup k)
    (i : relativePoints G (fieldTest k L) ≅ relativePoints H.val (fieldTest k L))
    (j : relativePoints G (fieldTest k L) ≅ relativePoints K.val (fieldTest k L))
    (h : ∀ σ, transportedAut k L i σ = transportedAut k L j σ) :
    Nonempty (H.val ≅ K.val) := by
  let d := i.symm ≪≫ j
  have hd (σ : Gal(L/k)) : restrictIso (fieldMap k L σ) d = d := by
    have hi : restrictIso (fieldMap k L σ) i = (transportedAut k L i σ).asIso ≪≫ i := by
      change _ = (restrictIso (fieldMap k L σ) i ≪≫ i.symm) ≪≫ i
      simp
    have hj : restrictIso (fieldMap k L σ) j = (transportedAut k L i σ).asIso ≪≫ j := by
      rw [h σ]
      change _ = (restrictIso (fieldMap k L σ) j ≪≫ j.symm) ≪≫ j
      simp
    have hinv : restrictIso (fieldMap k L σ) i.symm = (restrictIso (fieldMap k L σ) i).symm := by
      apply Iso.ext
      rfl
    rw [show d = i.symm ≪≫ j from rfl, restrict_trans, hinv, hi, hj]
    simp
  obtain ⟨A, _, A₀, t, _, _, ht, _⟩ := Forms.schemeComparison (K := L) H
  obtain ⟨B, _, B₀, _⟩ := Forms.schemeComparison (K := L) K
  obtain ⟨E, _, hE⟩ := RelativeFormComparison.hopfIsomorphismComparison t ht A₀ B₀
  let e := E.symm d
  have he : E e = d := E.apply_symm_apply d
  obtain ⟨f, _⟩ := descend_standard_iso e (by
    intro σ x
    exact ((hE σ e e).mpr (by rw [he, hd σ])) x)
  exact ⟨A₀.symm ≪≫ Forms.spectrumIso f ≪≫ B₀⟩

private theorem relative_law_comparison {k L V W : Type} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {G H : GroupScheme k} (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (J : ParaQuadratic k V) (K : ParaQuadratic k W)
    (a : ∀ S : TestAlgebra k, SpinSpecification.SchemePoints G S →* (S ⊗[k] V ≃ₗ[S] S ⊗[k] V))
    (b : ∀ S : TestAlgebra k, SpinSpecification.SchemePoints H S →* (S ⊗[k] W ≃ₗ[S] S ⊗[k] W))
    (ha : ∀ S, Function.Injective (a S) ∧ Set.range (a S) =
      {g | g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
        ∀ x y, g (J.op S x y) = J.op S (g x) (g y)})
    (hb : ∀ S, Function.Injective (b S) ∧ Set.range (b S) =
      {g | g (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] K.unit ∧
        ∀ x y, g (K.op S x y) = K.op S (g x) (g y)})
    (an : ∀ {S T : TestAlgebra k} (p : S ⟶ T) (g : SpinSpecification.SchemePoints G S) (x : S ⊗[k] V),
      pointMap p.hom (a S g x) = a T (mapPoints p g) (pointMap p.hom x))
    (bn : ∀ {S T : TestAlgebra k} (p : S ⟶ T) (g : SpinSpecification.SchemePoints H S) (x : S ⊗[k] W),
      pointMap p.hom (b S g x) = b T (mapPoints p g) (pointMap p.hom x))
    (C : L ⊗[k] W ≃ₗ[L] L ⊗[k] V)
    (hU : C (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] J.unit)
    (hO : ∀ x y, C (K.op L x y) = J.op L (C x) (C y))
    (c : Gal(L/k) → (fieldTest k L ⟶ G.X))
    (hC : ∀ σ (w : W), a (CommAlgCat.of k L) (c σ) (pointMap σ.toAlgHom (C (1 ⊗ₜ[k] w))) =
      C (1 ⊗ₜ[k] w)) :
    ∃ i : relativePoints G (fieldTest k L) ≅ relativePoints H (fieldTest k L),
      ∀ σ, transportedAut k L i σ = innerAut (c σ) := by
  classical
  have hExists (S : TestAlgebra k) (f : L →ₐ[k] S) :
      ∃ φ : SpinSpecification.SchemePoints G S ≃* SpinSpecification.SchemePoints H S,
        ∀ g x, extendComparison f C (b S (φ g) x) = a S g (extendComparison f C x) := by
    obtain ⟨hu, ho⟩ := extendComparison_preserves f C J K hU hO
    exact actions_conjugated J K S (a S) (b S) (ha S) (hb S) (extendComparison f C) hu ho
  choose φ hφ using hExists
  have hNat {R S : TestAlgebra k} (p : R ⟶ S) (f : L →ₐ[k] R)
      (g : SpinSpecification.SchemePoints G R) :
      mapPoints p (φ R f g) = φ S (p.hom.comp f) (mapPoints p g) := by
    apply (hb S).1
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    let E := extendComparison (p.hom.comp f) C
    apply E.injective
    change E (b S (mapPoints p (φ R f g)) (r ⊗ₜ[k] w)) =
      E (b S (φ S (p.hom.comp f) (mapPoints p g)) (r ⊗ₜ[k] w))
    rw [hφ]
    have hx (x : R ⊗[k] W) :
        E (b S (mapPoints p (φ R f g)) (pointMap p.hom x)) =
          a S (mapPoints p g) (E (pointMap p.hom x)) := by
      rw [← bn, ← extendComparison_natural, hφ, an, extendComparison_natural]
    have h := hx (1 ⊗ₜ[k] w)
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at h
    have hr : (r ⊗ₜ[k] w : S ⊗[k] W) = r • ((1 : S) ⊗ₜ[k] w) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hr, map_smul, map_smul, map_smul, map_smul, h]
  obtain ⟨i, hi⟩ := relative_equivalence_from_points hG hH φ hNat
  refine ⟨i, ?_⟩
  intro σ
  have he : restrictIso (fieldMap k L σ) i = (innerAut (c σ)).asIso ≪≫ i := by
    apply Iso.ext
    apply relativeHom_ext_affine
    intro R f g
    let e := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f
    let h := e.unop.hom
    have hf : fieldPoint R h = f := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f
    let hσ := h.comp σ.toAlgHom
    let t := fieldPoint R h ≫ c σ
    have hF : fieldPoint R h ≫ fieldMap k L σ = fieldPoint R hσ := by
      change (testSpec k).map (CommAlgCat.ofHom h).op ≫
        (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op = (testSpec k).map (CommAlgCat.ofHom hσ).op
      rw [← Functor.map_comp, ← op_comp]
      rfl
    rw [← hf]
    change i.hom.app (op (Over.mk (fieldPoint R h ≫ fieldMap k L σ))) g =
      i.hom.app (op (Over.mk (fieldPoint R h))) (t * g * t⁻¹)
    rw [hF, hi, hi]
    let E := extendComparison h C
    let Eσ := extendComparison hσ C
    have hEq (x : R ⊗[k] W) : a R t (Eσ x) = E x := by
      induction x using TensorProduct.inductionOn with
      | tmul r w =>
        change a R t (extendComparison hσ C (r ⊗ₜ[k] w)) = extendComparison h C (r ⊗ₜ[k] w)
        rw [extendComparison_tmul, extendComparison_tmul, map_smul]
        let f : CommAlgCat.of k L ⟶ R := ConcreteCategory.ofHom (C := CommAlgCat k) h
        have hh := congrArg (pointMap h) (hC σ w)
        change pointMap f.hom (a _ (c σ) (pointMap σ.toAlgHom (C (1 ⊗ₜ[k] w)))) =
          pointMap f.hom (C (1 ⊗ₜ[k] w)) at hh
        rw [an f, pointMap_compose] at hh
        exact congrArg (r • ·) hh
      | add x y hx hy => simp only [map_add, hx, hy]
    apply (hb R).1
    apply LinearEquiv.ext
    intro x
    apply E.injective
    change E (b R (φ R hσ g) x) = E (b R (φ R h (t * g * t⁻¹)) x)
    rw [← hEq (b R (φ R hσ g) x)]
    change a R t (extendComparison hσ C (b R (φ R hσ g) x)) =
      extendComparison h C (b R (φ R h (t * g * t⁻¹)) x)
    rw [hφ, hφ, map_mul, map_mul, map_inv]
    change a R t (a R g (Eσ x)) = a R t (a R g ((a R t).symm (E x)))
    rw [← hEq x, LinearEquiv.symm_apply_apply]
  rw [transportedAut, he]
  apply Aut.ext
  simp

end DescentComparison

section Realization

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest)
open private modelBaseChange modelBaseChange_tmul modelBaseChange_operator mapModel_unit from
  LinearAlgebraicGroups.Albert.IntrinsicCubic
open private ground_operator from LinearAlgebraicGroups.Albert.QuadraticOperators
open private fibreIterateIso from LinearAlgebraicGroups.Classification.IntegralRealization

set_option backward.isDefEq.respectTransparency false

private theorem split_albert_law (k : Type) [Field k] :
    ∃ J : ParaQuadratic k (SplitRank.octonion.Model k),
      IsAlbert J ∧ IsSplitModel J .octonion ∧
      ∀ (B : Type) [CommRing B] [Algebra k B], Nonempty (SplitChart J B) := by
  let weights := LowerRankSpecification.untwisted k
  let J := ParaQuadratic.ofJordan (weightedHermitianJordan weights (Zorn.isOctonion k))
  have hc (B : Type) [CommRing B] [Algebra k B] : Nonempty (SplitChart J B) := by
    refine ⟨⟨modelBaseChange k B, ?_, ?_⟩⟩
    · change modelBaseChange k B (1 ⊗ₜ[k] cubicUnit) = _
      rw [modelBaseChange_tmul, one_smul]
      exact mapModel_unit (algebraMap k B)
    · intro x y
      exact modelBaseChange_operator x y
  obtain ⟨c⟩ := hc k
  refine ⟨J, (albert_iff_split_octonion_after_cover J).2
    ⟨k, inferInstance, inferInstance, inferInstance, c.coordinates, c.unit, c.op⟩, ?_, hc⟩
  exact ⟨LinearEquiv.refl k _, rfl, fun x y => ground_operator weights (Zorn.isOctonion k) x y⟩

private def affine_algebraic_group {k : Type} [Field k] (G : GroupScheme k)
    (ha : IsAffine G.X.left) (hf : LocallyOfFinitePresentation G.X.hom) : AffineAlgebraicGroup k := by
  letI := ha
  letI := hf
  exact ⟨G, ha, inferInstance, inferInstance⟩

private def chevalley_scalar_tower (k L : Type) [Field k] [Field L] [Algebra k L]
    {D : Pinning.BasedRootDatum.{0}} (C : IntegralSemisimpleModel.Model D) :
    (groupChange k L).obj ((chevalleyChange k).obj C.group) ≅
      (chevalleyChange L).obj C.group := by
  letI : Algebra IntegralSemisimpleModel.Integers.{0} k := IntegralSemisimpleModel.integerAlgebra k
  letI : Algebra IntegralSemisimpleModel.Integers.{0} L := IntegralSemisimpleModel.integerAlgebra L
  exact fibreIterateIso (by
    ext x
    change algebraMap k L (x.down : k) = (x.down : L)
    exact map_intCast (algebraMap k L) x.down) C.group

set_option maxHeartbeats 800000 in
/-- A form of split F₄ descends together with its pointed quadratic law. -/
theorem formsAndIsotropy : FormsAndIsotropy := by
  obtain ⟨S, forms⟩ := AutomorphismType.automorphismType
  refine ⟨S, ?_⟩
  intro k K _ _ _ _ H hSplit
  obtain ⟨_, R, eC, _⟩ := S.chevalley.fieldFibre k
  let P := R.pinned
  let G₀ := P.pair.G
  obtain ⟨J₀, hJ₀, hModel, charts⟩ := split_albert_law k
  obtain ⟨G, _, _, hRep, _, _, hCenter, _, _, hCompare⟩ := forms J₀ hJ₀
  obtain ⟨eG⟩ := hCompare hModel
  let e₀ : G₀.val ≅ G := eC.symm ≪≫ eG.symm
  have hCenter₀ : IsCenterless G₀.val := centerless_of_iso e₀.symm hCenter
  obtain ⟨a, ha, an⟩ := represents_of_iso hRep e₀
  obtain ⟨eH⟩ := hSplit
  let eH₀ : (groupChange k K).obj G₀.val ≅ (groupChange k K).obj H.val :=
    (groupChange k K).mapIso eC.symm ≪≫ chevalley_scalar_tower k K S.chevalley ≪≫ eH.symm
  obtain ⟨L, ⟨i⟩⟩ := finite_trivialization G₀ H eH₀
  obtain ⟨c, hc, hOne, hMul⟩ := displacement hCenter₀
    (split_group_conjugation P S.datum S.datumCoordinates R.attached R.datumIso
      AutomorphismType.rootLatticeCalculation AutomorphismType.corootCalculation
      hCenter₀ (fieldTest k L)) i
  let ρ := semilinearTwist a an c hOne hMul
  obtain ⟨chart⟩ := charts L
  obtain ⟨J, hJ, hU, hO⟩ := twisted_law a (fun R => (ha R).2) an c hOne hMul chart
  let M : Type := ρ.fixed
  let C : L ⊗[k] M ≃ₗ[L] L ⊗[k] SplitRank.octonion.Model k := ρ.descentEquiv
  have hC (σ) (w : M) :
      a (CommAlgCat.of k L) (c σ) (pointMap σ.toAlgHom (C (1 ⊗ₜ[k] w))) =
        C (1 ⊗ₜ[k] w) := by
    have h : C (1 ⊗ₜ[k] w) = w.val := by
      change (1 : L) • w.val = w.val
      exact one_smul L w.val
    rw [h]
    exact w.property σ
  obtain ⟨GJ, hAff, hFP, hRepJ, _⟩ := forms J hJ
  let JGroup := affine_algebraic_group GJ hAff hFP
  have ⟨b, hb, bn⟩ := hRepJ
  obtain ⟨j, hj⟩ := relative_law_comparison G₀.property.1 hAff J₀ J
      a b ha hb an bn C hU hO c hC
  obtain ⟨d⟩ := same_displacement_descends H JGroup i j
    (fun σ => (hc σ).symm.trans (hj σ).symm)
  have hRepH : RepresentsAutomorphisms J H.val := represents_of_iso hRepJ d
  obtain ⟨F, hF, _⟩ := (intrinsic_coefficients J hJ).1
  refine ⟨M, inferInstance, inferInstance, J, F, hJ, hF, hRepH, ?_⟩
  intro cochar hCochar
  have hNorm := norm_zero_of_cocharacter hJ hF hRepH cochar hCochar
  exact ⟨hNorm, rankOneIdempotentOfNormZero J F hJ hF hNorm⟩

end Realization

end
end LinearAlgebraicGroups.Arithmetic.AlbertFrames
