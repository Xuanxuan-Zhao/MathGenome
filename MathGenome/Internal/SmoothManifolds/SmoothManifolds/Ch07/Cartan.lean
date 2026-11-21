import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.Cartan
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.VectorFieldDerivations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.BracketFromFlow
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section

namespace SmoothManifolds.CartanResults
open ModelData AtlasData TangentData TangentBundleData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData VectorFieldData CartanData
open DifferentialData MaximalFlowData Set Filter
open scoped Topology
universe u v

/-- The identification used to define contraction is the original evaluation. -/
theorem evaluationEquiv_apply {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (p : M) (k : ℕ) (ω : Fiber (TangentSpace S p) k) :
    evaluationEquiv K p k ω = evaluate (TangentSpace S p) k ω := by
  unfold evaluationEquiv
  rfl

private theorem contraction_apply_proof :
    Specs.SmoothManifolds.Ch07.Cartan.contraction_applyType.{u} := by
  intro n a M _ S C X k ω p v
  change evaluate (TangentSpace S p) k
    ((evaluationEquiv C.tangent.fiberCoordinates p k).symm
      ((evaluate (TangentSpace S p) (k+1) (ω p)).curryLeft (X p))) v = _
  rw [← evaluationEquiv_apply C.tangent.fiberCoordinates p k,
    LinearEquiv.apply_symm_apply]
  rfl

private theorem contraction_zero_proof :
    Specs.SmoothManifolds.Ch07.Cartan.contraction_zeroType.{u} := by
  intro n a M _ S C X ω
  rfl

/-- An algebraic polarization of alternation, requiring no topology. -/
theorem curryLeft_anticomm {V : Type u} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (A : AlternatingMap ℝ V ℝ (Fin (k+1+1))) (x y : V) :
    (A.curryLeft x).curryLeft y + (A.curryLeft y).curryLeft x = 0 := by
  have h := A.curryLeft_same (x+y)
  rw [add_comm]
  simpa only [map_add, AlternatingMap.curryLeft_add, LinearMap.add_apply,
    AlternatingMap.curryLeft_same, zero_add, add_zero] using h

private theorem contraction_anticomm_proof :
    Specs.SmoothManifolds.Ch07.Cartan.contraction_anticommType.{u} := by
  intro n a M _ S C X Y k ω
  cases k with
  | zero => simp [contraction]
  | succ k =>
    cases k with
    | zero => simp [contraction]
    | succ k =>
      funext p
      apply (evaluationEquiv C.tangent.fiberCoordinates p k).injective
      simp only [Pi.add_apply, Pi.zero_apply, map_add, map_zero]
      apply AlternatingMap.ext
      intro v
      simp only [evaluationEquiv_apply, add_apply]
      change (evaluate (TangentSpace S p) k
        ((evaluationEquiv C.tangent.fiberCoordinates p k).symm
          ((evaluate (TangentSpace S p) (k+1)
            ((evaluationEquiv C.tangent.fiberCoordinates p (k+1)).symm
              ((evaluate (TangentSpace S p) (k+1+1) (ω p)).curryLeft (Y p)))).curryLeft (X p)))) v +
        (evaluate (TangentSpace S p) k
        ((evaluationEquiv C.tangent.fiberCoordinates p k).symm
          ((evaluate (TangentSpace S p) (k+1)
            ((evaluationEquiv C.tangent.fiberCoordinates p (k+1)).symm
              ((evaluate (TangentSpace S p) (k+1+1) (ω p)).curryLeft (X p)))).curryLeft (Y p)))) v = 0
      simp only [← evaluationEquiv_apply C.tangent.fiberCoordinates p,
        LinearEquiv.apply_symm_apply]
      simpa only [evaluationEquiv_apply, add_apply, zero_apply] using
        congrArg (fun A : AlternatingMap ℝ (TangentSpace S p) ℝ (Fin k) => A v)
        (curryLeft_anticomm k (evaluate (TangentSpace S p) (k+1+1) (ω p)) (Y p) (X p))



private theorem contraction_linear_proof :
    Specs.SmoothManifolds.Ch07.Cartan.contraction_linearType.{u} := by
  intro n a M _ S C X k α β r
  cases k with
  | zero => simp [contraction]
  | succ k =>
    constructor
    · funext p
      simp [contraction, map_add, AlternatingMap.curryLeft_add]
    · funext p
      simp [contraction, map_smul, AlternatingMap.curryLeft_smul]

private theorem exteriorDerivative_eq_proof
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.exteriorDerivative_eqType.{u} := by
  intro n a M _ S C k ω η hη
  have h : ∃ η, HasExteriorDerivative C ω η := ⟨η, hη⟩
  rw [exteriorDerivative, dite_eq_left h]
  exact h_unique C k ω _ η (Classical.choose_spec h) hη

private theorem exteriorDerivative_zero_proof
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_zero : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.exteriorDerivative_zeroType.{u} := by
  intro n a M _ S C k
  exact exteriorDerivative_eq_proof h_unique C k 0 0 (h_zero C k)

/-- Coordinate derivatives uniquely determine a field on the flow neighborhood. -/
theorem flowLieDerivative_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (F : MaximalFlowData.CurveFamily M) (k : ℕ) (ω η ζ : Field S k) (O : Set M)
    (hη : HasFlowLieDerivativeOn C F k ω η O)
    (hζ : HasFlowLieDerivativeOn C F k ω ζ O) : ∀ p ∈ O, η p = ζ p := by
  intro p hpO
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let b := ((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.exteriorPower k
  apply b.repr.injective
  apply Finsupp.ext
  intro I
  exact (hη c hc p hp hpO I).unique (hζ c hc p hp hpO I)

private theorem flowLieDerivative_eq_proof :
    Specs.SmoothManifolds.Ch07.Cartan.flowLieDerivative_eqType.{u} := by
  intro n a M _ S C F k ω η hη
  have h : ∃ η, HasFlowLieDerivativeOn C F k ω η Set.univ := ⟨η, hη⟩
  rw [flowLieDerivative, dite_eq_left h]
  funext p
  exact flowLieDerivative_unique C F k ω _ η Set.univ (Classical.choose_spec h) hη p
    (Set.mem_univ p)

/-- Evaluation equivalence on a fixed Euclidean model. -/
def modelEvaluationEquiv (n k : ℕ) :
    Fiber (Euclidean n) k ≃ₗ[ℝ] AlternatingMap ℝ (Euclidean n) ℝ (Fin k) :=
  LinearEquiv.ofBijective (evaluate (Euclidean n) k)
    (ExteriorAlgebraResults.alternating_interpretation (Euclidean n) k)

@[simp] theorem modelEvaluationEquiv_apply (n k : ℕ) (ω : Fiber (Euclidean n) k) :
    modelEvaluationEquiv n k ω = evaluate (Euclidean n) k ω := rfl

/-- In coordinates contraction is a single fixed bilinear map. -/
def modelContraction (n k : ℕ) :
    Euclidean n →ₗ[ℝ] (Index n (k+1) → ℝ) →ₗ[ℝ] (Index n k → ℝ) :=
  LinearMap.mk₂ ℝ (fun x α =>
    ((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun
      ((modelEvaluationEquiv n k).symm
        ((modelEvaluationEquiv n (k+1)
          (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm α)).curryLeft x)))
    (by intros; simp only [map_add])
    (by intros; simp only [map_smul])
    (by intros; simp only [map_add, AlternatingMap.curryLeft_add, LinearMap.add_apply])
    (by intros; simp only [map_smul, AlternatingMap.curryLeft_smul, LinearMap.smul_apply])

/-- Naturality of exterior evaluation between distinct universes. -/
theorem evaluate_coordinate_map {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (k : ℕ) (L : W →ₗ[ℝ] V) (ω : Fiber V k) (v : Fin k → W) :
    evaluate W k (exteriorPower.map k L.dualMap ω) v =
      evaluate V k ω (fun i => L (v i)) := by
  have hmem : ω ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ k (M := Module.Dual ℝ V))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    rw [exteriorPower.map_apply_ιMulti]
    change exteriorPower.pairingDual ℝ W k
      (exteriorPower.ιMulti ℝ k (L.dualMap ∘ α)) (exteriorPower.ιMulti ℝ k v) =
      exteriorPower.pairingDual ℝ V k (exteriorPower.ιMulti ℝ k α)
        (exteriorPower.ιMulti ℝ k (fun i => L (v i)))
    rw [exteriorPower.pairingDual_ιMulti_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
    rfl
  | zero => simp
  | add x y hx hy hxx hyy => simp only [map_add, add_apply, hxx, hyy]
  | smul r x hx hxx => simp only [map_smul, smul_apply, hxx]

/-- Dual bases and exterior coordinate transport use the same linear equivalence. -/
theorem exterior_coordinate_transport {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (e : V ≃ₗ[ℝ] Euclidean n) (k : ℕ) (ω : Fiber V k) :
    (((Pi.basisFun ℝ (Fin n)).map e.symm).dualBasis.exteriorPower k).equivFun ω =
      ((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun
        (exteriorPower.map k e.symm.dualMap.toLinearMap ω) := by
  have hb : ((Pi.basisFun ℝ (Fin n)).map e.symm).dualBasis =
      (Pi.basisFun ℝ (Fin n)).dualBasis.map e.dualMap := by
    apply DFunLike.ext
    intro i
    apply LinearMap.ext
    intro v
    simp [Module.Basis.map_repr]
  rw [hb, ExteriorAlgebraResults.exteriorBasis_map]
  ext I
  simp only [Module.Basis.equivFun_apply, Module.Basis.map_repr]
  rfl

/-- The coefficient formula is fiberwise and therefore holds without smoothness. -/
theorem contraction_coefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : Section S) (k : ℕ) (ω : Field S (k+1))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    (fun I => coefficients C k c hc (contraction C X (k+1) ω) p I) =
      modelContraction n k (C.tangent.fiberCoordinates.equiv c hc p.val p.property (X p.val))
        (fun I => coefficients C (k+1) c hc ω p I) := by
  let e := C.tangent.fiberCoordinates.equiv c hc p.val p.property
  change (((Pi.basisFun ℝ (Fin n)).map e.symm).dualBasis.exteriorPower k).equivFun
    (contraction C X (k+1) ω p.val) = _
  have h := exterior_coordinate_transport (V := TangentSpace S p.val) (n := n) e k (contraction C X (k+1) ω p.val)
  apply h.trans
  change _ = ((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun
    ((modelEvaluationEquiv n k).symm ((modelEvaluationEquiv n (k+1)
      (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm
        ((((Pi.basisFun ℝ (Fin n)).map e.symm).dualBasis.exteriorPower (k+1)).equivFun (ω p.val)))).curryLeft (e (X p.val))))
  have hω := exterior_coordinate_transport (V := TangentSpace S p.val) (n := n) e (k+1) (ω p.val)
  rw [hω, LinearEquiv.symm_apply_apply]
  congr 1
  apply (modelEvaluationEquiv n k).injective
  rw [LinearEquiv.apply_symm_apply]
  apply AlternatingMap.ext
  intro v
  rw [modelEvaluationEquiv_apply]
  have hd : e.symm.dualMap.toLinearMap = e.symm.toLinearMap.dualMap := rfl
  rw [hd]
  rw [evaluate_coordinate_map (V := TangentSpace S p.val) (W := Euclidean n) k e.symm.toLinearMap]
  change evaluate (TangentSpace S p.val) k
    ((evaluationEquiv C.tangent.fiberCoordinates p.val k).symm
      ((evaluate (TangentSpace S p.val) (k+1) (ω p.val)).curryLeft (X p.val)))
    (fun i => e.symm (v i)) = _
  have hev : ∀ η : Fiber (TangentSpace S p.val) k,
      evaluationEquiv C.tangent.fiberCoordinates p.val k η =
        evaluate (TangentSpace S p.val) k η := fun _ => rfl
  rw [← hev, LinearEquiv.apply_symm_apply]
  rw [AlternatingMap.curryLeft_apply_apply, AlternatingMap.curryLeft_apply_apply,
    modelEvaluationEquiv_apply]
  rw [evaluate_coordinate_map (V := TangentSpace S p.val) (W := Euclidean n) (k+1) e.symm.toLinearMap]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp
/-- Coordinates of a smooth vector field, on an ordinary chart domain. -/
theorem field_coordinates_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : SmoothField C.tangent) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p : c.source => C.tangent.fiberCoordinates.equiv c hc p.val p.property (X.val p.val)) := by
  letI := C.tangent.topology
  let f : M → TangentBundleData.TotalSpace S := fun p => ⟨p, X.val p⟩
  have hf := (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
    C.tangent.manifold.smoothStructure.val f c.source c.open_source).mp
    (fun p hp => X.smooth p)
  intro p
  have ht : f p.val ∈ (C.tangent.chart c hc).source := by
    rw [C.tangent.chart_source]; exact p.property
  have hh : FrameData.VectorSmoothAt
      (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p : c.source => TangentBundle.chartFiber C.tangent c hc (f p.val)) p := by
    refine ⟨?_, ?_⟩
    · exact (C.tangent.productCoordinates.linearEquiv.symm.continuous.continuousAt.comp
        (continuous_subtype_val.continuousAt.comp
          (((C.tangent.chart c hc).continuousAt ht).comp (f := fun q : c.source => f q.val) (hf p).1))).snd
    · intro d hd hpd
      obtain ⟨U, hU, hpU, F, hF, he⟩ := (hf p).2 d hd (C.tangent.chart c hc)
        (TangentBundle.chart_mem S C.tangent c hc) hpd ht
      refine ⟨U, hU, hpU, fun z => (C.tangent.productCoordinates.linearEquiv.symm (F z)).2,
        (C.tangent.productCoordinates.linearEquiv.symm.contDiff.snd.comp_contDiffOn hF), ?_⟩
      exact he.fun_comp (fun z => (C.tangent.productCoordinates.linearEquiv.symm z).2)
  apply hh.congr
  exact Filter.Eventually.of_forall (fun q =>
    TangentBundle.chartFiber_eq S C.tangent c hc (f q.val) q.property)

/-- Contraction preserves genuine smooth exterior sections, also at a boundary. -/
theorem contraction_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (X : SmoothField C.tangent)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) :
    IsForm (B (k-1)) (contraction C X.val k ω) := by
  cases k with
  | zero =>
    apply (ExteriorAlgebraResults.smooth_iff_coefficients C 0 (B 0) 0).mpr
    intro c hc I p
    simpa only [coefficients, Pi.zero_apply, map_zero, Finsupp.zero_apply] using
      FrameData.VectorSmoothAt.const
        (openSubsetAtlas S.smoothStructure.val c.source c.open_source) (0 : ℝ) p
  | succ k =>
    apply (ExteriorAlgebraResults.smooth_iff_coefficients C k (B k) _).mpr
    intro c hc I p
    have hX := field_coordinates_smooth C X c hc p
    have hωc := FrameData.VectorSmoothAt.pi
      (fun I => (ExteriorAlgebraResults.smooth_iff_coefficients C (k+1) (B (k+1)) ω).mp hω c hc I p)
    let T : Euclidean n →L[ℝ] (Index n (k+1) → ℝ) →L[ℝ] (Index n k → ℝ) :=
      LinearMap.toContinuousLinearMap
        (LinearMap.toContinuousLinearMap.toLinearMap.comp (modelContraction n k))
    have hh := ((hX.postcomp T.contDiff).clm_apply hωc).postcomp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index n k => ℝ) I).contDiff
    apply hh.congr
    exact Filter.Eventually.of_forall (fun q =>
      (congrFun (contraction_coefficients C X.val k ω c hc q) I).symm)


/-- On smooth fields the selected coordinate derivative is an actual derivative
and is a smooth section of the original exterior bundle. -/
theorem exteriorDerivative_smooth
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) :
    HasExteriorDerivative C ω (exteriorDerivative C k ω) ∧
      IsForm (B (k+1)) (exteriorDerivative C k ω) := by
  obtain ⟨D, hD, _⟩ := h_exists C B
  have hη := h_coords C B D hD k ω hω
  have hex : ∃ η, HasExteriorDerivative C ω η := ⟨D k ω, hη⟩
  have heq : exteriorDerivative C k ω = D k ω := by
    rw [exteriorDerivative, dite_eq_left hex]
    exact h_unique C k ω _ _ (Classical.choose_spec hex) hη
  rw [heq]
  exact ⟨hη, hD.smooth k ω hω⟩

theorem isForm_add {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k)
    (α β : Field S k) (hα : IsForm B α) (hβ : IsForm B β) : IsForm B (α+β) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C k B (α+β)).mpr
  intro c hc I p
  have ha := (ExteriorAlgebraResults.smooth_iff_coefficients C k B α).mp hα c hc I p
  have hb := (ExteriorAlgebraResults.smooth_iff_coefficients C k B β).mp hβ c hc I p
  have hh := (ha.prod hb).postcomp (contDiff_fst.add contDiff_snd)
  simpa only [coefficients, Pi.add_apply, map_add, Finsupp.add_apply] using hh


/-- Identification with any global exterior-derivative family on smooth inputs. -/
theorem exteriorDerivative_eq_family
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (D : ∀ k, Field S k → Field S (k+1)) (hD : DerivativeAxioms C B D)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) :
    exteriorDerivative C k ω = D k ω :=
  exteriorDerivative_eq_proof h_unique C k ω _ (h_coords C B D hD k ω hω)

/-- Square-zero is a statement about the selected intrinsic operator. -/
theorem exteriorDerivative_square
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) :
    exteriorDerivative C (k+1) (exteriorDerivative C k ω) = 0 := by
  obtain ⟨D, hD, _⟩ := h_exists C B
  rw [exteriorDerivative_eq_family h_coords h_unique C B D hD k ω hω,
    exteriorDerivative_eq_family h_coords h_unique C B D hD (k+1) _ (hD.smooth k ω hω)]
  exact hD.square k ω hω

/-- Additivity on genuine smooth exterior sections. -/
theorem exteriorDerivative_add
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (k : ℕ) (α β : Field S k) (hα : IsForm (B k) α) (hβ : IsForm (B k) β) :
    exteriorDerivative C k (α+β) = exteriorDerivative C k α + exteriorDerivative C k β := by
  obtain ⟨D, hD, _⟩ := h_exists C B
  rw [exteriorDerivative_eq_family h_coords h_unique C B D hD k (α+β)
      (isForm_add C k (B k) α β hα hβ),
    exteriorDerivative_eq_family h_coords h_unique C B D hD k α hα,
    exteriorDerivative_eq_family h_coords h_unique C B D hD k β hβ]
  exact hD.add k α β hα hβ

private theorem operators_smooth_proof
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.operators_smoothType.{u} := by
  intro n a M _ S C B X k ω hω
  have hD := exteriorDerivative_smooth h_exists h_coords h_unique C B k ω hω
  refine ⟨hD.1, hD.2, contraction_smooth C B X k ω hω, ?_⟩
  cases k with
  | zero => exact contraction_smooth C B X 1 _ hD.2
  | succ k =>
    exact isForm_add C (k+1) (B (k+1)) _ _
      (exteriorDerivative_smooth h_exists h_coords h_unique C B k _
        (contraction_smooth C B X (k+1) ω hω)).2
      (contraction_smooth C B X (k+1+1) _ hD.2)

/-- A positive-degree contraction is a linear map and hence sends zero to zero. -/
theorem contraction_map_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : Section S) (k : ℕ) : contraction C X k (0 : Field S k) = 0 := by
  cases k with
  | zero => rfl
  | succ k => funext p; simp [contraction]

private theorem lie_commutes_d_proof
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_dType.{u} := by
  intro n a M _ S C B X k ω hω
  have hdω := (exteriorDerivative_smooth h_exists h_coords h_unique C B k ω hω).2
  have hdd := exteriorDerivative_square h_exists h_coords h_unique C B k ω hω
  apply sub_eq_zero.mpr
  cases k with
  | zero =>
    change exteriorDerivative C 0 (contraction C X.val 1 (exteriorDerivative C 0 ω)) +
      contraction C X.val 2 (exteriorDerivative C 1 (exteriorDerivative C 0 ω)) = _
    rw [hdd, contraction_map_zero, add_zero]
    rfl
  | succ k =>
    have hiω := contraction_smooth C B X (k+1) ω hω
    have hdiω := (exteriorDerivative_smooth h_exists h_coords h_unique C B k _ hiω).2
    have hidω := contraction_smooth C B X (k+1+1) _ hdω
    simp only [lieDerivative, eq_mp_eq_cast, cast_eq]
    rw [hdd, contraction_map_zero, add_zero,
      exteriorDerivative_add h_exists h_coords h_unique C B (k+1) _ _ hdiω hidω,
      exteriorDerivative_square h_exists h_coords h_unique C B k _ hiω, zero_add]

/-- Evaluation in an increasing coordinate coframe is the determinant formula. -/
theorem fieldEvaluation_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (Y : Fin k → Section S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    fieldEvaluation k ω Y p.val = ∑ I : Index n k, coefficients C k c hc ω p I *
      (Matrix.of (fun i j => C.tangent.fiberCoordinates.equiv c hc p.val p.property
        (Y j p.val) (Set.powersetCard.ofFinEmbEquiv.symm I i))).det := by
  unfold fieldEvaluation
  rw [ExteriorAlgebraResults.coefficient_expansion C k c hc ω p]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [ExteriorAlgebraResults.determinant_normalization]
  congr 2

/-- Determinants are smooth polynomial functions of all matrix entries. -/
theorem determinant_contDiff (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin k → Fin k → ℝ => (Matrix.of A).det) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

/-- The scalar obtained by evaluating a smooth form on smooth vector fields
is itself smooth. This includes the empty evaluation in degree zero. -/
theorem fieldEvaluation_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (k : ℕ) (ω : Field S k)
    (Y : Fin k → SmoothField C.tangent) (hω : IsForm (B k) ω) :
    PartitionData.ScalarSmooth S.smoothStructure.val
      (fieldEvaluation k ω (fun i => (Y i).val)) := by
  have hlocal (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
      FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p : c.source => fieldEvaluation k ω (fun i => (Y i).val) p.val) := by
    intro p
    have hsum : FrameData.VectorSmoothAt
        (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p : c.source => ∑ I : Index n k, coefficients C k c hc ω p I *
          (Matrix.of (fun i j => C.tangent.fiberCoordinates.equiv c hc p.val p.property
            ((Y j).val p.val) (Set.powersetCard.ofFinEmbEquiv.symm I i))).det) p := by
      apply FrameData.VectorSmoothAt.sum
      intro I
      have hα := (ExteriorAlgebraResults.smooth_iff_coefficients C k (B k) ω).mp hω c hc I p
      have hmatrix : FrameData.VectorSmoothAt
          (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
          (fun q : c.source => fun i j =>
            C.tangent.fiberCoordinates.equiv c hc q.val q.property ((Y j).val q.val)
              (Set.powersetCard.ofFinEmbEquiv.symm I i)) p := by
        apply FrameData.VectorSmoothAt.pi
        intro i
        apply FrameData.VectorSmoothAt.pi
        intro j
        exact (field_coordinates_smooth C (Y j) c hc p).postcomp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
            (Set.powersetCard.ofFinEmbEquiv.symm I i)).contDiff
      exact (hα.prod (hmatrix.postcomp (determinant_contDiff k))).postcomp
        (contDiff_fst.mul contDiff_snd)
    apply hsum.congr
    exact Filter.Eventually.of_forall (fun q =>
      (fieldEvaluation_coordinates C k ω (fun i => (Y i).val) c hc q).symm)
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let q : c.source := ⟨p, hp⟩
  have hext := (hlocal c hc q).2 (c.subtypeRestr (s := ⟨c.source, c.open_source⟩) ⟨q⟩)
    ⟨⟨q⟩, c, hc, rfl⟩ (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hp)
  apply scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hp
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hext
  refine ⟨U, hU, hpU, F, hF, ?_⟩
  rw [← c.open_source.isOpenEmbedding_subtypeVal.map_nhds_eq q]
  exact he

/-- Smooth sections are stable under real scalar multiplication. -/
theorem isForm_smul {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k)
    (r : ℝ) (ω : Field S k) (hω : IsForm B ω) : IsForm B (r • ω) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C k B (r • ω)).mpr
  intro c hc I p
  have h := (ExteriorAlgebraResults.smooth_iff_coefficients C k B ω).mp hω c hc I p
  have hh := h.postcomp (contDiff_const.mul contDiff_id :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => r * x))
  simpa only [coefficients, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] using hh

/-- Smooth sections are stable under negation. -/
theorem isForm_neg {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k)
    (ω : Field S k) (hω : IsForm B ω) : IsForm B (-ω) := by
  have he : (-1 : ℝ) • ω = -ω := neg_one_smul ℝ ω
  rw [← he]
  exact isForm_smul C k B (-1 : ℝ) ω hω

/-- Smooth sections are stable under subtraction. -/
theorem isForm_sub {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k)
    (α β : Field S k) (hα : IsForm B α) (hβ : IsForm B β) : IsForm B (α-β) := by
  simpa only [sub_eq_add_neg] using isForm_add C k B α (-β) hα (isForm_neg C k B β hβ)

/-- The selected coordinate derivative is real homogeneous on smooth forms. -/
theorem exteriorDerivative_smul
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (k : ℕ) (r : ℝ) (ω : Field S k) (hω : IsForm (B k) ω) :
    exteriorDerivative C k (r • ω) = r • exteriorDerivative C k ω := by
  obtain ⟨D, hD, _⟩ := h_exists C B
  rw [exteriorDerivative_eq_family h_coords h_unique C B D hD k (r • ω)
      (isForm_smul C k (B k) r ω hω),
    exteriorDerivative_eq_family h_coords h_unique C B D hD k ω hω]
  exact hD.smul k r ω hω

/-- The selected coordinate derivative preserves differences of smooth forms. -/
theorem exteriorDerivative_sub
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (k : ℕ) (α β : Field S k) (hα : IsForm (B k) α) (hβ : IsForm (B k) β) :
    exteriorDerivative C k (α-β) = exteriorDerivative C k α - exteriorDerivative C k β := by
  have hn : exteriorDerivative C k (-β) = - exteriorDerivative C k β := by
    have he : (-1 : ℝ) • β = -β := neg_one_smul ℝ β
    have hd : (-1 : ℝ) • exteriorDerivative C k β = -exteriorDerivative C k β :=
      neg_one_smul ℝ (exteriorDerivative C k β)
    rw [← he, ← hd]
    exact exteriorDerivative_smul h_exists h_coords h_unique C B k (-1 : ℝ) β hβ
  simpa only [sub_eq_add_neg, hn] using exteriorDerivative_add h_exists h_coords h_unique C B k α (-β)
    hα (isForm_neg C k (B k) β hβ)

/-- Contraction preserves differences, without a regularity hypothesis. -/
theorem contraction_sub {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (X : Section S)
    (k : ℕ) (α β : Field S k) :
    contraction C X k (α-β) = contraction C X k α - contraction C X k β := by
  cases k with
  | zero => simp [contraction]
  | succ k =>
    funext p
    change (evaluationEquiv C.tangent.fiberCoordinates p k).symm
      ((AlternatingMap.curryLeftLinearMap (R := ℝ) (M := TangentSpace S p) (N := ℝ))
        (evaluate (TangentSpace S p) (k+1) ((α-β) p)) (X p)) = _
    simp only [Pi.sub_apply, map_sub, LinearMap.sub_apply]
    rfl

/-- The Cartan extension is additive on smooth sections in every degree. -/
theorem lieDerivative_add
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (k : ℕ) (α β : Field S k)
    (hα : IsForm (B k) α) (hβ : IsForm (B k) β) :
    lieDerivative C X.val k (α+β) = lieDerivative C X.val k α + lieDerivative C X.val k β := by
  cases k with
  | zero =>
    change contraction C X.val 1 (exteriorDerivative C 0 (α+β)) = _
    rw [exteriorDerivative_add h_exists h_coords h_unique C B 0 α β hα hβ,
      (contraction_linear_proof C X.val 1 _ _ 0).1]
    rfl
  | succ k =>
    simp only [lieDerivative, eq_mp_eq_cast, cast_eq]
    rw [(contraction_linear_proof C X.val (k+1) α β 0).1,
      exteriorDerivative_add h_exists h_coords h_unique C B k _ _
        (contraction_smooth C B X (k+1) α hα) (contraction_smooth C B X (k+1) β hβ),
      exteriorDerivative_add h_exists h_coords h_unique C B (k+1) α β hα hβ,
      (contraction_linear_proof C X.val (k+1+1) _ _ 0).1]
    abel

/-- The Cartan extension preserves differences of smooth sections. -/
theorem lieDerivative_sub
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (k : ℕ) (α β : Field S k)
    (hα : IsForm (B k) α) (hβ : IsForm (B k) β) :
    lieDerivative C X.val k (α-β) = lieDerivative C X.val k α - lieDerivative C X.val k β := by
  cases k with
  | zero =>
    change contraction C X.val 1 (exteriorDerivative C 0 (α-β)) = _
    rw [exteriorDerivative_sub h_exists h_coords h_unique C B 0 α β hα hβ, contraction_sub]
    rfl
  | succ k =>
    simp only [lieDerivative, eq_mp_eq_cast, cast_eq]
    rw [contraction_sub,
      exteriorDerivative_sub h_exists h_coords h_unique C B k _ _
        (contraction_smooth C B X (k+1) α hα) (contraction_smooth C B X (k+1) β hβ),
      exteriorDerivative_sub h_exists h_coords h_unique C B (k+1) α β hα hβ, contraction_sub]
    abel


/-- Contraction commutes with pullback for related vectors, pointwise. -/
theorem contraction_pullback_related {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (C : CotangentBundle S) (D : CotangentBundle T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (X : Section S) (Y : Section T) (hXY : ∀ p, L p (X p) = Y (f p))
    (k : ℕ) (ω : Field T k) :
    FormPullbackData.pullbackField S T f L (contraction D Y k ω) =
      contraction C X k (FormPullbackData.pullbackField S T f L ω) := by
  cases k with
  | zero => funext p; simp [contraction, FormPullbackData.pullbackField]
  | succ k =>
    funext p
    apply (evaluationEquiv C.tangent.fiberCoordinates p k).injective
    apply AlternatingMap.ext
    intro v
    simp only [evaluationEquiv_apply]
    rw [FormPullbackResults.pullback_apply, contraction_apply_proof,
      contraction_apply_proof, FormPullbackResults.pullback_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Matrix.cons_val_zero] using (hXY p).symm
    · simp only [Matrix.cons_val_succ]
/-- The selected derivative commutes with genuine smooth pullback. -/
theorem exteriorDerivative_pullback
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_nat : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (k : ℕ) (ω : Field T k) (hω : IsForm (E k) ω) :
    FormPullbackData.pullbackField S T f L (exteriorDerivative A k ω) =
      exteriorDerivative C k (FormPullbackData.pullbackField S T f L ω) := by
  obtain ⟨D, hD, _⟩ := h_exists C B
  obtain ⟨J, hJ, _⟩ := h_exists A E
  have hp := FormPullbackResults.pullback_smooth S T C A f hf L hL k (B k) (E k) ω hω
  rw [exteriorDerivative_eq_family h_coords h_unique A E J hJ k ω hω,
    exteriorDerivative_eq_family h_coords h_unique C B D hD k _ hp]
  exact h_nat S T C A B E D J hD hJ f hf L hL k ω hω


/-- The total action agrees with the intrinsic germ action whenever a smooth
representative exists. -/
theorem scalarAction_eq_germ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (X : Section S)
    (f : M → ℝ) (p : M) (g : SmoothGerm S p) (hg : g.val = Germ.ofFun f) :
    scalarAction X f p = (X p).val g := by
  have h : ∃ g : SmoothGerm S p, g.val = Germ.ofFun f := ⟨g, hg⟩
  rw [scalarAction, dite_eq_left h]
  congr 1
  exact Subtype.ext ((Classical.choose_spec h).trans hg.symm)

/-- Globally smooth scalars are in the represented branch of the action. -/
theorem scalarAction_eq_dFunction {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (X : Section S)
    (f : M → ℝ) (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M) :
    scalarAction X f p = dFunction S f hf p (X p) := by
  exact scalarAction_eq_germ X f p (functionGerm S f hf p) rfl

/-- Smooth vector fields act smoothly on the represented smooth scalars. -/
theorem scalarAction_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : SmoothField C.tangent) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) :
    PartitionData.ScalarSmooth S.smoothStructure.val (scalarAction X.val f) := by
  let F : GlobalSmooth S := ⟨f, (mem_globalSmoothAlgebra_iff S f).mpr hf⟩
  have h := VectorFields.field_action_smooth S C.tangent X F
  have he : (fun p => (X.val p).val (globalToGerm S p F)) = scalarAction X.val f := by
    funext p
    exact (scalarAction_eq_germ X.val f p (globalToGerm S p F) rfl).symm
  rwa [he] at h

/-- Determinant-normalized exterior evaluation agrees with the degree-zero
scalar identification. -/
theorem evaluate_degree_zero {V : Type u} [AddCommGroup V] [Module ℝ V]
    (ω : Fiber V 0) (v : Fin 0 → V) :
    evaluate V 0 ω v = exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V) ω := by
  rw [FormPullbackResults.evaluate_eq_pairing]
  conv_lhs => rw [← (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm_apply_apply ω]
  rw [exteriorPower.zeroEquiv_symm_apply]
  simp

/-- Determinant-normalized exterior evaluation agrees with the degree-one
covector identification. -/
theorem evaluate_degree_one {V : Type u} [AddCommGroup V] [Module ℝ V]
    (ω : Fiber V 1) (v : Fin 1 → V) :
    evaluate V 1 ω v = exteriorPower.oneEquiv ℝ (Module.Dual ℝ V) ω (v 0) := by
  rw [FormPullbackResults.evaluate_eq_pairing]
  conv_lhs => rw [← (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm_apply_apply ω]
  rw [exteriorPower.oneEquiv_symm_apply]
  simp

/-- Local equality of scalar functions implies equality of their intrinsic actions,
including the default branch when no represented germ exists. -/
theorem scalarAction_congr {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (X : Section S)
    (f g : M → ℝ) (p : M) (hfg : f =ᶠ[𝓝 p] g) :
    scalarAction X f p = scalarAction X g p := by
  classical
  have hgerm : Germ.ofFun f = (Germ.ofFun g : Germ (𝓝 p) ℝ) := Germ.coe_eq.mpr hfg
  by_cases h : ∃ h : SmoothGerm S p, h.val = Germ.ofFun f
  · obtain ⟨h, hh⟩ := h
    rw [scalarAction_eq_germ X f p h hh,
      scalarAction_eq_germ X g p h (hh.trans hgerm)]
  · have hn : ¬ ∃ h : SmoothGerm S p, h.val = Germ.ofFun g := by
      rintro ⟨z, hz⟩
      exact h ⟨z, hz.trans hgerm.symm⟩
    simp only [scalarAction, dite_eq_right h, dite_eq_right hn]

/-- Ambient chart extensions compute the actual scalar action. -/
theorem scalarAction_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (X : Section S) (f : M → ℝ) (p : M) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (g : SmoothGerm S p) (hg : g.val = Germ.ofFun f) (F : Euclidean n → ℝ)
    (hF : GermChartExtension S p c g F) :
    scalarAction X f p = fderiv ℝ F (c p).val (K.equiv c hc p hp (X p)) := by
  rw [scalarAction_eq_germ X f p g hg]
  exact VectorFields.tangent_action_coordinates S K p c hc hp (X p) g F hF

/-- Global derivations and the scalar action use the identical represented germ. -/
theorem scalarAction_global {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : SmoothField C.tangent) (f : GlobalSmooth S) (p : M) :
    scalarAction X.val f.val p = (VectorFields.derivationOfField S C.tangent X f).val p := by
  exact scalarAction_eq_germ X.val f.val p (globalToGerm S p f) rfl

/-- The bracket characterized on global derivations acts by the ordinary
commutator on every globally smooth scalar. -/
theorem scalarAction_bracket {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : LieBracketData.BracketOperation b) (X Y : SmoothField C.tangent)
    (f : M → ℝ) (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M) :
    scalarAction (b X Y).val f p =
      scalarAction X.val (scalarAction Y.val f) p -
        scalarAction Y.val (scalarAction X.val f) p := by
  let F : GlobalSmooth S := ⟨f, (mem_globalSmoothAlgebra_iff S f).mpr hf⟩
  let D := VectorFields.derivationOfField S C.tangent X
  let E := VectorFields.derivationOfField S C.tangent Y
  have hrep := hb X Y D E (VectorFields.derivationOfField_represents S C.tangent X)
    (VectorFields.derivationOfField_represents S C.tangent Y)
  have hbr := hrep p F (globalToGerm S p F) rfl
  rw [Derivation.commutator_apply] at hbr
  change (D (E F)).val p - (E (D F)).val p = _ at hbr
  have hY : (E F).val = scalarAction Y.val f := by
    funext q
    exact (scalarAction_global C Y F q).symm
  have hX : (D F).val = scalarAction X.val f := by
    funext q
    exact (scalarAction_global C X F q).symm
  rw [scalarAction_eq_germ (b X Y).val f p (globalToGerm S p F) rfl]
  rw [← hbr, ← scalarAction_global C X (E F) p, ← scalarAction_global C Y (D F) p,
    hX, hY]

/-- Every degree-zero exterior field is the scalar field of its empty evaluation. -/
theorem scalarField_fieldEvaluation_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (ω : Field S 0)
    (Y : Fin 0 → Section S) :
    FormPullbackData.scalarField S (fieldEvaluation 0 ω Y) = ω := by
  funext p
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  change exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))
    ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
      (fieldEvaluation 0 ω Y p)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact evaluate_degree_zero (ω p) (fun i => Y i p)




/-- Cartan's extension acts on every smooth degree-zero field by its actual
intrinsic scalar derivation. Only function correctness and uniqueness of d are used. -/
theorem lie_evaluation_degree_zero
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (ω : Field S 0)
    (Y : Fin 0 → SmoothField C.tangent) (hω : IsForm (B 0) ω) :
    PartitionData.ScalarSmooth S.smoothStructure.val
      (fieldEvaluation 0 ω (fun i => (Y i).val)) ∧
    ∀ p, fieldEvaluation 0 (lieDerivative C X.val 0 ω) (fun i => (Y i).val) p =
      scalarAction X.val (fieldEvaluation 0 ω (fun i => (Y i).val)) p := by
  let f := fieldEvaluation 0 ω (fun i => (Y i).val)
  have hf := fieldEvaluation_smooth C B 0 ω Y hω
  refine ⟨hf, ?_⟩
  intro p
  have hωeq := scalarField_fieldEvaluation_zero ω (fun i => (Y i).val)
  have hd := exteriorDerivative_eq_proof h_unique C 0
    (FormPullbackData.scalarField S f)
    (fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
      (dFunction S f hf p)) (h_function C f hf)
  change FormPullbackData.scalarField S f = ω at hωeq
  rw [hωeq] at hd
  change evaluate (TangentSpace S p) 0
    ((evaluationEquiv C.tangent.fiberCoordinates p 0).symm
      ((evaluate (TangentSpace S p) 1 (exteriorDerivative C 0 ω p)).curryLeft (X.val p)))
      (fun i => (Y i).val p) = _
  rw [← evaluationEquiv_apply C.tangent.fiberCoordinates p 0,
    LinearEquiv.apply_symm_apply, AlternatingMap.curryLeft_apply_apply,
    hd, evaluate_degree_one, LinearEquiv.apply_symm_apply]
  exact (scalarAction_eq_dFunction X.val f hf p).symm



/-- Restricting the set of base points preserves the actual flow derivative. -/
theorem hasFlowLieDerivativeOn_mono {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (F : CurveFamily M) (k : ℕ) (ω η : Field S k) {O P : Set M}
    (h : HasFlowLieDerivativeOn C F k ω η P) (hOP : O ⊆ P) :
    HasFlowLieDerivativeOn C F k ω η O := by
  intro c hc p hp hpO I
  exact h c hc p hp (hOP hpO) I

/-- Maximal boundaryless flow data supply the local flow predicate everywhere. -/
theorem isLocalFlowOn_univ_boundaryless {n : ℕ} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n .euclidean M}
    {B : TangentBundleStructure S} (X : SmoothField B) (F : CurveFamily M)
    (hF : MaximalFlowData.IsMaximalFamily X F) : IsLocalFlowOn X F univ := by
  refine ⟨isOpen_univ, ?_⟩
  intro p _
  refine ⟨(hF p).1, (hF p).2.1, (hF p).2.2.1, ?_⟩
  intro t ht
  exact (MaximalFlow.domain_open_smooth S B X F hF).2 (t, p) ht

/-- Tangent-boundary maximal flow data supply the local flow predicate everywhere. -/
theorem isLocalFlowOn_univ_boundary {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {B : TangentBundleStructure S} (X : SmoothField B)
    (hX : BoundaryFlowData.IsTangentToBoundary X) (F : CurveFamily M)
    (hF : BoundaryFlowData.IsMaximalFamily X F) : IsLocalFlowOn X F univ := by
  refine ⟨isOpen_univ, ?_⟩
  intro p _
  refine ⟨(hF p).1, (hF p).2.1, (hF p).2.2.1, ?_⟩
  intro t ht
  exact (BoundaryTangentFlow.domain_open_smooth S B X hX F hF).2 (t, p) ht

/-- The choice operator is identified once its actual pullback derivative is known. -/
theorem flowLieDerivative_eq_of_hasDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (F : CurveFamily M) (k : ℕ) (ω η : Field S k)
    (hη : HasFlowLieDerivativeOn C F k ω η univ) :
    HasFlowLieDerivativeOn C F k ω (flowLieDerivative C F k ω) univ ∧
      flowLieDerivative C F k ω = η := by
  have hex : ∃ ζ, HasFlowLieDerivativeOn C F k ω ζ univ := ⟨η, hη⟩
  have hchoice : HasFlowLieDerivativeOn C F k ω (flowLieDerivative C F k ω) univ := by
    simpa only [flowLieDerivative, dite_eq_left hex] using Classical.choose_spec hex
  refine ⟨hchoice, funext (fun p => ?_)⟩
  exact flowLieDerivative_unique C F k ω _ η univ hchoice hη p (mem_univ p)

/-- Once the local theorem has been proved, the global boundaryless theorem
follows from maximal-flow regularity and uniqueness of the actual derivative. -/
theorem flow_boundaryless_of_local_flow
    (hloc : Specs.SmoothManifolds.Ch07.Cartan.local_flowType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.flow_boundarylessType.{u} := by
  intro n M _ S C B X F hF k ω hω
  exact flowLieDerivative_eq_of_hasDerivative C F k ω _
    (hloc C B X F univ (isLocalFlowOn_univ_boundaryless X F hF) k ω hω)

/-- The same reduction applies with precisely tangency of the generating field. -/
theorem flow_boundary_of_local_flow
    (hloc : Specs.SmoothManifolds.Ch07.Cartan.local_flowType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.flow_boundaryType.{u} := by
  intro n a M _ S C B X hX F hF k ω hω
  exact flowLieDerivative_eq_of_hasDerivative C F k ω _
    (hloc C B X F univ (isLocalFlowOn_univ_boundary X hX F hF) k ω hω)

/-- Genuine time-map differentials exist under the actual local joint smoothness
hypothesis; their total choice definition agrees with that differential. -/
theorem timeDifferential_spec {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (p : M) (hsm : BoundaryFlowData.FlowSmoothAt S F (t, p)) :
    IsDifferential S S (fun q => F.curve q t) p (timeDifferential S F t p) := by
  have hex : ∃ L, IsDifferential S S (fun q => F.curve q t) p L :=
    (BracketFromFlow.differentialAt_exists S S (fun q => F.curve q t) p
      (BracketFromFlow.timeMap_smoothAt S F t p hsm)).exists
  simpa only [timeDifferential, dite_eq_left hex] using Classical.choose_spec hex

/-- Pointwise evaluation of actual flow pullback uses the forward differential,
whose target is the moving tangent fiber. -/
theorem flowPullback_apply {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (k : ℕ) (ω : Field S k) (p : M) (v : Fin k → TangentSpace S p) :
    evaluate (TangentSpace S p) k (flowPullback S F t k ω p) v =
      evaluate (TangentSpace S (F.curve p t)) k (ω (F.curve p t))
        (fun i => timeDifferential S F t p (v i)) := by
  exact FormPullbackResults.pullback_apply S S (fun q => F.curve q t)
    (timeDifferential S F t) k ω p v

/-- On functions flow pullback is exactly composition, even before existence of
a time-map differential has been established. -/
theorem flowPullback_scalarField {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (f : M → ℝ) :
    flowPullback S F t 0 (FormPullbackData.scalarField S f) =
      FormPullbackData.scalarField S (fun p => f (F.curve p t)) := by
  exact FormPullbackResults.pullback_zero_proof S S (fun q => F.curve q t)
    (timeDifferential S F t) f

/-- An integral curve differentiates every actual smooth germ by its generating
point derivation. This uses only the chart ODE and the scalar chain rule. -/
theorem integralCurve_scalar_derivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {B : TangentBundleStructure S} (X : SmoothField B) {I : Set ℝ}
    (hI : IsOpen I) (γ : ℝ → M) (hγ : BoundaryFlowData.IsIntegralCurveOn X I γ)
    (t : ℝ) (ht : t ∈ I) (g : SmoothGerm S (γ t)) (f : M → ℝ)
    (hf : Germ.ofFun f = g.val) :
    HasDerivAt (fun s => f (γ s)) ((X.val (γ t)).val g) t := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ t)
  obtain ⟨H, ⟨U, hU, hpU, hH⟩, heH⟩ := exists_germChartExtension S (γ t) e he hp g
  have hHd : DifferentiableAt ℝ H (e (γ t)).val :=
    (hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hpath := hHd.hasFDerivAt.comp_hasDerivAt t (hγ.2 t ht e he hp).2
  have heq : (fun s => H (e (γ s)).val) =ᶠ[𝓝 t] (fun s => f (γ s)) :=
    (Germ.coe_eq.mp (heH.trans hf.symm)).comp_tendsto
      (hγ.1.continuousAt (hI.mem_nhds ht))
  have haction : (X.val (γ t)).val g =
      fderiv ℝ H (e (γ t)).val
        (B.fiberCoordinates.equiv e he (γ t) hp (X.val (γ t))) := by
    rw [derivation_coordinate_formula S (γ t) e he hp (X.val (γ t)) g H
      ⟨⟨U, hU, hpU, hH⟩, heH⟩]
    let w := B.fiberCoordinates.equiv e he (γ t) hp (X.val (γ t))
    have hw : w = ∑ i, w i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    change _ = fderiv ℝ H (e (γ t)).val w
    rw [hw, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, ← LieBrackets.coordinates_eval (B := B) e he (γ t) hp]
  exact (hpath.congr_of_eventuallyEq heq.symm).congr_deriv haction.symm

/-- Above the dimension every ordered-wedge coefficient index is impossible,
so the coefficient definition of a flow derivative is automatically satisfied. -/
theorem hasFlowLieDerivativeOn_of_dimension_lt {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (F : CurveFamily M) (k : ℕ) (hk : n < k) (ω η : Field S k) (O : Set M) :
    HasFlowLieDerivativeOn C F k ω η O := by
  intro c hc p hp hpO I
  have hle := Fintype.card_le_of_injective
    (Set.powersetCard.ofFinEmbEquiv.symm I)
    (Set.powersetCard.ofFinEmbEquiv.symm I).injective
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using hle
  exact False.elim ((Nat.not_le_of_gt hk) hkn)



/-- Every vector in an intrinsic tangent fiber is the value of a global smooth
field, obtained by multiplying a constant local coordinate field by a bump. -/
theorem smoothField_exists_value
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (p : M) (v : TangentSpace S p) :
    ∃ X : SmoothField B, X.val p = v := by
  classical
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨f, hf, hf01, hfp, hfs, hfcp⟩ :=
    exists_local_bump S p e.source e.open_source hp
  let w := B.fiberCoordinates.equiv e he p hp v
  let X : Section S := fun q => if hq : q ∈ e.source then
    (B.fiberCoordinates.equiv e he q hq).symm (f q • w) else 0
  have hX : letI := B.topology
      IsSmoothMap S B.manifold (fun q => ⟨q, X q⟩) := by
    letI := B.topology
    intro q
    by_cases hq : q ∈ e.source
    · apply VectorFields.section_smoothAt_of_coordinates S B X q e he hq
        e.source e.open_source hq (fun _ h => h) (fun z => f z • w)
      · apply VectorFields.vectorSmoothAt_of_components S
        exact fun i => ScalarContDiffAt.mul (hf q)
          (ScalarContDiffAt.const (⊤ : ℕ∞) S.smoothStructure.val (w i) q)
      · intro z hz
        simp only [X, dite_eq_left hz, LinearEquiv.apply_symm_apply]
    · obtain ⟨d, hd, hqd⟩ := S.smoothStructure.property.1.1 q
      have hqf : q ∉ sectionSupport f := fun h => hq (hfs h)
      apply VectorFields.section_smoothAt_of_coordinates S B X q d hd hqd
        (d.source ∩ (sectionSupport f)ᶜ)
        (d.open_source.inter isClosed_closure.isOpen_compl) ⟨hqd, hqf⟩
        (fun _ h => h.1) (fun _ => 0)
      · apply VectorFields.vectorSmoothAt_of_components S
        exact fun i => ScalarContDiffAt.const (⊤ : ℕ∞) S.smoothStructure.val 0 q
      · intro z hz
        have hfz : f z = 0 := by
          by_contra h
          exact hz.2 (subset_closure h)
        simp only [X, hfz, zero_smul]
        split_ifs <;> simp only [map_zero]
  refine ⟨⟨X, hX⟩, ?_⟩
  change X p = v
  simp only [X, dite_eq_left hp, hfp.eq_of_nhds, one_smul, w,
    LinearEquiv.symm_apply_apply]

/-- The last Cartan commutator follows algebraically from the first two,
with the degree-zero case retaining only the contraction-differential term. -/
theorem lie_commutes_lie_of_contraction
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (hops : Specs.SmoothManifolds.Ch07.Cartan.operators_smoothType.{u})
    (hd : Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_dType.{u})
    (hi : Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_contractionType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_lieType.{u} := by
  intro n a M _ S C B b hb X Y k ω hω
  have hdω := (hops C B X k ω hω).2.1
  have hXdω := sub_eq_zero.mp (hd C B X k ω hω)
  cases k with
  | zero =>
    have hh := hi C B b hb X Y 1 (exteriorDerivative C 0 ω) hdω
    rw [hXdω] at hh
    simpa only [Nat.reduceSub, lieDerivative] using hh
  | succ k =>
    have hiω := (hops C B Y (k+1) ω hω).2.2.1
    have hdiω := (hops C B X k _ hiω).2.1
    have hidω := (hops C B Y (k+1+1) _ hdω).2.2.1
    have hXω := (hops C B X (k+1) ω hω).2.2.2
    have hiXω := (hops C B Y (k+1) _ hXω).2.2.1
    have hiBω := (hops C B (b X Y) (k+1) ω hω).2.2.1
    have hXdiω := sub_eq_zero.mp (hd C B X k _ hiω)
    have hXiω := (sub_eq_iff_eq_add.mp (hi C B b hb X Y (k+1) ω hω))
    have hXidω := (sub_eq_iff_eq_add.mp (hi C B b hb X Y (k+1+1) _ hdω))
    let I : Field S k := contraction C Y.val (k+1) ω
    let J : Field S k := contraction C (b X Y).val (k+1) ω
    let K : Field S k := contraction C Y.val (k+1) (lieDerivative C X.val (k+1) ω)
    let A : Field S (k+1) := exteriorDerivative C k I
    let E : Field S (k+1) := contraction C Y.val (k+1+1) (exteriorDerivative C (k+1) ω)
    let F : Field S (k+1) := contraction C Y.val (k+1+1)
      (exteriorDerivative C (k+1) (lieDerivative C X.val (k+1) ω))
    let G : Field S (k+1) := contraction C (b X Y).val (k+1+1) (exteriorDerivative C (k+1) ω)
    let H : Field S (k+1) := contraction C Y.val (k+1+1)
      (lieDerivative C X.val (k+1+1) (exteriorDerivative C (k+1) ω))
    have hI : lieDerivative C X.val k I = J+K := hXiω
    have hA : lieDerivative C X.val (k+1) A =
        exteriorDerivative C k (lieDerivative C X.val k I) := hXdiω
    have hE : lieDerivative C X.val (k+1) E = G+H := hXidω
    have hH : H = F := congrArg (fun η => contraction C Y.val (k+1+1) η) hXdω
    change lieDerivative C X.val (k+1) (A+E) -
      (exteriorDerivative C k K + F) = exteriorDerivative C k J + G
    rw [lieDerivative_add h_exists h_coords h_unique C B X (k+1) A E hdiω hidω,
      hA, hI, hE, hH,
      exteriorDerivative_add h_exists h_coords h_unique C B k J K hiBω hiXω]
    abel

/-- Testing on global smooth fields detects all original exterior-fiber values. -/
theorem field_ext_of_evaluation_smooth
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (α β : Field S k)
    (h : ∀ Y : Fin k → SmoothField C.tangent, ∀ p,
      fieldEvaluation k α (fun i => (Y i).val) p =
        fieldEvaluation k β (fun i => (Y i).val) p) : α = β := by
  classical
  funext p
  apply (evaluationEquiv C.tangent.fiberCoordinates p k).injective
  apply AlternatingMap.ext
  intro v
  choose Y hY using fun i => smoothField_exists_value C.tangent p (v i)
  simpa only [fieldEvaluation, evaluationEquiv_apply, hY] using h Y p

/-- First-slot contraction evaluated on a tuple of fields. -/
theorem fieldEvaluation_contraction
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (Y : SmoothField C.tangent) (k : ℕ) (ω : Field S (k+1))
    (Z : Fin k → SmoothField C.tangent) :
    fieldEvaluation k (contraction C Y.val (k+1) ω) (fun i => (Z i).val) =
      fieldEvaluation (k+1) ω (fun i => (Matrix.vecCons Y Z i).val) := by
  funext p
  rw [fieldEvaluation, contraction_apply_proof]
  change evaluate (TangentSpace S p) (k+1) (ω p) _ =
    evaluate (TangentSpace S p) (k+1) (ω p) _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem fieldEvaluation_sub
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (k : ℕ) (α β : Field S k)
    (Z : Fin k → Section S) :
    fieldEvaluation k (α-β) Z = fieldEvaluation k α Z - fieldEvaluation k β Z := by
  funext p
  simp [fieldEvaluation]

/-- The contraction commutator is a formal consequence of the full invariant
Lie evaluation formula, including degree zero. -/
theorem lie_commutes_contraction_of_evaluation
    (hzero : Specs.SmoothManifolds.Ch07.Cartan.exteriorDerivative_zeroType.{u})
    (hops : Specs.SmoothManifolds.Ch07.Cartan.operators_smoothType.{u})
    (heval : Specs.SmoothManifolds.Ch07.Cartan.lie_evaluationType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_contractionType.{u} := by
  classical
  intro n a M _ S C B b hb X Y k ω hω
  cases k with
  | zero =>
    change lieDerivative C X.val 0 (0 : Field S 0) - 0 = 0
    rw [sub_zero]
    change contraction C X.val 1 (exteriorDerivative C 0 0) = 0
    rw [hzero C 0, contraction_map_zero]
  | succ k =>
    apply field_ext_of_evaluation_smooth C k
    intro Z p
    have hiω := (hops C B Y (k+1) ω hω).2.2.1
    have h1 := (heval C B b hb X k (contraction C Y.val (k+1) ω) Z hiω).2 p
    have h2 := (heval C B b hb X (k+1) ω (Matrix.vecCons Y Z) hω).2 p
    rw [fieldEvaluation_contraction C Y k ω Z] at h1
    simp only [fieldEvaluation_sub, Pi.sub_apply]
    rw [fieldEvaluation_contraction C Y k (lieDerivative C X.val (k+1) ω) Z]
    rw [fieldEvaluation_contraction C (b X Y) k ω Z]
    have hs : (∑ i : Fin (k+1), fieldEvaluation (k+1) ω
        (fun j => (Function.update (Matrix.vecCons Y Z) i (b X (Matrix.vecCons Y Z i)) j).val) p) =
      fieldEvaluation (k+1) ω (fun i => (Matrix.vecCons (b X Y) Z i).val) p +
      ∑ i : Fin k, fieldEvaluation k (contraction C Y.val (k+1) ω)
        (fun j => (Function.update Z i (b X (Z i)) j).val) p := by
      rw [Fin.sum_univ_succ]
      congr 1
      · congr 2
        funext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp
      · apply Finset.sum_congr rfl
        intro i hi
        rw [fieldEvaluation_contraction C Y k ω (Function.update Z i (b X (Z i)))]
        congr 2
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
          rfl
        · simp [Function.update_apply]
    rw [hs] at h2
    change fieldEvaluation k (lieDerivative C X.val k (contraction C Y.val (k+1) ω))
      (fun i => (Z i).val) p -
      fieldEvaluation (k+1) (lieDerivative C X.val (k+1) ω)
        (fun i => (Matrix.vecCons Y Z i).val) p =
      fieldEvaluation (k+1) ω (fun i => (Matrix.vecCons (b X Y) Z i).val) p
    rw [h1, h2]
    abel


/-- The Lie-Lie identity on functions follows from the actual derivation bracket,
without requiring the positive-degree Cartan evaluation theorem. -/
theorem lie_commutes_lie_degree_zero
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : LieBracketData.BracketOperation b) (X Y : SmoothField C.tangent)
    (ω : Field S 0) (hω : IsForm (B 0) ω) :
    lieDerivative C X.val 0 (lieDerivative C Y.val 0 ω) -
      lieDerivative C Y.val 0 (lieDerivative C X.val 0 ω) = lieDerivative C (b X Y).val 0 ω := by
  have hX := (operators_smooth_proof h_exists h_coords h_unique C B X 0 ω hω).2.2.2
  have hY := (operators_smooth_proof h_exists h_coords h_unique C B Y 0 ω hω).2.2.2
  apply field_ext_of_evaluation_smooth C 0
  intro Z p
  have hf := (lie_evaluation_degree_zero h_unique h_function C B X ω Z hω).1
  have heX : fieldEvaluation 0 (lieDerivative C X.val 0 ω) (fun i => (Z i).val) =
      scalarAction X.val (fieldEvaluation 0 ω (fun i => (Z i).val)) := by
    funext q
    exact (lie_evaluation_degree_zero h_unique h_function C B X ω Z hω).2 q
  have heY : fieldEvaluation 0 (lieDerivative C Y.val 0 ω) (fun i => (Z i).val) =
      scalarAction Y.val (fieldEvaluation 0 ω (fun i => (Z i).val)) := by
    funext q
    exact (lie_evaluation_degree_zero h_unique h_function C B Y ω Z hω).2 q
  rw [fieldEvaluation_sub, Pi.sub_apply,
    (lie_evaluation_degree_zero h_unique h_function C B X _ Z hY).2 p,
    (lie_evaluation_degree_zero h_unique h_function C B Y _ Z hX).2 p,
    (lie_evaluation_degree_zero h_unique h_function C B (b X Y) ω Z hω).2 p,
    heX, heY]
  exact (scalarAction_bracket C b hb X Y _ hf p).symm


/-- The unique empty wedge has coefficient equal to its scalar value. -/
theorem coefficients_scalarField_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) (p : c.source) (I : Index n 0) :
    coefficients C 0 c hc (FormPullbackData.scalarField S f) p I = f p.val := by
  letI : Subsingleton (Index n 0) := ⟨fun J K => Subtype.ext (by
    exact (Finset.card_eq_zero.mp J.property).trans (Finset.card_eq_zero.mp K.property).symm)⟩
  letI : Unique (Index n 0) := ⟨⟨I⟩, fun J => Subsingleton.elim J I⟩
  have h := fieldEvaluation_coordinates C 0 (FormPullbackData.scalarField S f)
    (fun i => Fin.elim0 i) c hc p
  simp only [Matrix.det_isEmpty, mul_one, Finset.univ_unique, Finset.sum_singleton] at h
  rw [fieldEvaluation, evaluate_degree_zero] at h
  have he : (default : Index n 0) = I := Subsingleton.elim _ _
  simpa only [FormPullbackData.scalarField, LinearEquiv.apply_symm_apply, he] using h.symm



/-- A genuine local flow differentiates scalar pullback by the intrinsic
point-derivation action of its generating field. -/
theorem localFlow_scalar_derivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {B : TangentBundleStructure S} (X : SmoothField B) (F : CurveFamily M)
    (O : Set M) (hF : IsLocalFlowOn X F O) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M) (hpO : p ∈ O) :
    HasDerivAt (fun t => f (F.curve p t)) (scalarAction X.val f p) 0 := by
  obtain ⟨hzero, hinit, hcurve, hsm⟩ := hF.2 p hpO
  have hder := integralCurve_scalar_derivative X (F.interval p).isOpen
    (F.curve p) hcurve 0 hzero (functionGerm S f hf (F.curve p 0)) f rfl
  rw [← scalarAction_eq_germ X.val f (F.curve p 0)
    (functionGerm S f hf (F.curve p 0)) rfl, hinit] at hder
  exact hder

/-- The full ordered-wedge coefficient flow derivative in degree zero. -/
theorem localFlow_scalarField_hasDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : SmoothField C.tangent) (F : CurveFamily M) (O : Set M)
    (hF : IsLocalFlowOn X F O) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) :
    HasFlowLieDerivativeOn C F 0 (FormPullbackData.scalarField S f)
      (FormPullbackData.scalarField S (scalarAction X.val f)) O := by
  intro c hc p hp hpO I
  simpa only [flowPullback_scalarField, coefficients_scalarField_zero] using
    localFlow_scalar_derivative X F O hF f hf p hpO


/-- The local-flow Cartan identity in degree zero, for every smooth form on
either ordinary model. No tangency hypothesis is needed at an actual local flow. -/
theorem local_flow_degree_zero
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (F : CurveFamily M) (O : Set M)
    (hF : IsLocalFlowOn X F O) (ω : Field S 0) (hω : IsForm (B 0) ω) :
    HasFlowLieDerivativeOn C F 0 ω (lieDerivative C X.val 0 ω) O := by
  let Y : Fin 0 → SmoothField C.tangent := fun i => Fin.elim0 i
  let f := fieldEvaluation 0 ω (fun i => (Y i).val)
  have heval := lie_evaluation_degree_zero h_unique h_function C B X ω Y hω
  have hωeq := scalarField_fieldEvaluation_zero ω (fun i => (Y i).val)
  change FormPullbackData.scalarField S f = ω at hωeq
  have hηeq : FormPullbackData.scalarField S (scalarAction X.val f) =
      lieDerivative C X.val 0 ω := by
    have heFun : fieldEvaluation 0 (lieDerivative C X.val 0 ω) (fun i => (Y i).val) =
        scalarAction X.val f := funext heval.2
    rw [← heFun]
    exact scalarField_fieldEvaluation_zero (lieDerivative C X.val 0 ω) (fun i => (Y i).val)
  have hflow := localFlow_scalarField_hasDerivative C X F O hF f heval.1
  rw [hωeq, hηeq] at hflow
  exact hflow


section ModelCalculus
open ContinuousAlternatingMap
set_option backward.isDefEq.respectTransparency false

/-- Differentiating the scalar evaluation of a first-slot contraction. -/
theorem fderiv_contraction_evaluation {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ω : E → E [⋀^Fin (k+1)]→L[ℝ] ℝ} {X : E → E} {x : E}
    (hω : DifferentiableAt ℝ ω x) (hX : DifferentiableAt ℝ X x)
    (v : Fin k → E) (dx : E) :
    fderiv ℝ (fun y => ω y (Fin.cons (X y) v)) x dx =
      fderiv ℝ ω x dx (Fin.cons (X x) v) +
        ω x (Fin.cons (fderiv ℝ X x dx) v) := by
  have hg (i : Fin (k+1)) : DifferentiableAt ℝ (fun y => (Fin.cons (X y) v : Fin (k+1) → E) i) x := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hX
    · exact differentiableAt_const (v j)
  rw [fderiv_continuousAlternatingMap_apply_apply hω hg dx]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have htail : ∑ i : Fin k,
      ω x (Function.update (Fin.cons (X x) v : Fin (k+1) → E) i.succ
        (fderiv ℝ (fun y => (Fin.cons (X y) v : Fin (k+1) → E) i.succ) x dx)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp
  simp only [Fin.cons_succ] at htail
  rw [htail, add_zero]
  congr 2
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- The local Cartan sum in a fixed normed vector space has the usual
coefficient derivative plus one derivative of the field in each slot. -/
theorem model_cartan_evaluation {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ω : E → E [⋀^Fin (k+1)]→L[ℝ] ℝ} {X : E → E} {x : E}
    (hω : DifferentiableAt ℝ ω x) (hX : DifferentiableAt ℝ X x)
    (hc : DifferentiableAt ℝ (fun y => (ω y).curryLeft (X y)) x)
    (v : Fin (k+1) → E) :
    extDeriv (fun y => (ω y).curryLeft (X y)) x v +
      extDeriv ω x (Fin.cons (X x) v) =
    fderiv ℝ ω x (X x) v +
      ∑ i : Fin (k+1), ω x (Function.update v i (fderiv ℝ X x (v i))) := by
  rw [extDeriv_apply hc, extDeriv_apply hω]
  conv_lhs => arg 2; rw [Fin.sum_univ_succ]
  simp only [Fin.removeNth_zero, Fin.cons_zero, pow_zero, one_smul,
    Fin.cons_succ, Fin.val_succ, pow_succ, smul_neg, neg_smul,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  have hremove (i : Fin (k+1)) :
      i.succ.removeNth (Fin.cons (X x) v : Fin (k+2) → E) =
        (Fin.cons (X x) (i.removeNth v) : Fin (k+1) → E) := by
    exact Fin.cons_comp_succ_succAbove (X x) v i
  simp only [Matrix.vecCons, Fin.tail_cons, Fin.val_zero, pow_zero, one_smul]
  simp_rw [hremove]
  simp only [fderiv_contraction_evaluation hω hX,
    fderiv_continuousAlternatingMap_apply_const_apply hω]
  have hs (i : Fin (k+1)) :
      (-1 : ℤ)^i.val • ω x (Fin.cons (fderiv ℝ X x (v i)) (i.removeNth v)) =
        ω x (Function.update v i (fderiv ℝ X x (v i))) := by
    have hi := Fin.insertNth_removeNth i (fderiv ℝ X x (v i)) v
    rw [← hi, ContinuousAlternatingMap.map_insertNth]
    simp [smul_smul, ← pow_add, ← two_mul, Matrix.vecCons]
  simp only [smul_add, Finset.sum_add_distrib, hs]
  simp only [mul_neg_one, neg_smul, Finset.sum_neg_distrib]
  ring

/-- Cartan's local expression has the invariant Lie evaluation formula on a
normed vector space, with the ordinary vector-field commutator. -/
theorem model_lie_evaluation {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ω : E → E [⋀^Fin (k+1)]→L[ℝ] ℝ} {X : E → E} {x : E}
    (hω : DifferentiableAt ℝ ω x) (hX : DifferentiableAt ℝ X x)
    (hc : DifferentiableAt ℝ (fun y => (ω y).curryLeft (X y)) x)
    (Y : Fin (k+1) → E → E) (hY : ∀ i, DifferentiableAt ℝ (Y i) x) :
    extDeriv (fun y => (ω y).curryLeft (X y)) x (fun i => Y i x) +
      extDeriv ω x (Fin.cons (X x) (fun i => Y i x)) =
    fderiv ℝ (fun y => ω y (fun i => Y i y)) x (X x) -
      ∑ i : Fin (k+1), ω x (Function.update (fun j => Y j x) i
        (VectorField.lieBracket ℝ X (Y i) x)) := by
  rw [model_cartan_evaluation hω hX hc,
    fderiv_continuousAlternatingMap_apply_apply hω hY]
  simp only [VectorField.lieBracket, ContinuousAlternatingMap.map_update_sub,
    Finset.sum_sub_distrib]
  ring

end ModelCalculus

/-- The intrinsic bracket is the ordinary model bracket of any actual smooth
coordinate representatives, including at boundary points. -/
theorem bracket_coordinates_of_extensions {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : LieBracketData.BracketOperation b) (X Y : SmoothField C.tangent)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (FX FY : Euclidean n → Euclidean n)
    (hFX : DifferentiableAt ℝ FX (c p).val) (hFY : DifferentiableAt ℝ FY (c p).val)
    (heX : (fun q => FX (c q).val) =ᶠ[𝓝 p] LieBracketData.coefficients C.tangent X.val c hc)
    (heY : (fun q => FY (c q).val) =ᶠ[𝓝 p] LieBracketData.coefficients C.tangent Y.val c hc) :
    C.tangent.fiberCoordinates.equiv c hc p hp ((b X Y).val p) =
      VectorField.lieBracket ℝ FX FY (c p).val := by
  have hL : FiniteRegularityData.HasCoordinateDerivative c
      (LieBracketData.coefficients C.tangent X.val c hc) p (fderiv ℝ FX (c p).val) :=
    ⟨FX, hFX.hasFDerivAt, heX⟩
  have hK : FiniteRegularityData.HasCoordinateDerivative c
      (LieBracketData.coefficients C.tangent Y.val c hc) p (fderiv ℝ FY (c p).val) :=
    ⟨FY, hFY.hasFDerivAt, heY⟩
  have hbr := (LieBrackets.bracket_coordinates S C.tangent b hb X Y).2
    c hc p hp (fderiv ℝ FX (c p).val) (fderiv ℝ FY (c p).val) hL hK
  rw [← LieBrackets.coefficients_eq (B := C.tangent) (b X Y).val c hc p hp]
  funext j
  rw [VectorField.lieBracket, heX.eq_of_nhds, heY.eq_of_nhds,
    LieBrackets.coordinate_commutator_sum]
  exact hbr j

/-- In an actual chart, an eventual coordinate representative can be restricted
so that it represents every chart point whose coordinates lie in the new open set. -/
theorem chart_extension_of_eventual {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ModelChart n a M) (p : M) (hp : p ∈ c.source) (r : ℕ∞)
    (f : M → V) (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (F : Euclidean n → V) (hF : ContDiffOn ℝ r F U)
    (he : (fun q => F (c q).val) =ᶠ[𝓝 p] f) :
    HasLocalContDiffExtensionAt r (fun q : c.source => (c q.val).val)
      (fun q => f q.val) ⟨p, hp⟩ := by
  have hgood : {q | q ∈ c.source ∧ F (c q).val = f q} ∈ 𝓝 p :=
    Filter.inter_mem (c.open_source.mem_nhds hp) he
  obtain ⟨A, hAs, hA, hpA⟩ := mem_nhds_iff.mp hgood
  have hAc : A ⊆ c.source := fun q hq => (hAs hq).1
  have hImage : IsOpen (c '' A) := c.isOpen_image_of_subset_source hA hAc
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hImage
  have hpW : (c p).val ∈ W := by
    change c p ∈ Subtype.val ⁻¹' W
    rw [hWeq]
    exact ⟨p, hpA, rfl⟩
  refine ⟨U ∩ W, hU.inter hW, ⟨hpU, hpW⟩, F, hF.mono inter_subset_left, ?_⟩
  intro q hq
  have hqI : c q.val ∈ c '' A := by
    rw [← hWeq]
    exact hq.2
  obtain ⟨y, hyA, hyq⟩ := hqI
  have hy : y = q.val := c.injOn (hAc hyA) q.property hyq
  simpa only [hy] using (hAs hyA).2

/-- Smooth vector fields have uniform ambient coefficient representatives in
any chart, at every requested finite or smooth order. -/
theorem field_coordinates_regular {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : SmoothField C.tangent) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (r : ℕ∞) :
    LocallyContDiffAlong r (fun q : c.source => (c q.val).val)
      (fun q => C.tangent.fiberCoordinates.equiv c hc q.val q.property (X.val q.val)) := by
  intro p
  obtain ⟨U, hU, hpU, F, hF, he⟩ :=
    VectorFields.field_local_coordinates S C.tangent X p.val c hc p.property
  have he' : (fun q => F (c q).val) =ᶠ[𝓝 p.val]
      LieBracketData.coefficients C.tangent X.val c hc := by
    filter_upwards [he] with q hq
    obtain ⟨hqs, hqeq⟩ := hq
    rw [hqeq, LieBrackets.coefficients_eq (B := C.tangent) X.val c hc q hqs]
  obtain ⟨V, hV, hpV, H, hH, hHe⟩ := chart_extension_of_eventual c p.val p.property r
    (LieBracketData.coefficients C.tangent X.val c hc) U hU hpU F (hF.of_le (by simp)) he'
  refine ⟨V, hV, hpV, H, hH, ?_⟩
  intro q hq
  rw [hHe q hq]
  exact LieBrackets.coefficients_eq (B := C.tangent) X.val c hc q.val q.property


theorem exterior_regrade_coe {V : Type u} [AddCommGroup V] [Module ℝ V]
    {k l : ℕ} (h : k=l) (x : ⋀[ℝ]^k V) :
    ((Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h : ⋀[ℝ]^l V) : ExteriorAlgebra ℝ V) = x := by
  cases h
  rfl

theorem wedge_one_cons {V : Type u} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (α : V) (β : Fin k → V) :
    (exteriorPower.wedge ℝ V 1 k ((exteriorPower.oneEquiv ℝ V).symm α)
      (exteriorPower.ιMulti ℝ k β) : ExteriorAlgebra ℝ V) =
    (exteriorPower.ιMulti ℝ (k+1) (Matrix.vecCons α β) : ExteriorAlgebra ℝ V) := by
  change ExteriorAlgebra.ιMulti ℝ 1 (fun _ => α) * ExteriorAlgebra.ιMulti ℝ k β = _
  simp [ExteriorAlgebra.ιMulti_succ_apply]

theorem continuousLinearMap_coordinate_expansion {n : ℕ} (A : Euclidean n →L[ℝ] ℝ) :
    A.toLinearMap = ∑ j : Fin n, A (Pi.single j 1) • (Pi.basisFun ℝ (Fin n)).dualBasis j := by
  classical
  apply LinearMap.ext
  intro v
  have hv : v = ∑ j : Fin n, v j • Pi.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  change A v = _
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]

theorem coordinateExpression_as_sum
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    coordinateExpression C k c hc p hp A =
      ∑ I : Index n k, exteriorPower.ιMulti ℝ (k+1)
        (Matrix.vecCons ((A I).toLinearMap.comp
          (C.tangent.fiberCoordinates.equiv c hc p hp).toLinearMap)
          (fun j => coordinateCovector C.tangent.fiberCoordinates c hc p hp
            (Set.powersetCard.ofFinEmbEquiv.symm I j))) := by
  classical
  apply Subtype.ext
  rw [coordinateExpression, exterior_regrade_coe]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [wedge_one_cons]
  have hA : (A I).toLinearMap.comp (C.tangent.fiberCoordinates.equiv c hc p hp).toLinearMap =
      ∑ j : Fin n, A I (Pi.single j 1) •
        coordinateCovector C.tangent.fiberCoordinates c hc p hp j := by
    rw [continuousLinearMap_coordinate_expansion]
    ext v
    simp [coordinateCovector]
  rw [hA]
  change (∑ j, A I (Pi.single j 1) •
    ExteriorAlgebra.ιMulti ℝ (k+1) (Matrix.vecCons
      (coordinateCovector C.tangent.fiberCoordinates c hc p hp j)
      (fun j => coordinateCovector C.tangent.fiberCoordinates c hc p hp
        (Set.powersetCard.ofFinEmbEquiv.symm I j)))) = _
  simp only [exteriorPower.ιMulti_apply_coe]
  simp_rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp only [Matrix.cons_val_zero, Matrix.tail_cons,
    map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]

theorem coordinateExpression_evaluation
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (A : Index n k → Euclidean n →L[ℝ] ℝ)
    (v : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1) (coordinateExpression C k c hc p hp A) v =
      evaluate (Euclidean n) (k+1) (∑ I : Index n k,
        exteriorPower.ιMulti ℝ (k+1)
          (Matrix.vecCons (A I).toLinearMap (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
            (Set.powersetCard.ofFinEmbEquiv.symm I j))))
        (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
  classical
  rw [coordinateExpression_as_sum]
  simp only [map_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro I hI
  rw [ExteriorAlgebraResults.determinant_normalization,
    ExteriorAlgebraResults.determinant_normalization]
  congr 2
  ext i j
  refine Fin.cases ?_ (fun l => ?_) i
  · rfl
  · simp [coordinateCovector]

theorem coefficient_alternating_derivative_of_equiv
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (n k : ℕ)
    (e : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (heval : ∀ (α : Index n k → ℝ) (v : Fin k → Euclidean n),
      e α v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm α) v)
    (F : Euclidean n → Index n k → ℝ) (x : Euclidean n)
    (hF : DifferentiableAt ℝ F x) (v : Fin (k+1) → Euclidean n) :
    extDeriv (fun y => e (F y)) x v =
      evaluate (Euclidean n) (k+1) (∑ I : Index n k,
        exteriorPower.ιMulti ℝ (k+1)
          (Matrix.vecCons (fderiv ℝ (fun y => F y I) x).toLinearMap
            (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
              (Set.powersetCard.ofFinEmbEquiv.symm I j)))) v := by
  obtain ⟨e', heval', hd⟩ := h_bridge n k
  have he : e = e' := by
    apply DFunLike.ext
    intro α
    apply ContinuousAlternatingMap.ext
    intro v
    exact (heval α v).trans (heval' α v).symm
  subst e'
  exact hd F x hF v

theorem selected_exteriorDerivative_eq_extDeriv_of_extension
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (k : ℕ) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (hω : IsForm (B k) ω) (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean n)) (F : Euclidean n → Index n k → ℝ)
    (hU : IsOpen U) (hpU : (c p).val ∈ U) (hF : ContDiffOn ℝ 1 F U)
    (heq : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F z.val I = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I)
    (e : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (heval : ∀ (α : Index n k → ℝ) (v : Fin k → Euclidean n),
      e α v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm α) v)
    (v : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1) (exteriorDerivative C k ω p) v =
      extDeriv (fun y => e (F y)) (c p).val
        (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
  have hη := (exteriorDerivative_smooth h_exists h_coords h_unique C B k ω hω).1
  have hFd : DifferentiableAt ℝ F (c p).val :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  rw [hη c hc p hp,
    h_extension C k c hc ω p hp U (fun I z => F z I) hU hpU
      (fun I => (contDiffOn_pi.mp hF) I) heq,
    coordinateExpression_evaluation]
  exact (coefficient_alternating_derivative_of_equiv h_bridge n k e heval F (c p).val hFd _).symm

theorem coefficient_equiv_contraction (n k : ℕ)
    (e0 : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (h0 : ∀ (α : Index n k → ℝ) (v : Fin k → Euclidean n),
      e0 α v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm α) v)
    (e1 : (Index n (k+1) → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ))
    (h1 : ∀ (α : Index n (k+1) → ℝ) (v : Fin (k+1) → Euclidean n),
      e1 α v = evaluate (Euclidean n) (k+1)
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm α) v)
    (x : Euclidean n) (α : Index n (k+1) → ℝ) :
    e0 (modelContraction n k x α) = (e1 α).curryLeft x := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [h0, ContinuousAlternatingMap.curryLeft_apply_apply, h1]
  change evaluate (Euclidean n) k
    ((((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm
      (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun
        ((modelEvaluationEquiv n k).symm
          ((modelEvaluationEquiv n (k+1)
            (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm α)).curryLeft x))))) v = _
  rw [LinearEquiv.symm_apply_apply,
    ← modelEvaluationEquiv_apply, LinearEquiv.apply_symm_apply]
  rfl


theorem modelContraction_contDiffOn (n k : ℕ)
    {U : Set (Euclidean n)} {r : ℕ∞}
    {X : Euclidean n → Euclidean n} {F : Euclidean n → Index n (k+1) → ℝ}
    (hX : ContDiffOn ℝ r X U) (hF : ContDiffOn ℝ r F U) :
    ContDiffOn ℝ r (fun z => modelContraction n k (X z) (F z)) U := by
  let T : Euclidean n →L[ℝ] (Index n (k+1) → ℝ) →L[ℝ] (Index n k → ℝ) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap.comp (modelContraction n k))
  exact ((T.contDiff.contDiffOn.comp hX (Set.mapsTo_univ _ _)).clm_apply hF)

theorem coefficient_contraction_differentiableAt (n k : ℕ)
    (e0 : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (h0 : ∀ (α : Index n k → ℝ) (v : Fin k → Euclidean n),
      e0 α v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm α) v)
    (e1 : (Index n (k+1) → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ))
    (h1 : ∀ (α : Index n (k+1) → ℝ) (v : Fin (k+1) → Euclidean n),
      e1 α v = evaluate (Euclidean n) (k+1)
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm α) v)
    {X : Euclidean n → Euclidean n} {F : Euclidean n → Index n (k+1) → ℝ}
    {x : Euclidean n} (hX : DifferentiableAt ℝ X x) (hF : DifferentiableAt ℝ F x) :
    DifferentiableAt ℝ (fun z => (e1 (F z)).curryLeft (X z)) x := by
  let T : Euclidean n →L[ℝ] (Index n (k+1) → ℝ) →L[ℝ] (Index n k → ℝ) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap.comp (modelContraction n k))
  have hh := ((T.differentiableAt.comp x hX).clm_apply hF)
  have hcomp := e0.differentiableAt.comp x hh
  change DifferentiableAt ℝ (fun z => e0 (modelContraction n k (X z) (F z))) x at hcomp
  simpa only [coefficient_equiv_contraction n k e0 h0 e1 h1] using hcomp


theorem coordinateDerivative_eq_extDeriv_of_extension
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean n)) (F : Euclidean n → Index n k → ℝ)
    (hU : IsOpen U) (hpU : (c p).val ∈ U) (hF : ContDiffOn ℝ 1 F U)
    (heq : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F z.val I = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I) :
    ∃ e : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      (∀ (α : Index n k → ℝ) (v : Fin k → Euclidean n),
        e α v = evaluate (Euclidean n) k
          (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm α) v) ∧
      ∀ v : Fin (k+1) → TangentSpace S p,
        evaluate (TangentSpace S p) (k+1) (coordinateDerivative C k c hc ω p hp) v =
          extDeriv (fun y => e (F y)) (c p).val
            (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
  obtain ⟨e, heval, hd⟩ := h_bridge n k
  refine ⟨e, heval, ?_⟩
  intro v
  have hFd : DifferentiableAt ℝ F (c p).val :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  rw [h_extension C k c hc ω p hp U (fun I z => F z I) hU hpU
    (fun I => (contDiffOn_pi.mp hF) I) heq,
    coordinateExpression_evaluation]
  exact (hd F (c p).val hFd _).symm



/-- The continuous-alternating coordinate identification evaluates on the actual
coordinate vectors of the original intrinsic field. -/
theorem fieldEvaluation_model {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (Y : Fin k → Section S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (A : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (hA : ∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
      A a v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v) :
    fieldEvaluation k ω Y p.val = A (fun I => coefficients C k c hc ω p I)
      (fun i => C.tangent.fiberCoordinates.equiv c hc p.val p.property (Y i p.val)) := by
  let e := C.tangent.fiberCoordinates.equiv c hc p.val p.property
  rw [hA]
  change evaluate (TangentSpace S p.val) k (ω p.val) (fun i => Y i p.val) =
    evaluate (Euclidean n) k
      (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm
        ((((Pi.basisFun ℝ (Fin n)).map e.symm).dualBasis.exteriorPower k).equivFun
          (ω p.val))) (fun i => e (Y i p.val))
  have hcoeff := exterior_coordinate_transport (V := TangentSpace S p.val) (n := n) e k (ω p.val)
  rw [hcoeff, LinearEquiv.symm_apply_apply]
  have hd : e.symm.dualMap.toLinearMap = e.symm.toLinearMap.dualMap := rfl
  rw [hd, evaluate_coordinate_map (V := TangentSpace S p.val) (W := Euclidean n) k
    e.symm.toLinearMap]
  apply congrArg (fun v : Fin k → TangentSpace S p.val =>
    evaluate (TangentSpace S p.val) k (ω p.val) v)
  funext i
  exact (e.symm_apply_apply (Y i p.val)).symm

/-- Matching local coefficient and vector extensions gives a genuine ambient
extension of the evaluated scalar function. -/
theorem fieldEvaluation_model_eventuallyEq {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (Y : Fin k → Section S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (hA : ∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
      A a v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v)
    (F : Euclidean n → Index n k → ℝ) (V : Fin k → Euclidean n → Euclidean n)
    (hF : ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
      F (c q).val = fun I => coefficients C k c hc ω ⟨q,hq⟩ I)
    (hV : ∀ i, (fun q => V i (c q).val) =ᶠ[𝓝 p]
      LieBracketData.coefficients C.tangent (Y i) c hc) :
    (fun q => A (F (c q).val) (fun i => V i (c q).val)) =ᶠ[𝓝 p]
      fieldEvaluation k ω Y := by
  have hVall : ∀ᶠ q in 𝓝 p, ∀ i, V i (c q).val =
      LieBracketData.coefficients C.tangent (Y i) c hc q :=
    (Filter.eventually_all.mpr hV)
  filter_upwards [hF, hVall, c.open_source.mem_nhds hp] with q hqF hqV hq
  rw [hqF hq]
  rw [fieldEvaluation_model C k ω Y c hc ⟨q,hq⟩ A hA]
  congr 1
  funext i
  simpa only [LieBracketData.coefficients, dite_eq_left hq] using hqV i

/-- Evaluation in a finite coefficient space is polynomial in the coefficients
and in all the vectors. This form avoids any chosen norm on exterior powers. -/
theorem modelEvaluation_contDiffOn {n k : ℕ}
    (A : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (F : Euclidean n → Index n k → ℝ) (V : Fin k → Euclidean n → Euclidean n)
    (U : Set (Euclidean n)) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A (F z) (fun i => V i z)) U := by
  have hexp (a : Index n k → ℝ) (v : Fin k → Euclidean n) :
      A a v = ∑ I : Index n k, a I * A (Pi.single I 1) v := by
    have ha : a = ∑ I : Index n k, a I • Pi.single I 1 := by
      ext J
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    simp only [map_sum, ContinuousAlternatingMap.sum_apply, map_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∑ I : Index n k, F z I * A (Pi.single I 1) (fun i => V i z)) U := by
    apply ContDiffOn.sum
    intro I hI
    have hFI := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index n k => ℝ) I).contDiff.comp_contDiffOn hF
    have hVi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fun i => V i z) U := contDiffOn_pi.mpr hV
    have hAi := (A (Pi.single I 1)).toContinuousMultilinearMap.contDiff.comp_contDiffOn hVi
    exact hFI.mul hAi
  exact hs.congr (fun z hz => hexp (F z) (fun i => V i z))

/-- A smooth model extension of evaluation computes the exact intrinsic scalar
action, including at boundary and corner points. -/
theorem scalarAction_fieldEvaluation_model {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (X : Section S) (k : ℕ) (ω : Field S k)
    (Y : Fin k → SmoothField C.tangent) (hω : IsForm (B k) ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (hA : ∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
      A a v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v)
    (F : Euclidean n → Index n k → ℝ) (V : Fin k → Euclidean n → Euclidean n)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hVs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) U)
    (hF : ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
      F (c q).val = fun I => coefficients C k c hc ω ⟨q,hq⟩ I)
    (hV : ∀ i, (fun q => V i (c q).val) =ᶠ[𝓝 p]
      LieBracketData.coefficients C.tangent (Y i).val c hc) :
    scalarAction X (fieldEvaluation k ω (fun i => (Y i).val)) p =
      fderiv ℝ (fun z => A (F z) (fun i => V i z)) (c p).val
        (C.tangent.fiberCoordinates.equiv c hc p hp (X p)) := by
  let f := fieldEvaluation k ω (fun i => (Y i).val)
  have hf := fieldEvaluation_smooth C B k ω Y hω
  let g := functionGerm S f hf p
  have he : GermChartExtension S p c g (fun z => A (F z) (fun i => V i z)) := by
    refine ⟨⟨U,hU,hpU,modelEvaluation_contDiffOn A F V U hFs hVs⟩, ?_⟩
    exact Germ.coe_eq.mpr (fieldEvaluation_model_eventuallyEq C k ω
      (fun i => (Y i).val) c hc p hp A hA F V hF hV)
  exact scalarAction_coordinates C.tangent.fiberCoordinates X f p c hc hp g rfl _ he



/-- A smooth form, a smooth field and finitely many smooth slot fields admit
actual smooth ambient representatives on one common open coordinate neighborhood. -/
theorem common_coordinate_extensions
    (h_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (k : ℕ) (ω : Field S k)
    (Y : Fin k → SmoothField C.tangent) (hω : IsForm (B k) ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source) :
    ∃ (U : Set (Euclidean n)), IsOpen U ∧ (c p).val ∈ U ∧
      ∃ (F : Euclidean n → Index n k → ℝ) (GX : Euclidean n → Euclidean n)
        (GY : Fin k → Euclidean n → Euclidean n),
        ContDiffOn ℝ (⊤ : ℕ∞) F U ∧ ContDiffOn ℝ (⊤ : ℕ∞) GX U ∧
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (GY i) U) ∧
        (∀ q : c.source, (c q.val).val ∈ U →
          F (c q.val).val = fun I => coefficients C k c hc ω q I) ∧
        (∀ q : c.source, (c q.val).val ∈ U →
          GX (c q.val).val = C.tangent.fiberCoordinates.equiv c hc q.val q.property (X.val q.val)) ∧
        (∀ i, ∀ q : c.source, (c q.val).val ∈ U →
          GY i (c q.val).val = C.tangent.fiberCoordinates.equiv c hc q.val q.property ((Y i).val q.val)) := by
  classical
  obtain ⟨Uω, hUω, hpω, F, hF, heF⟩ :=
    (h_regular C k (B k) ω).mp hω c hc ⟨p, hp⟩
  obtain ⟨UX, hUX, hpX, GX, hGX, heX⟩ :=
    field_coordinates_regular C X c hc ⊤ ⟨p, hp⟩
  choose UY hUY hpY GY hGY heY using fun i =>
    field_coordinates_regular C (Y i) c hc ⊤ ⟨p, hp⟩
  let U := (Uω ∩ UX) ∩ ⋂ i, UY i
  have hU : IsOpen U := (hUω.inter hUX).inter (isOpen_iInter_of_finite (fun i => hUY i))
  have hpU : (c p).val ∈ U := ⟨⟨hpω, hpX⟩, mem_iInter.mpr hpY⟩
  refine ⟨U, hU, hpU, F, GX, GY, hF.mono (fun z hz => hz.1.1),
    hGX.mono (fun z hz => hz.1.2), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hGY i).mono (fun z hz => mem_iInter.mp hz.2 i)
  · intro q hq
    exact heF q hq.1.1
  · intro q hq
    exact heX q hq.1.2
  · intro i q hq
    exact heY i q (mem_iInter.mp hq.2 i)

/-- Evaluation in one original tangent fiber uses the same normalized model coefficients. -/
theorem evaluate_model_coefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) (v : Fin k → TangentSpace S p.val)
    (A : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (hA : ∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
      A a v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v) :
    evaluate (TangentSpace S p.val) k (ω p.val) v = A (fun I => coefficients C k c hc ω p I)
      (fun i => C.tangent.fiberCoordinates.equiv c hc p.val p.property (v i)) := by
  let e := C.tangent.fiberCoordinates.equiv c hc p.val p.property
  rw [hA]
  change evaluate (TangentSpace S p.val) k (ω p.val) v =
    evaluate (Euclidean n) k
      (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm
        ((((Pi.basisFun ℝ (Fin n)).map e.symm).dualBasis.exteriorPower k).equivFun
          (ω p.val))) (fun i => e (v i))
  have hcoeff := exterior_coordinate_transport (V := TangentSpace S p.val) (n := n) e k (ω p.val)
  rw [hcoeff, LinearEquiv.symm_apply_apply]
  have hd : e.symm.dualMap.toLinearMap = e.symm.toLinearMap.dualMap := rfl
  rw [hd, evaluate_coordinate_map (V := TangentSpace S p.val) (W := Euclidean n) k
    e.symm.toLinearMap]
  apply congrArg (fun v : Fin k → TangentSpace S p.val =>
    evaluate (TangentSpace S p.val) k (ω p.val) v)
  funext i
  exact (e.symm_apply_apply (v i)).symm




/-- Strong coefficient extensions on the chart source agree throughout the
corresponding portion of the model target. -/
theorem coefficient_extension_on_target
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (U : Set (Euclidean n)) (F : Euclidean n → Index n k → ℝ)
    (hF : ∀ q : c.source, (c q.val).val ∈ U →
      F (c q.val).val = fun I => coefficients C k c hc ω q I) :
    ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F z.val I = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I := by
  intro z hz hzU I
  have hh := hF ⟨c.symm z, c.map_target hz⟩
  have hcz : c (c.symm z) = z := c.right_inv hz
  have hzU' : (c (c.symm z)).val ∈ U := by simpa only [hcz] using hzU
  simpa only [hcz] using congrFun (hh hzU') I

/-- The intrinsic Cartan extension is the usual Euclidean Cartan sum in any
fixed ambient coefficient and vector-field extensions. -/
theorem lieDerivative_model_evaluation_of_extensions
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (X : SmoothField C.tangent) (k : ℕ) (ω : Field S (k+1)) (hω : IsForm (B (k+1)) ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (F : Euclidean n → Index n (k+1) → ℝ) (G : Euclidean n → Euclidean n)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F U) (hGs : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hF : ∀ q : c.source, (c q.val).val ∈ U →
      F (c q.val).val = fun I => coefficients C (k+1) c hc ω q I)
    (hG : ∀ q : c.source, (c q.val).val ∈ U →
      G (c q.val).val = C.tangent.fiberCoordinates.equiv c hc q.val q.property (X.val q.val))
    (e0 : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (h0 : ∀ (α : Index n k → ℝ) (v : Fin k → Euclidean n),
      e0 α v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm α) v)
    (e1 : (Index n (k+1) → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ))
    (h1 : ∀ (α : Index n (k+1) → ℝ) (v : Fin (k+1) → Euclidean n),
      e1 α v = evaluate (Euclidean n) (k+1)
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm α) v)
    (v : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1) (lieDerivative C X.val (k+1) ω p) v =
      extDeriv (fun z => (e1 (F z)).curryLeft (G z)) (c p).val
          (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) +
        extDeriv (fun z => e1 (F z)) (c p).val
          (Matrix.vecCons (G (c p).val) (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i))) := by
  let H : Euclidean n → Index n k → ℝ := fun z => modelContraction n k (G z) (F z)
  have hHs : ContDiffOn ℝ (⊤ : ℕ∞) H U := modelContraction_contDiffOn n k hGs hFs
  have hH : ∀ q : c.source, (c q.val).val ∈ U →
      H (c q.val).val = fun I => coefficients C k c hc (contraction C X.val (k+1) ω) q I := by
    intro q hqU
    dsimp only [H]
    rw [hG q hqU, hF q hqU]
    exact (contraction_coefficients C X.val k ω c hc q).symm
  have hd0 := selected_exteriorDerivative_eq_extDeriv_of_extension
    h_exists h_coords h_unique h_bridge h_extension C B k c hc
    (contraction C X.val (k+1) ω) (contraction_smooth C B X (k+1) ω hω)
    p hp U H hU hpU (hHs.of_le (by simp))
    (coefficient_extension_on_target C k c hc _ U H hH) e0 h0 v
  have hd1 := selected_exteriorDerivative_eq_extDeriv_of_extension
    h_exists h_coords h_unique h_bridge h_extension C B (k+1) c hc ω hω
    p hp U F hU hpU (hFs.of_le (by simp))
    (coefficient_extension_on_target C (k+1) c hc ω U F hF) e1 h1
    (Matrix.vecCons (X.val p) v)
  have hHfun : (fun z => e0 (H z)) = fun z => (e1 (F z)).curryLeft (G z) := by
    funext z
    exact coefficient_equiv_contraction n k e0 h0 e1 h1 (G z) (F z)
  rw [hHfun] at hd0
  have hv : (fun i => C.tangent.fiberCoordinates.equiv c hc p hp
      (Matrix.vecCons (X.val p) v i)) =
        Matrix.vecCons (G (c p).val)
          (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hG ⟨p,hp⟩ hpU).symm
    · rfl
  rw [hv] at hd1
  simp only [lieDerivative, eq_mp_eq_cast, cast_eq, Pi.add_apply, map_add, add_apply]
  rw [hd0, contraction_apply_proof, hd1]


/-- Differentiating the actual finite-dimensional pullback of an alternating
form produces one coefficient derivative and one Jacobian derivative per slot. -/
theorem model_flowPullback_derivative
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (ω : E → E [⋀^Fin k]→L[ℝ] ℝ) (g : ℝ → E)
    (A : ℝ → E →L[ℝ] E) (x dx : E) (D : E →L[ℝ] E)
    (hω : DifferentiableAt ℝ ω x) (hg0 : g 0 = x)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hg : HasDerivAt g dx 0) (hA : HasDerivAt A D 0) (v : Fin k → E) :
    HasDerivAt (fun t => ω (g t) (fun i => A t (v i)))
      (fderiv ℝ ω x dx v + ∑ i : Fin k, ω x (Function.update v i (D (v i)))) 0 := by
  have hw : HasDerivAt (fun t => ω (g t)) (fderiv ℝ ω x dx) 0 := by
    exact hω.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg hg0.symm
  have hv (i : Fin k) : HasDerivAt (fun t => A t (v i)) (D (v i)) 0 := by
    simpa only [map_zero, add_zero] using hA.clm_apply (hasDerivAt_const (0 : ℝ) (v i))
  have h := (hw.hasFDerivAt.continuousAlternatingMap_apply
    (fun i => (hv i).hasFDerivAt)).hasDerivAt
  convert h using 1 <;> simp [hg0, hA0]

/-- For an actual joint smooth flow representative, its state Jacobian's time
derivative is the spatial derivative of its initial velocity. -/
theorem model_flow_jacobian_derivative
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × E → E) (X : E → E) (x : E)
    (hG : ContDiffAt ℝ 2 G (0, x))
    (hvel : (fun y => fderiv ℝ G (0, y) (1, 0)) =ᶠ[𝓝 x] X) :
    HasDerivAt
      (fun t => (fderiv ℝ G (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (fderiv ℝ X x) 0 := by
  have h := BracketFromFlow.time_derivative_state_jacobian G 0 x hG
  have heq : fderiv ℝ (fun y => fderiv ℝ G (0, y) (1, 0)) x = fderiv ℝ X x :=
    hvel.fderiv_eq
  exact h.congr_deriv heq

/-- Cartan's model expression is the derivative of pullback along every smooth
curve of time maps with the prescribed initial value and initial velocity. -/
theorem model_flowPullback_cartan
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (ω : E → E [⋀^Fin (k+1)]→L[ℝ] ℝ)
    (G : ℝ × E → E) (X : E → E) (x : E)
    (hω : DifferentiableAt ℝ ω x) (hX : DifferentiableAt ℝ X x)
    (hc : DifferentiableAt ℝ (fun y => (ω y).curryLeft (X y)) x)
    (hG : ContDiffAt ℝ 2 G (0, x))
    (hinit : (fun y => G (0, y)) =ᶠ[𝓝 x] id)
    (hvel : (fun y => fderiv ℝ G (0, y) (1, 0)) =ᶠ[𝓝 x] X)
    (v : Fin (k+1) → E) :
    HasDerivAt
      (fun t => ω (G (t, x))
        (fun i => fderiv ℝ G (t, x) (0, v i)))
      (extDeriv (fun y => (ω y).curryLeft (X y)) x v +
        extDeriv ω x (Fin.cons (X x) v)) 0 := by
  have hGs : HasDerivAt (fun t => G (t, x)) (X x) 0 := by
    have h := (hG.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    simpa only [hvel.self_of_nhds, Function.comp_def, id_eq] using h
  have hJac0 : (fderiv ℝ G (0, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      ContinuousLinearMap.id ℝ E := by
    have hs := (hG.differentiableAt (by norm_num)).hasFDerivAt.comp x
      ((hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun y => G (0, y)) _ x at hs
    have heq : fderiv ℝ (fun y => G (0, y)) x = fderiv ℝ id x := hinit.fderiv_eq
    rw [hs.fderiv, fderiv_id (𝕜 := ℝ)] at heq
    convert heq using 1 <;> ext v <;> rfl
  have hder := model_flowPullback_derivative ω (fun t => G (t, x))
    (fun t => (fderiv ℝ G (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
    x (X x) (fderiv ℝ X x) hω hinit.self_of_nhds hJac0 hGs
    (model_flow_jacobian_derivative G X x hG hvel) v
  rw [← model_cartan_evaluation hω hX hc v] at hder
  exact hder



/-- The actual local flow equation determines the initial forward Jacobian and
its time derivative, including full normal columns in boundary charts. -/
theorem localFlow_coordinate_jet {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (O : Set M) (hF : IsLocalFlowOn X F O)
    (p : M) (hpO : p ∈ O) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) (U : Set (ℝ × Euclidean n)) (G : ℝ × Euclidean n → Euclidean n)
    (hU : IsOpen U) (hpU : (0, (e p).val) ∈ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (heG : (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (0, p)]
      (fun w => (e (flow F w)).val))
    (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
    (hV : IsOpen V) (hpV : (e p).val ∈ V) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (heH : (fun q => H (e q).val) =ᶠ[𝓝 p]
      (LieBracketData.coefficients B X.val e he)) :
    G (0, (e p).val) = (e p).val ∧
    (fderiv ℝ G (0, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)) =
      ContinuousLinearMap.id ℝ (Euclidean n) ∧
    HasDerivAt (fun t => G (t, (e p).val)) (H (e p).val) 0 ∧
    HasDerivAt
      (fun t => (fderiv ℝ G (t, (e p).val)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)))
      (fderiv ℝ H (e p).val) 0 := by
  have hi : ContinuousAt (fun q : M => ((0 : ℝ), q)) p :=
    continuousAt_const.prodMk continuousAt_id
  have hinit : (fun q => G (0, (e q).val)) =ᶠ[𝓝 p] (fun q => (e q).val) := by
    filter_upwards [heG.comp_tendsto hi, hF.1.mem_nhds hpO] with q hq hqO
    exact hq.trans (congrArg (fun r => (e r).val) (hF.2 q hqO).2.1)
  have hG0 : G (0, (e p).val) = (e p).val := hinit.self_of_nhds
  have hGat := hG.contDiffAt (hU.mem_nhds hpU)
  have hGd := hGat.differentiableAt (by simp)
  have hs := hGd.hasFDerivAt.comp (e p).val
    ((hasFDerivAt_const (0 : ℝ) (e p).val).prodMk (hasFDerivAt_id (e p).val))
  have hA0 := FiniteRegularity.extension_independence e (fun q => (e q).val) p hp _ _
    ⟨_, hs, hinit⟩ ⟨_, hasFDerivAt_id (e p).val, Eventually.of_forall (fun _ => rfl)⟩
  change (fderiv ℝ G (0, (e p).val)).comp
    (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)) = ContinuousLinearMap.id ℝ (Euclidean n) at hA0
  have hcoord : ContinuousAt (fun q => ((0 : ℝ), (e q).val)) p :=
    continuousAt_const.prodMk
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp))
  have hnear : ∀ᶠ q in 𝓝 p,
      (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (0, q)]
        (fun w => (e (flow F w)).val) :=
    hi.eventually (eventually_eventually_nhds.mpr heG)
  have hvel : (fun q => fderiv ℝ G (0, (e q).val) (1, 0)) =ᶠ[𝓝 p]
      (LieBracketData.coefficients B X.val e he) := by
    filter_upwards [hnear, hF.1.mem_nhds hpO, e.open_source.mem_nhds hp,
      hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hq hqO hqe hqU
    obtain ⟨hzq, hinitq, hγq, hsmq⟩ := hF.2 q hqO
    have hqγ : F.curve q 0 ∈ e.source := by simpa only [hinitq] using hqe
    have hode := (hγq.2 0 hzq e he hqγ).2
    rw [← LieBrackets.coefficients_eq X.val e he (F.curve q 0) hqγ, hinitq] at hode
    have hs0 : ContinuousAt (fun t : ℝ => (t, q)) 0 :=
      continuousAt_id.prodMk continuousAt_const
    have hgpath :=
      ((hG.contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (e q).val))
    exact (hgpath.congr_of_eventuallyEq (hq.comp_tendsto hs0).symm).unique hode
  have hvel0 : fderiv ℝ G (0, (e p).val) (1, 0) = H (e p).val :=
    hvel.self_of_nhds.trans heH.self_of_nhds.symm
  have hpath : HasDerivAt (fun t => G (t, (e p).val)) (H (e p).val) 0 := by
    have ht := hGd.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (e p).val))
    simpa only [hvel0, Function.comp_def, id_eq] using ht
  have hvelocity : (fun q => fderiv ℝ G (0, (e q).val) (1, 0)) =ᶠ[𝓝 p]
      (fun q => H (G (0, (e q).val))) := by
    filter_upwards [hvel, hinit, heH] with q hqv hqi hqH
    exact hqv.trans (hqH.symm.trans (congrArg H hqi.symm))
  have hHd : DifferentiableAt ℝ H (G (0, (e p).val)) := by
    rw [hG0]
    exact (hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hJac := BracketFromFlow.state_jacobian_variation_of_velocity e p hp G H 0
    (hGat.of_le (by simp)) hHd hvelocity
  rw [hG0, hA0, ContinuousLinearMap.comp_id] at hJac
  exact ⟨hG0, hA0, hpath, hJac⟩



/-- Near zero, actual flow pullback in a fixed original fiber is represented by
the genuine forward state Jacobian of any joint smooth coordinate extension. -/
theorem flowPullback_model_eventuallyEq {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (X : SmoothField C.tangent) (F : CurveFamily M) (O : Set M) (hF : IsLocalFlowOn X F O)
    (p : M) (hpO : p ∈ O) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hp : p ∈ c.source) (k : ℕ) (ω : Field S k) (v : Fin k → TangentSpace S p)
    (A : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ))
    (hA : ∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
      A a v = evaluate (Euclidean n) k
        (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v)
    (Ω : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ)
    (hΩ : ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
      Ω (c q).val = A (fun I => coefficients C k c hc ω ⟨q, hq⟩ I))
    (U : Set (ℝ × Euclidean n)) (G : ℝ × Euclidean n → Euclidean n)
    (hU : IsOpen U) (hpU : (0, (c p).val) ∈ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (heG : (fun w : ℝ × M => G (w.1, (c w.2).val)) =ᶠ[𝓝 (0, p)]
      (fun w => (c (flow F w)).val)) :
    (fun t => evaluate (TangentSpace S p) k (flowPullback S F t k ω p) v) =ᶠ[𝓝 0]
      (fun t => Ω (G (t, (c p).val))
        (fun i => fderiv ℝ G (t, (c p).val)
          (0, C.tangent.fiberCoordinates.equiv c hc p hp (v i)))) := by
  obtain ⟨hz, hinit, hcurve, hsm⟩ := hF.2 p hpO
  have hγ : Tendsto (F.curve p) (𝓝 0) (𝓝 p) := by
    have hγ0 : Tendsto (F.curve p) (𝓝 0) (𝓝 (F.curve p 0)) :=
      hcurve.1.continuousAt ((F.interval p).isOpen.mem_nhds hz)
    simpa only [hinit] using hγ0
  have hi : ContinuousAt (fun t : ℝ => (t, p)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hcoord : ContinuousAt (fun t : ℝ => (t, (c p).val)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hnear : ∀ᶠ t in 𝓝 0,
      (fun w : ℝ × M => G (w.1, (c w.2).val)) =ᶠ[𝓝 (t, p)]
        (fun w => (c (flow F w)).val) :=
    hi.eventually (eventually_eventually_nhds.mpr heG)
  filter_upwards [(F.interval p).isOpen.mem_nhds hz,
    hγ.eventually (c.open_source.mem_nhds hp), hγ.eventually hΩ,
    hcoord.preimage_mem_nhds (hU.mem_nhds hpU), hnear, heG.comp_tendsto hi]
    with t ht hqt hΩt htU heGt hGpt
  change G (t, (c p).val) = (c (F.curve p t)).val at hGpt
  rw [flowPullback_apply, evaluate_model_coefficients C k ω c hc
    ⟨F.curve p t, hqt⟩ (fun i => timeDifferential S F t p (v i)) A hA,
    ← hΩt hqt, ← hGpt]
  congr 1
  funext i
  let Ut : Set (Euclidean n) := (fun y => (t, y)) ⁻¹' U
  have hUt : IsOpen Ut := hU.preimage (continuous_const.prodMk continuous_id)
  have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => G (t, y)) Ut :=
    hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  have hiq : ContinuousAt (fun q : M => (t, q)) p :=
    continuousAt_const.prodMk continuousAt_id
  have hEq : (fun q => G (t, (c q).val)) =ᶠ[𝓝 p]
      (fun q => (c (F.curve q t)).val) := heGt.comp_tendsto hiq
  have hD := timeDifferential_spec S F t p (hsm t ht)
  have hjac := BracketFromFlow.rebased_jacobian C.tangent (fun q => F.curve q t)
    p (F.curve p t) (timeDifferential S F t p) hD c hc hqt c hc hp
    Ut (fun y => G (t, y)) hUt htU hslice hEq (v i)
  have hs := ((hG.contDiffAt (hU.mem_nhds htU)).differentiableAt (by simp)).hasFDerivAt.comp
    (c p).val ((hasFDerivAt_const t (c p).val).prodMk (hasFDerivAt_id (c p).val))
  change HasFDerivAt (fun y => G (t, y)) _ (c p).val at hs
  rw [hs.fderiv] at hjac
  exact hjac


/-- The complete invariant evaluation formula at a point with arbitrary genuine
smooth ambient representatives on one common chart neighborhood. -/
theorem lie_evaluation_of_extensions
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent)
    (hb : LieBracketData.BracketOperation b) (X : SmoothField C.tangent)
    (k : ℕ) (ω : Field S (k+1)) (Y : Fin (k+1) → SmoothField C.tangent)
    (hω : IsForm (B (k+1)) ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (F : Euclidean n → Index n (k+1) → ℝ)
    (GX : Euclidean n → Euclidean n) (GY : Fin (k+1) → Euclidean n → Euclidean n)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hGXs : ContDiffOn ℝ (⊤ : ℕ∞) GX U)
    (hGYs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (GY i) U)
    (hF : ∀ q : c.source, (c q.val).val ∈ U →
      F (c q.val).val = fun I => coefficients C (k+1) c hc ω q I)
    (hGX : ∀ q : c.source, (c q.val).val ∈ U → GX (c q.val).val =
      C.tangent.fiberCoordinates.equiv c hc q.val q.property (X.val q.val))
    (hGY : ∀ i, ∀ q : c.source, (c q.val).val ∈ U → GY i (c q.val).val =
      C.tangent.fiberCoordinates.equiv c hc q.val q.property ((Y i).val q.val)) :
    fieldEvaluation (k+1) (lieDerivative C X.val (k+1) ω) (fun i => (Y i).val) p =
      scalarAction X.val (fieldEvaluation (k+1) ω (fun i => (Y i).val)) p -
        ∑ i : Fin (k+1), fieldEvaluation (k+1) ω
          (fun j => (Function.update Y i (b X (Y i)) j).val) p := by
  obtain ⟨e0,he0,_⟩ := h_bridge n k
  obtain ⟨e1,he1,_⟩ := h_bridge n (k+1)
  have hcoord : ContinuousAt (fun q => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ c.source ∧ (c q).val ∈ U :=
    Filter.Eventually.and (c.open_source.mem_nhds hp)
      (hcoord.preimage_mem_nhds (hU.mem_nhds hpU))
  have heF : ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
      F (c q).val = fun I => coefficients C (k+1) c hc ω ⟨q,hq⟩ I := by
    filter_upwards [hnear] with q hq
    intro hqs
    exact hF ⟨q,hqs⟩ hq.2
  have heGX : (fun q => GX (c q).val) =ᶠ[𝓝 p]
      LieBracketData.coefficients C.tangent X.val c hc := by
    filter_upwards [hnear] with q hq
    simpa only [LieBracketData.coefficients, dite_eq_left hq.1] using hGX ⟨q,hq.1⟩ hq.2
  have heGY (i : Fin (k+1)) : (fun q => GY i (c q).val) =ᶠ[𝓝 p]
      LieBracketData.coefficients C.tangent (Y i).val c hc := by
    filter_upwards [hnear] with q hq
    simpa only [LieBracketData.coefficients, dite_eq_left hq.1] using hGY i ⟨q,hq.1⟩ hq.2
  have hFd : DifferentiableAt ℝ F (c p).val :=
    (hFs.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hGXd : DifferentiableAt ℝ GX (c p).val :=
    (hGXs.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hGYd (i : Fin (k+1)) : DifferentiableAt ℝ (GY i) (c p).val :=
    ((hGYs i).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hGX0 := hGX ⟨p,hp⟩ hpU
  have hGY0 (i : Fin (k+1)) := hGY i ⟨p,hp⟩ hpU
  have hF0 := hF ⟨p,hp⟩ hpU
  have hscalar := scalarAction_fieldEvaluation_model C B X.val (k+1) ω Y hω
    c hc p hp e1 he1 F GY U hU hpU hFs hGYs heF heGY
  have hbracket (i : Fin (k+1)) := bracket_coordinates_of_extensions C b hb X (Y i)
    c hc p hp GX (GY i) hGXd (hGYd i) heGX (heGY i)
  have hsum : (∑ i : Fin (k+1), fieldEvaluation (k+1) ω
      (fun j => (Function.update Y i (b X (Y i)) j).val) p) =
      ∑ i : Fin (k+1), e1 (F (c p).val)
        (Function.update (fun j => GY j (c p).val) i
          (VectorField.lieBracket ℝ GX (GY i) (c p).val)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [fieldEvaluation_model C (k+1) ω _ c hc ⟨p,hp⟩ e1 he1, ← hF0]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using hbracket i
    · simpa only [Function.update_of_ne hj] using (hGY0 j).symm
  have hcmodel := coefficient_contraction_differentiableAt n k e0 he0 e1 he1 hGXd hFd
  have hmodel := model_lie_evaluation (e1.differentiableAt.comp (c p).val hFd)
    hGXd hcmodel GY hGYd
  simp only [Function.comp_def] at hmodel
  have hL := lieDerivative_model_evaluation_of_extensions h_exists h_coords h_unique h_bridge h_extension
    C B X k ω hω c hc p hp U hU hpU F GX hFs hGXs hF hGX e0 he0 e1 he1
    (fun i => (Y i).val p)
  change fieldEvaluation (k+1) (lieDerivative C X.val (k+1) ω) (fun i => (Y i).val) p = _ at hL
  simp only [← hGY0, Matrix.vecCons] at hL
  rw [hL, hmodel, ← hsum, hscalar, ← hGX0]



private theorem lie_evaluation_proof
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.lie_evaluationType.{u} := by
  intro n a M _ S C B b hb X k ω Y hω
  refine ⟨fieldEvaluation_smooth C B k ω Y hω, ?_⟩
  intro p
  cases k with
  | zero =>
    simpa using (lie_evaluation_degree_zero h_unique h_function C B X ω Y hω).2 p
  | succ k =>
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨U, hU, hpU, F, GX, GY, hFs, hGXs, hGYs, hF, hGX, hGY⟩ :=
      common_coordinate_extensions h_regular C B X (k+1) ω Y hω c hc p hp
    exact lie_evaluation_of_extensions h_exists h_coords h_unique h_bridge h_extension
      C B b hb X k ω Y hω c hc p hp U hU hpU F GX GY hFs hGXs hGYs hF hGX hGY

private theorem lie_commutes_contraction_proof
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h_zero : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_contractionType.{u} :=
  lie_commutes_contraction_of_evaluation (exteriorDerivative_zero_proof h_unique h_zero)
    (operators_smooth_proof h_exists h_coords h_unique)
    (lie_evaluation_proof h_exists h_coords h_unique h_bridge h_extension h_regular h_function)

private theorem lie_commutes_lie_proof
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h_zero : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_lieType.{u} :=
  lie_commutes_lie_of_contraction h_exists h_coords h_unique
    (operators_smooth_proof h_exists h_coords h_unique)
    (lie_commutes_d_proof h_exists h_coords h_unique)
    (lie_commutes_contraction_proof h_exists h_coords h_unique h_bridge h_extension
      h_regular h_function h_zero)


/-- Increasing exterior coefficients are evaluation on the corresponding ordered
coordinate tangent basis; no factorial is introduced. -/
theorem exterior_coefficient_evaluation {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (k : ℕ) (ω : Fiber V k) (I : Index n k) :
    (b.dualBasis.exteriorPower k).repr ω I =
      evaluate V k ω (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm I i)) := by
  rw [FormPullbackResults.evaluate_eq_pairing]
  have hI : exteriorPower.ιMulti ℝ k (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm I i)) =
      b.exteriorPower k I := by
    simpa only [exteriorPower.ιMulti_family, Function.comp_def] using (exteriorPower.basis_apply ℝ k b I).symm
  rw [hI]
  rw [exteriorPower.pairingDual_eq_dualBasis_constr k b,
    Module.Basis.constr_apply_fintype]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.dualBasis_apply,
    Module.Basis.repr_self, Finsupp.single_apply, Module.Basis.equivFun_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Every actual coefficient is an ordered coordinate-basis evaluation. -/
theorem coefficients_eq_evaluate {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k) :
    coefficients C k c hc ω p I =
      evaluate (TangentSpace S p.val) k (ω p.val)
        (fun i => coordinateVector C.tangent.fiberCoordinates c hc p.val p.property
          (Set.powersetCard.ofFinEmbEquiv.symm I i)) := by
  have h := exterior_coefficient_evaluation (V := TangentSpace S p.val)
    ((Pi.basisFun ℝ (Fin n)).map (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm)
    k (ω p.val) I
  simpa only [coefficients, Module.Basis.map_apply, Pi.basisFun_apply, coordinateVector] using h

/-- The actual local-flow derivative equals the intrinsic Cartan extension in
every chart and every degree, including boundary points where the flow exists. -/
private theorem local_flow_proof
    (h_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h_coords : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h_function : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u}) :
    Specs.SmoothManifolds.Ch07.Cartan.local_flowType.{u} := by
  classical
  intro n a M _ S C B X F O hFlow r ω hω
  cases r with
  | zero => exact local_flow_degree_zero h_unique h_function C B X F O hFlow ω hω
  | succ k =>
    intro c hc p hp hpO I
    let v : Fin (k+1) → TangentSpace S p := fun i =>
      coordinateVector C.tangent.fiberCoordinates c hc p hp
        (Set.powersetCard.ofFinEmbEquiv.symm I i)
    obtain ⟨hz, hinit, hγ, hsm⟩ := hFlow.2 p hpO
    have hfp : flow F (0, p) ∈ c.source := by
      change F.curve p 0 ∈ c.source
      rwa [hinit]
    obtain ⟨UG, hUG, hpUG, G, hG, heG⟩ := (hsm 0 hz).2 c hc c hc hp hfp
    obtain ⟨U, hU, hpU, f, H, Y, hf, hH, hY, hef, heH, heY⟩ :=
      common_coordinate_extensions h_regular C B X (k+1) ω (fun _ => X) hω c hc p hp
    obtain ⟨e0, h0, hd0⟩ := h_bridge n k
    obtain ⟨e1, h1, hd1⟩ := h_bridge n (k+1)
    let Ω : Euclidean n → (Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ := fun z => e1 (f z)
    have hcoord : ContinuousAt (fun q : M => (c q).val) p :=
      continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
    have hΩ : ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
        Ω (c q).val = e1 (fun J => coefficients C (k+1) c hc ω ⟨q,hq⟩ J) := by
      filter_upwards [hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqU
      intro hq
      exact congrArg e1 (hef ⟨q,hq⟩ hqU)
    have heH' : (fun q => H (c q).val) =ᶠ[𝓝 p]
        (LieBracketData.coefficients C.tangent X.val c hc) := by
      filter_upwards [hcoord.preimage_mem_nhds (hU.mem_nhds hpU),
        c.open_source.mem_nhds hp] with q hqU hq
      simpa only [LieBracketData.coefficients, dite_eq_left hq] using heH ⟨q,hq⟩ hqU
    obtain ⟨hG0, hJac0, hGt, hJact⟩ := localFlow_coordinate_jet C.tangent X F O hFlow
      p hpO c hc hp UG G hUG hpUG hG heG U H hU hpU hH heH'
    have hfd : DifferentiableAt ℝ f (c p).val :=
      (hf.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
    have hHd : DifferentiableAt ℝ H (c p).val :=
      (hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
    have hΩd : DifferentiableAt ℝ Ω (c p).val := e1.differentiableAt.comp (c p).val hfd
    have hContr := coefficient_contraction_differentiableAt n k e0 h0 e1 h1 hHd hfd
    let V : Fin (k+1) → Euclidean n := fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)
    have hModel := model_cartan_evaluation hΩd hHd hContr V
    have hLie := lieDerivative_model_evaluation_of_extensions h_exists h_coords h_unique
      h_bridge h_extension C B X k ω hω c hc p hp U hU hpU f H hf hH hef heH e0 h0 e1 h1 v
    have hder := model_flowPullback_derivative Ω (fun t => G (t, (c p).val))
      (fun t => (fderiv ℝ G (t, (c p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)))
      (c p).val (H (c p).val) (fderiv ℝ H (c p).val) hΩd hG0 hJac0 hGt hJact V
    rw [← hModel] at hder
    have hLsym : extDeriv (fun z => (Ω z).curryLeft (H z)) (c p).val V +
        extDeriv Ω (c p).val (Fin.cons (H (c p).val) V) =
        evaluate (TangentSpace S p) (k+1) (lieDerivative C X.val (k+1) ω p) v := hLie.symm
    rw [hLsym] at hder
    change HasDerivAt
      (fun t => Ω (G (t, (c p).val)) (fun i => fderiv ℝ G (t, (c p).val) (0, V i)))
      (evaluate (TangentSpace S p) (k+1) (lieDerivative C X.val (k+1) ω p) v) 0 at hder
    have hevent := flowPullback_model_eventuallyEq C X F O hFlow p hpO c hc hp
      (k+1) ω v e1 h1 Ω hΩ UG G hUG hpUG hG heG
    have hactual := hder.congr_of_eventuallyEq hevent
    simpa only [coefficients_eq_evaluate, v] using hactual


/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem contraction_apply_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.contraction_applyType.{u} :=
  contraction_apply_proof

/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem contraction_zero_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.contraction_zeroType.{u} :=
  contraction_zero_proof

/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem contraction_anticomm_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.contraction_anticommType.{u} :=
  contraction_anticomm_proof


/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem contraction_linear_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.contraction_linearType.{u} :=
  contraction_linear_proof

/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem exteriorDerivative_eq_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.exteriorDerivative_eqType.{u} :=
  exteriorDerivative_eq_proof _h31

/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem exteriorDerivative_zero_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.exteriorDerivative_zeroType.{u} :=
  exteriorDerivative_zero_proof _h31 _h48


/-- Conditional draft, with the complete ordered upstream interface explicit. -/
theorem flowLieDerivative_eq_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.flowLieDerivative_eqType.{u} :=
  flowLieDerivative_eq_proof

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem operators_smooth_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.operators_smoothType.{u} :=
  operators_smooth_proof _h43 _h34 _h31

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem lie_commutes_d_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_dType.{u} :=
  lie_commutes_d_proof _h43 _h34 _h31

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem lie_evaluation_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.lie_evaluationType.{u} :=
  lie_evaluation_proof _h43 _h34 _h31 _h3 _h22 _h42 _h33

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem lie_commutes_contraction_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_contractionType.{u} :=
  lie_commutes_contraction_proof _h43 _h34 _h31 _h3 _h22 _h42 _h33 _h48

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem lie_commutes_lie_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.lie_commutes_lieType.{u} :=
  lie_commutes_lie_proof _h43 _h34 _h31 _h3 _h22 _h42 _h33 _h48

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem local_flow_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.local_flowType.{u} :=
  local_flow_proof _h43 _h34 _h31 _h33 _h42 _h3 _h22

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem flow_boundaryless_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.flow_boundarylessType.{u} :=
  flow_boundaryless_of_local_flow (local_flow_proof _h43 _h34 _h31 _h33 _h42 _h3 _h22)

/-- Conditional derivation under the complete ordered upstream interface. -/
theorem flow_boundary_conditional
    (_h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h50 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.Cartan.flow_boundaryType.{u} :=
  flow_boundary_of_local_flow (local_flow_proof _h43 _h34 _h31 _h33 _h42 _h3 _h22)

end SmoothManifolds.CartanResults

universe v8_closure_9fe534642897aaac_u0
theorem _root_.«SmoothManifolds».«CartanResults».«contraction_anticomm» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«contraction_anticommType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«contraction_anticomm_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«contraction_apply» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«contraction_applyType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«contraction_apply_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«contraction_linear» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«contraction_linearType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«contraction_linear_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«contraction_zero» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«contraction_zeroType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«contraction_zero_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«exteriorDerivative_eq» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«exteriorDerivative_eqType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«exteriorDerivative_eq_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«exteriorDerivative_zero» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«exteriorDerivative_zeroType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«exteriorDerivative_zero_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«flowLieDerivative_eq» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«flowLieDerivative_eqType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«flowLieDerivative_eq_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«flow_boundary» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«flow_boundaryType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«flow_boundary_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«flow_boundaryless» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«flow_boundarylessType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«flow_boundaryless_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«lie_commutes_contraction» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«lie_commutes_contractionType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«lie_commutes_contraction_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«lie_commutes_d» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«lie_commutes_dType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«lie_commutes_d_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«lie_commutes_lie» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«lie_commutes_lieType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«lie_commutes_lie_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«lie_evaluation» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«lie_evaluationType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«lie_evaluation_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«local_flow» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«local_flowType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«local_flow_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
theorem _root_.«SmoothManifolds».«CartanResults».«operators_smooth» : _root_.«Specs».«SmoothManifolds».«Ch07».«Cartan».«operators_smoothType».{v8_closure_9fe534642897aaac_u0} :=
  @_root_.«SmoothManifolds».«CartanResults».«operators_smooth_conditional».{v8_closure_9fe534642897aaac_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_9fe534642897aaac_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_9fe534642897aaac_u0})
