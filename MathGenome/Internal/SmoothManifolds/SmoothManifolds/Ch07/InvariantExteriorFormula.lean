import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.InvariantExteriorFormula
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
/-! Invariant evaluation of the exterior derivative (paper.tex 1520--1529).

The proof uses the analytic invariant formula, then identifies its ingredients
with the intrinsic germ tangent fibers and determinant-normalized exterior
fibers. In particular the fields are arbitrary, and unique differentiability
on a relatively open model domain retains the boundary case and dimension zero.
The exported helpers retain the exact ordered conditional-draft contract;
the original target names are reserved for the owner's later closed wrappers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SmoothManifolds.InvariantExteriorFormulaResults
open ModelData AtlasData MapData PartitionData TangentData TangentBundleData
  CovectorData ExteriorData ExteriorDerivativeData VectorFieldData LieBracketData
  Set Filter
open scoped Topology
universe u

/-- The analytic calculation on a unique-differentiability domain, with the
manuscript's ordered-pair signs. This makes no commutativity assumption. -/
theorem ambient_invariant_positive {n k : ℕ} {s : Set (Euclidean n)} {x : Euclidean n}
    {ω : Euclidean n → (Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ}
    {X : Fin (k+2) → Euclidean n → Euclidean n}
    (hω : DifferentiableWithinAt ℝ ω s x)
    (hX : ∀ i, DifferentiableWithinAt ℝ (X i) s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    extDerivWithin ω s x (fun i => X i x) =
      (∑ i : Fin (k+2), (-1 : ℝ)^i.val *
        fderivWithin ℝ (fun y => ω y (i.removeNth (fun j => X j y))) s x (X i x)) +
      ∑ i : Fin (k+1), ∑ j ∈ Finset.Ici i,
        (-1 : ℝ)^(i.val+j.val+1) *
          ω x (Matrix.vecCons (VectorField.lieBracketWithin ℝ (X i.castSucc) (X j.succ) s x)
            (j.removeNth (i.castSucc.removeNth (fun l => X l x)))) := by
  rw [extDerivWithin_apply_vectorField hω hX hs, sub_eq_add_neg]
  apply congrArg₂ (· + ·)
  · simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg,
      Int.cast_one, smul_eq_mul]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp [← Int.cast_smul_eq_zsmul ℝ, pow_succ]

/-- Degree zero has no bracket terms, even when the field is not constant. -/
theorem ambient_invariant_zero {n : ℕ} {s : Set (Euclidean n)} {x : Euclidean n}
    {ω : Euclidean n → (Euclidean n) [⋀^Fin 0]→L[ℝ] ℝ}
    (hω : DifferentiableWithinAt ℝ ω s x) (hs : UniqueDiffWithinAt ℝ s x)
    (X : Euclidean n → Euclidean n) :
    extDerivWithin ω s x (fun _ => X x) =
      fderivWithin ℝ (fun y => ω y Fin.elim0) s x (X x) := by
  have hz (v : Fin 0 → Euclidean n) : v = Fin.elim0 := Subsingleton.elim _ _
  simpa [Fin.sum_univ_succ, hz] using extDerivWithin_apply hω hs (fun _ => X x)

def coordinateWedge {n k : ℕ} (I : Index n k) : (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ :=
  { exteriorPower.alternatingMapLinearEquiv.symm
      (exteriorPower.pairingDual ℝ (Euclidean n) k (exteriorPower.ιMulti ℝ k
        (fun i => LinearMap.proj (Set.powersetCard.ofFinEmbEquiv.symm I i)))) with
    cont := by
      change Continuous (fun v => exteriorPower.pairingDual ℝ (Euclidean n) k
        (exteriorPower.ιMulti ℝ k (fun i => LinearMap.proj
          (Set.powersetCard.ofFinEmbEquiv.symm I i))) (exteriorPower.ιMulti ℝ k v))
      simp_rw [exteriorPower.pairingDual_ιMulti_ιMulti]
      fun_prop }

theorem coordinateWedge_apply {n k : ℕ} (I : Index n k) (v : Fin k → Euclidean n) :
    coordinateWedge I v = (Matrix.of (fun i j => v j (Set.powersetCard.ofFinEmbEquiv.symm I i))).det := by
  change exteriorPower.pairingDual ℝ (Euclidean n) k _ (exteriorPower.ιMulti ℝ k v) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

def synthesizeCoefficients {n k : ℕ} : (Index n k → ℝ) →ₗ[ℝ] (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ := by
  classical
  exact ∑ I : Index n k, (LinearMap.proj I).smulRight (coordinateWedge I)

@[simp] theorem synthesizeCoefficients_apply {n k : ℕ} (A : Index n k → ℝ) (v : Fin k → Euclidean n) :
    synthesizeCoefficients A v = ∑ I : Index n k, A I *
      (Matrix.of (fun i j => v j (Set.powersetCard.ofFinEmbEquiv.symm I i))).det := by
  classical
  simp [synthesizeCoefficients, ContinuousAlternatingMap.sum_apply, coordinateWedge_apply, smul_eq_mul]


section IntrinsicCoordinates
variable {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} (C : BundleOperationsData.CotangentBundle S)
  (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)

/-- Determinant evaluation of the increasing-coordinate-wedge expansion. -/
theorem evaluation_coordinates (ω : Field S k) (p : M) (hp : p ∈ c.source)
    (v : Fin k → TangentSpace S p) :
    evaluate (TangentSpace S p) k (ω p) v =
      synthesizeCoefficients (ExteriorData.coefficients C k c hc ω ⟨p, hp⟩)
        (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
  classical
  rw [FormPullbackResults.evaluate_eq_pairing,
    ExteriorAlgebraResults.coefficient_expansion C k c hc ω ⟨p, hp⟩]
  simp only [map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, synthesizeCoefficients_apply]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

/-- Simultaneous smoothness of the full finite vector of form coefficients.
The totalization is relevant only on the open source of c. -/
theorem coefficient_vector_smooth (B : FormBundle C k) (ω : Field S k)
    (hω : IsForm B ω) (p : M) (hp : p ∈ c.source) :
    FrameData.VectorSmoothAt S.smoothStructure.val
      (FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q)) p := by
  have h := (ExteriorAlgebraResults.smooth_iff_coefficients C k B ω).mp hω c hc
  exact (FrameData.VectorSmoothAt.pi (fun I => h I ⟨p, hp⟩)).totalize c.open_source

/-- Actual field-coordinate functions have the ambient-extension smoothness
property near every point of their chart source. -/
theorem field_coordinate_smooth (X : SmoothField C.tangent)
    (p : M) (hp : p ∈ c.source) :
    FrameData.VectorSmoothAt S.smoothStructure.val
      (LieBracketData.coefficients C.tangent X.val c hc) p := by
  have h := TangentBundle.chartFiber_smoothAt S C.tangent S
    (fun q => ⟨q, X.val q⟩) p c hc hp (X.smooth p)
  apply FrameData.VectorSmoothAt.congr h
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  rw [TangentBundle.chartFiber_eq S C.tangent c hc ⟨q, X.val q⟩ hq,
    LieBrackets.coefficients_eq X.val c hc q hq]

end IntrinsicCoordinates


/-- The evaluation polynomial is smooth, including the empty determinant. -/
theorem coefficient_evaluation_smooth {n k : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Index n k → ℝ) × (Fin k → Euclidean n) => synthesizeCoefficients q.1 q.2) := by
  classical
  simp only [synthesizeCoefficients_apply, Matrix.det_apply, Matrix.of_apply]
  fun_prop

/-- Evaluation of a smooth differential form on arbitrary smooth fields is an
actual smooth scalar function. No choice of commuting fields is involved. -/
theorem evaluation_smooth {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : BundleOperationsData.CotangentBundle S)
    (B : FormBundle C k) (ω : Field S k) (hω : IsForm B ω)
    (X : Fin k → SmoothField C.tangent) :
    ScalarSmooth S.smoothStructure.val
      (fun p => evaluate (TangentSpace S p) k (ω p) (fun i => (X i).val p)) := by
  intro p
  classical
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let A : M → Index n k → ℝ := FrameData.totalize
    (fun q : c.source => ExteriorData.coefficients C k c hc ω q)
  let Y : M → Fin k → Euclidean n := fun q i =>
    LieBracketData.coefficients C.tangent (X i).val c hc q
  have hA := coefficient_vector_smooth C c hc B ω hω p hp
  have hY := FrameData.VectorSmoothAt.pi
    (fun i => field_coordinate_smooth C c hc (X i) p hp)
  have h : FrameData.VectorSmoothAt S.smoothStructure.val (fun q => synthesizeCoefficients (A q) (Y q)) p :=
    (hA.prod hY).postcomp coefficient_evaluation_smooth
  apply (scalarContDiffAt_iff (⊤ : ℕ∞) _ _ p).mpr
  apply FrameData.VectorSmoothAt.congr h
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  rw [evaluation_coordinates C c hc ω q hq]
  congr 1
  · exact congrArg synthesizeCoefficients (FrameData.totalize_of_mem
      (fun r : c.source => ExteriorData.coefficients C k c hc ω r) q hq)
  · funext i
    exact LieBrackets.coefficients_eq (X i).val c hc q hq


/-- Forgetting the homogeneous degree commutes with a degree cast. -/
private theorem fiber_cast_val {V : Type u} [AddCommGroup V] [Module ℝ V]
    {d e : ℕ} (h : d = e) (α : Fiber V d) :
    (Eq.ndrec (motive := fun r => Fiber V r) α h).val = α.val := by
  subst h
  rfl

/-- Left multiplication by a one-form, with the source's arithmetic degree cast,
is exactly the decomposable wedge with that covector in the first slot. -/
theorem one_wedge_decomposable {V : Type u} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (α : Module.Dual ℝ V) (β : Fin k → Module.Dual ℝ V) :
    Eq.ndrec (motive := fun r => Fiber V r)
      (ExteriorData.wedge (V := V) (k := 1) (l := k)
        ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm α)
        (exteriorPower.ιMulti ℝ k β)) (Nat.add_comm 1 k) =
      exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β) := by
  have hα : (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm α =
      exteriorPower.ιMulti ℝ 1 (fun _ => α) := by
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).injective
    simp [exteriorPower.oneEquiv_ιMulti]
  apply Subtype.ext
  rw [fiber_cast_val]
  change ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm α).val *
    (exteriorPower.ιMulti ℝ k β).val = _
  rw [hα]
  change ExteriorAlgebra.ιMulti ℝ 1 (fun _ => α) * ExteriorAlgebra.ιMulti ℝ k β =
    ExteriorAlgebra.ιMulti ℝ (k+1) (Fin.cons α β)
  simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

/-- Laplace expansion is precisely the alternating evaluation of a left wedge. -/
theorem evaluate_cons_wedge {V : Type u} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (α : Module.Dual ℝ V) (β : Fin k → Module.Dual ℝ V)
    (v : Fin (k+1) → V) :
    evaluate V (k+1) (exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β)) v =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val * α (v i) *
        (Matrix.of (fun r j => β r (i.removeNth v j))).det := by
  rw [ExteriorAlgebraResults.determinant_normalization, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.of_apply, Fin.cons_zero,
    Fin.removeNth]
  rfl

section DerivativeCoordinates
variable {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} (C : BundleOperationsData.CotangentBundle S)
  (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)

/-- A germ of simultaneous ambient coefficient extensions computes the
coordinate derivative, also on the boundary of the model. -/
theorem coordinate_derivative_local_extension (ω : Field S k) (p : M) (hp : p ∈ c.source)
    (F : Euclidean n → Index n k → ℝ)
    (hF : DifferentiableAt ℝ F (c p).val)
    (heF : (fun q => F (c q).val) =ᶠ[𝓝 p]
      FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q)) :
    ExteriorDerivativeData.coordinateDerivative C k c hc ω p hp =
      coordinateExpression C k c hc p hp (fun I => fderiv ℝ (fun z => F z I) (c p).val) := by
  classical
  unfold ExteriorDerivativeData.coordinateDerivative
  congr 1
  funext I
  obtain ⟨V, hVeq, hV, hpV⟩ := mem_nhds_iff.mp heF
  let t : Set (ModelSpace n a) := c.target ∩ c.symm ⁻¹' V
  have ht : IsOpen t := c.symm.isOpen_inter_preimage hV
  have hpt : c p ∈ t := ⟨c.map_source hp, by
    change c.symm (c p) ∈ V
    rwa [c.left_inv hp]⟩
  obtain ⟨W, hW, htW⟩ := isOpen_induced_iff.mp ht
  have hpW : (c p).val ∈ W := by change c p ∈ Subtype.val ⁻¹' W; rwa [htW]
  have hpeq : (c p).val ∈ Subtype.val '' c.target := ⟨c p, c.map_source hp, rfl⟩
  have he : ambientCoefficient C k c hc ω I =ᶠ[𝓝[Subtype.val '' c.target] (c p).val]
      (fun z => F z I) := by
    filter_upwards [nhdsWithin_le_nhds (hW.mem_nhds hpW), self_mem_nhdsWithin] with z hzW hz
    obtain ⟨z, hz, rfl⟩ := hz
    have hzt : z ∈ t := by rw [← htW]; exact hzW
    have hv : F (c (c.symm z)).val = FrameData.totalize
        (fun q : c.source => ExteriorData.coefficients C k c hc ω q) (c.symm z) := hVeq hzt.2
    rw [FrameData.totalize_of_mem _ _ (c.map_target hz), c.right_inv hz] at hv
    simpa only [ambientCoefficient, dite_eq_left z.property, dite_eq_left hz] using (congrFun hv I).symm
  rw [he.fderivWithin_eq_of_mem hpeq]
  exact ((differentiableAt_pi.mp hF) I).fderivWithin (uniqueDiffOn_modelDomain c.open_target _ hpeq)

end DerivativeCoordinates


/-- Evaluation at a fixed tuple, bundled to commute with homogeneous sums. -/
def evaluateAt {V : Type u} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (v : Fin k → V) : Fiber V k →ₗ[ℝ] ℝ where
  toFun α := evaluate V k α v
  map_add' α β := by simp [FormPullbackResults.evaluate_eq_pairing]
  map_smul' r α := by simp [FormPullbackResults.evaluate_eq_pairing]

@[simp] theorem evaluateAt_apply {V : Type u} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (v : Fin k → V) (α : Fiber V k) : evaluateAt v α = evaluate V k α v := rfl

/-- Transport between equal homogeneous degrees is linear. -/
def degreeCast {V : Type u} [AddCommGroup V] [Module ℝ V]
    {d e : ℕ} (h : d = e) : Fiber V d ≃ₗ[ℝ] Fiber V e := by
  subst h
  exact LinearEquiv.refl ℝ (Fiber V d)

@[simp] theorem degreeCast_apply {V : Type u} [AddCommGroup V] [Module ℝ V]
    {d e : ℕ} (h : d = e) (α : Fiber V d) :
    degreeCast h α = Eq.ndrec (motive := fun r => Fiber V r) α h := by
  subst h
  rfl

/-- The coordinate expression evaluated on arbitrary tangent vectors is the
alternating sum of the coefficient derivatives on their coordinate vectors. -/
theorem coordinate_expression_evaluate {n k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : BundleOperationsData.CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source)
    (A : Index n k → Euclidean n →L[ℝ] ℝ)
    (v : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1) (coordinateExpression C k c hc p hp A) v =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        synthesizeCoefficients (fun I => A I (C.tangent.fiberCoordinates.equiv c hc p hp (v i)))
          (i.removeNth (fun j => C.tangent.fiberCoordinates.equiv c hc p hp (v j))) := by
  classical
  let Y := fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)
  let D := fun I : Index n k => fun i : Fin (k+1) =>
    (Matrix.of (fun r j => Y (i.succAbove j) (Set.powersetCard.ofFinEmbEquiv.symm I r))).det
  unfold coordinateExpression
  rw [← degreeCast_apply (V := TangentSpace S p) (Nat.add_comm 1 k)]
  change evaluateAt v ((degreeCast (V := TangentSpace S p) (Nat.add_comm 1 k))
    (∑ I : Index n k, ∑ j : Fin n, (A I (Pi.single j 1)) •
      ExteriorData.wedge (V := TangentSpace S p) (k := 1) (l := k)
        ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (coordinateCovector C.tangent.fiberCoordinates c hc p hp j))
        (exteriorPower.ιMulti ℝ k (fun r =>
          coordinateCovector C.tangent.fiberCoordinates c hc p hp
            (Set.powersetCard.ofFinEmbEquiv.symm I r))))) = _
  simp only [map_sum, map_smul, degreeCast_apply, one_wedge_decomposable,
    evaluateAt_apply, evaluate_cons_wedge, smul_eq_mul]
  change (∑ I : Index n k, ∑ j : Fin n, A I (Pi.single j 1) *
    ∑ i : Fin (k+1), (-1 : ℝ)^i.val * Y i j * D I i) = _
  simp only [Finset.mul_sum, synthesizeCoefficients_apply]
  calc
    (∑ I : Index n k, ∑ j : Fin n, ∑ i : Fin (k+1),
        A I (Pi.single j 1) * ((-1 : ℝ)^i.val * Y i j * D I i)) =
      ∑ i : Fin (k+1), ∑ I : Index n k, ∑ j : Fin n,
        A I (Pi.single j 1) * ((-1 : ℝ)^i.val * Y i j * D I i) := by
          simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
            (t := (Finset.univ : Finset (Fin (k+1))))]
          rw [Finset.sum_comm]
    _ = ∑ i : Fin (k+1), ∑ I : Index n k,
        (-1 : ℝ)^i.val * (A I (Y i) * D I i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro I _
      have hexp : Y i = ∑ j : Fin n, Y i j • Pi.single j (1 : ℝ) := by
        ext j
        simp [Pi.single_apply, Finset.sum_apply]
      conv_rhs => rw [hexp, map_sum]
      simp only [map_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rfl

/-- The preceding algebraic sum is Mathlib's analytic exterior derivative of
the synthesized coefficient extension. -/
theorem coordinate_derivative_evaluation {n k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : BundleOperationsData.CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : M) (hp : p ∈ c.source)
    (F : Euclidean n → Index n k → ℝ)
    (hF : DifferentiableAt ℝ F (c p).val)
    (heF : (fun q => F (c q).val) =ᶠ[𝓝 p]
      FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q))
    (v : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1)
        (ExteriorDerivativeData.coordinateDerivative C k c hc ω p hp) v =
      extDeriv (fun z => synthesizeCoefficients (F z)) (c p).val
        (fun i => C.tangent.fiberCoordinates.equiv c hc p hp (v i)) := by
  classical
  rw [coordinate_derivative_local_extension C c hc ω p hp F hF heF,
    coordinate_expression_evaluate]
  let L : (Index n k → ℝ) →L[ℝ] (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ :=
    synthesizeCoefficients.toContinuousLinearMap
  change _ = ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (fun z => L (F z)) (c p).val) _
  rw [show fderiv ℝ (fun z => L (F z)) (c p).val =
      L.comp (fderiv ℝ F (c p).val) from
      (L.hasFDerivAt.comp (c p).val hF.hasFDerivAt).fderiv,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.comp_apply, ← Int.cast_smul_eq_zsmul ℝ,
    Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg (fun A : Index n k → ℝ => synthesizeCoefficients A _)
  funext I
  exact congrArg (fun T => T (C.tangent.fiberCoordinates.equiv c hc p hp (v i)))
    (fderiv_apply hF I)


/-- Synthesis and evaluation preserve a simultaneous local ambient extension.
This supplies the scalar germs differentiated in the invariant formula. -/
theorem synthesized_evaluation_extension {n k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : BundleOperationsData.CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (X : Fin k → SmoothField C.tangent)
    (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean n))
    (F : Euclidean n → Index n k → ℝ) (W : Fin k → Euclidean n → Euclidean n)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) U)
    (heF : (fun q => F (c q).val) =ᶠ[𝓝 p]
      FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q))
    (heW : ∀ i, (fun q => W i (c q).val) =ᶠ[𝓝 p]
      LieBracketData.coefficients C.tangent (X i).val c hc) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => synthesizeCoefficients (F z) (fun i => W i z)) U ∧
    (fun q => synthesizeCoefficients (F (c q).val) (fun i => W i (c q).val)) =ᶠ[𝓝 p]
      (fun q => evaluate (TangentSpace S q) k (ω q) (fun i => (X i).val q)) := by
  classical
  constructor
  · exact coefficient_evaluation_smooth.comp_contDiffOn (hF.prodMk (contDiffOn_pi.mpr hW))
  · filter_upwards [heF, Filter.eventually_all.mpr heW, c.open_source.mem_nhds hp] with q hFq hWq hq
    rw [hFq, FrameData.totalize_of_mem _ _ hq, evaluation_coordinates C c hc ω q hq]
    congr 1
    funext i
    exact (hWq i).trans (LieBrackets.coefficients_eq (X i).val c hc q hq)

/-- Intrinsic bracket coordinates agree with the analytic bracket of any smooth
ambient representatives, without requiring fields to commute. -/
theorem bracket_coordinates_extension {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source)
    (W Z : Euclidean n → Euclidean n)
    (hW : DifferentiableAt ℝ W (c p).val) (hZ : DifferentiableAt ℝ Z (c p).val)
    (heW : (fun q => W (c q).val) =ᶠ[𝓝 p] LieBracketData.coefficients B X.val c hc)
    (heZ : (fun q => Z (c q).val) =ᶠ[𝓝 p] LieBracketData.coefficients B Y.val c hc) :
    B.fiberCoordinates.equiv c hc p hp ((b X Y).val p) =
      VectorField.lieBracket ℝ W Z (c p).val := by
  have h := (LieBrackets.bracket_coordinates S B b hb X Y).2 c hc p hp
    (fderiv ℝ W (c p).val) (fderiv ℝ Z (c p).val)
    ⟨W, hW.hasFDerivAt, heW⟩ ⟨Z, hZ.hasFDerivAt, heZ⟩
  ext j
  rw [← LieBrackets.coefficients_eq (b X Y).val c hc p hp, h j]
  rw [VectorField.lieBracket, LieBrackets.coordinate_commutator_sum]
  rw [heW.eq_of_nhds, heZ.eq_of_nhds]

private theorem empty_tuple {T : Sort*} (f : Fin 0 → T) : f = Fin.elim0 :=
  Subsingleton.elim _ _

/-- The degree-zero invariant identity in the original intrinsic fibers. -/
theorem invariant_zero_of_local_extensions :
    Specs.SmoothManifolds.Ch07.InvariantExteriorFormula.invariant_zeroType.{u} := by
  intro n a M _ S C B ω η hω hη X
  let f : M → ℝ := fun p => evaluate (TangentSpace S p) 0 (ω p) Fin.elim0
  have hf : ScalarSmooth S.smoothStructure.val f :=
    evaluation_smooth C B ω hω (Fin.elim0 : Fin 0 → SmoothField C.tangent)
  refine ⟨f, hf, fun _ => rfl, ?_⟩
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ :=
    (coefficient_vector_smooth C c hc B ω hω p hp).2 c hc hp
  have hFd : DifferentiableAt ℝ F (c p).val :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  let L : (Index n 0 → ℝ) →L[ℝ] (Euclidean n) [⋀^Fin 0]→L[ℝ] ℝ :=
    synthesizeCoefficients.toContinuousLinearMap
  have hΩ : DifferentiableAt ℝ (fun z => synthesizeCoefficients (F z)) (c p).val :=
    L.differentiableAt.comp (c p).val hFd
  have hG := synthesized_evaluation_extension C c hc ω
    (Fin.elim0 : Fin 0 → SmoothField C.tangent) p hp U F Fin.elim0 hF
    (fun i => Fin.elim0 i) heF (fun i => Fin.elim0 i)
  simp only [empty_tuple] at hG
  have hg : GermChartExtension S p c (functionGerm S f hf p)
      (fun z => synthesizeCoefficients (F z) Fin.elim0) :=
    ⟨⟨U, hU, hpU, hG.1⟩, Germ.coe_eq.mpr hG.2⟩
  rw [hη c hc p hp, coordinate_derivative_evaluation C c hc ω p hp F hFd heF]
  calc
    extDeriv (fun z => synthesizeCoefficients (F z)) (c p).val
        (fun _ => C.tangent.fiberCoordinates.equiv c hc p hp (X.val p)) =
      fderiv ℝ (fun z => synthesizeCoefficients (F z) Fin.elim0) (c p).val
        (C.tangent.fiberCoordinates.equiv c hc p hp (X.val p)) := by
          simpa only [extDerivWithin_univ, fderivWithin_univ] using
            ambient_invariant_zero (s := Set.univ) hΩ.differentiableWithinAt
              (uniqueDiffWithinAt_univ) (fun _ => C.tangent.fiberCoordinates.equiv c hc p hp (X.val p))
    _ = _ := (VectorFields.tangent_action_coordinates S C.tangent.fiberCoordinates
      p c hc hp (X.val p) (functionGerm S f hf p) _ hg).symm


/-- The complete positive-degree invariant identity for arbitrary smooth fields,
proved by the local analytic calculation and intrinsic coordinate bridges. -/
theorem invariant_positive_of_local_extensions :
    Specs.SmoothManifolds.Ch07.InvariantExteriorFormula.invariant_positiveType.{u} := by
  intro n a M _ S C k B ω η hω hη b hb X
  classical
  let f : Fin (k+2) → M → ℝ := fun i p =>
    evaluate (TangentSpace S p) (k+1) (ω p) (i.removeNth (fun j => (X j).val p))
  have hf (i : Fin (k+2)) : ScalarSmooth S.smoothStructure.val (f i) :=
    evaluation_smooth C B ω hω (fun j => X (i.succAbove j))
  refine ⟨f, hf, fun _ _ => rfl, ?_⟩
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ :=
    (coefficient_vector_smooth C c hc B ω hω p hp).2 c hc hp
  choose V hV hpV W hW heW using
    (fun i => (field_coordinate_smooth C c hc (X i) p hp).2 c hc hp)
  let T := U ∩ ⋂ i, V i
  have hT : IsOpen T := hU.inter (isOpen_iInter_of_finite hV)
  have hpT : (c p).val ∈ T := ⟨hpU, mem_iInter.mpr hpV⟩
  have hFT : ContDiffOn ℝ (⊤ : ℕ∞) F T := hF.mono inter_subset_left
  have hWT (i) : ContDiffOn ℝ (⊤ : ℕ∞) (W i) T :=
    (hW i).mono (fun _ h => mem_iInter.mp h.2 i)
  have hFd : DifferentiableAt ℝ F (c p).val :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hWd (i) : DifferentiableAt ℝ (W i) (c p).val :=
    ((hW i).contDiffAt ((hV i).mem_nhds (hpV i))).differentiableAt (by simp)
  let L : (Index n (k+1) → ℝ) →L[ℝ] (Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ :=
    synthesizeCoefficients.toContinuousLinearMap
  have hΩ : DifferentiableAt ℝ (fun z => synthesizeCoefficients (F z)) (c p).val :=
    L.differentiableAt.comp (c p).val hFd
  have hX (i) : C.tangent.fiberCoordinates.equiv c hc p hp ((X i).val p) = W i (c p).val := by
    rw [← LieBrackets.coefficients_eq (X i).val c hc p hp]
    exact (heW i).eq_of_nhds.symm
  have hact (i) :
      ((X i).val p).val (functionGerm S (f i) (hf i) p) =
        fderiv ℝ (fun z => synthesizeCoefficients (F z) (i.removeNth (fun j => W j z))) (c p).val
          (W i (c p).val) := by
    have hG := synthesized_evaluation_extension C c hc ω
      (fun j => X (i.succAbove j)) p hp T F (fun j => W (i.succAbove j)) hFT
      (fun j => hWT (i.succAbove j)) heF (fun j => heW (i.succAbove j))
    have hg : GermChartExtension S p c (functionGerm S (f i) (hf i) p)
        (fun z => synthesizeCoefficients (F z) (i.removeNth (fun j => W j z))) :=
      ⟨⟨T, hT, hpT, hG.1⟩, Germ.coe_eq.mpr hG.2⟩
    rw [VectorFields.tangent_action_coordinates S C.tangent.fiberCoordinates p c hc hp
      ((X i).val p) _ _ hg, hX i]
  have hbracket (i j : Fin (k+1)) :
      evaluate (TangentSpace S p) (k+1) (ω p)
        (Matrix.vecCons ((b (X i.castSucc) (X j.succ)).val p)
          (j.removeNth (i.castSucc.removeNth (fun l => (X l).val p)))) =
      synthesizeCoefficients (F (c p).val)
        (Matrix.vecCons (VectorField.lieBracket ℝ (W i.castSucc) (W j.succ) (c p).val)
          (j.removeNth (i.castSucc.removeNth (fun l => W l (c p).val)))) := by
    rw [evaluation_coordinates C c hc ω p hp,
      ← FrameData.totalize_of_mem
        (fun q : c.source => ExteriorData.coefficients C (k+1) c hc ω q) p hp,
      ← heF.eq_of_nhds]
    apply congrArg (fun v => synthesizeCoefficients (F (c p).val) v)
    funext l
    refine Fin.cases ?_ (fun r => ?_) l
    · exact bracket_coordinates_extension C.tangent b hb (X i.castSucc) (X j.succ)
        c hc p hp (W i.castSucc) (W j.succ) (hWd _) (hWd _) (heW _) (heW _)
    · exact hX _
  rw [hη c hc p hp, coordinate_derivative_evaluation C c hc ω p hp F hFd heF]
  simp only [hX, hact, hbracket]
  simpa only [extDerivWithin_univ, fderivWithin_univ, VectorField.lieBracketWithin_univ] using
    ambient_invariant_positive (s := Set.univ) hΩ.differentiableWithinAt
      (fun i => (hWd i).differentiableWithinAt) uniqueDiffWithinAt_univ


/-- Conditional-draft interface, retaining all supplied premises in order. -/
theorem invariant_zero_conditional
    (_h_ambient_coefficient_leibniz : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h_intrinsic_derivative_leibniz : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h_coefficient_alternating_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h_intrinsic_derivative_square : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h_ambient_derivative_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h_ambient_derivative_square : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h_ambient_dimension_zero : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h_ambient_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h_axioms_locality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h_axioms_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h_axioms_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h_axioms_zero_germ : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h_c1_derivative_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h_c1_derivative_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h_c1_derivative_section_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h_c1_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h_c1_restriction : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h_closed_embedding_proper : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h_closed_face_inclusion_proper : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h_continuous_field_section_iff : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h_coordinate_derivative_pullback : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h_coordinate_formula_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h_coordinate_locality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h_derivative_add : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h_derivative_compact_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h_derivative_locality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h_derivative_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h_derivative_smooth : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h_derivative_smul : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h_derivative_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h_derivative_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h_extension_independence : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h_function_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h_global_coordinates : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h_model_extension_independence : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h_orthant_extDerivWithin_pullback : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h_orthant_extension_independence : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h_proper_pullback_compact_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h_pullback_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h_pullback_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h_regular_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h_smooth_coefficients : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h_smooth_family_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h_smooth_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h_smooth_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h_tautological_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h_uniqueDiffOn_orthant : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h_zero_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h_zero_dim_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h_zero_dim_family_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.InvariantExteriorFormula.invariant_zeroType.{u} :=
  invariant_zero_of_local_extensions

/-- Conditional-draft interface, retaining all supplied premises in order. -/
theorem invariant_positive_conditional
    (_h_ambient_coefficient_leibniz : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (_h_intrinsic_derivative_leibniz : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (_h_coefficient_alternating_bridge : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (_h_intrinsic_derivative_square : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (_h_ambient_derivative_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (_h_ambient_derivative_square : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (_h_ambient_dimension_zero : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (_h_ambient_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (_h_axioms_locality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (_h_axioms_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (_h_axioms_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (_h_axioms_zero_germ : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (_h_c1_derivative_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (_h_c1_derivative_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (_h_c1_derivative_section_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (_h_c1_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (_h_c1_restriction : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (_h_closed_embedding_proper : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (_h_closed_face_inclusion_proper : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (_h_continuous_field_section_iff : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (_h_coordinate_derivative_pullback : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (_h_coordinate_formula_extension : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (_h_coordinate_locality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (_h_derivative_add : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (_h_derivative_compact_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (_h_derivative_locality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (_h_derivative_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (_h_derivative_smooth : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (_h_derivative_smul : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (_h_derivative_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (_h_derivative_unique : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (_h_extension_independence : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (_h_function_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (_h_global_coordinates : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (_h_model_extension_independence : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (_h_orthant_extDerivWithin_pullback : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (_h_orthant_extension_independence : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (_h_proper_pullback_compact_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (_h_pullback_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (_h_pullback_support : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (_h_regular_continuous : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (_h_smooth_coefficients : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (_h_smooth_family_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (_h_smooth_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (_h_smooth_regular : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (_h_tautological_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (_h_uniqueDiffOn_orthant : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (_h_zero_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (_h_zero_dim_derivative : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (_h_zero_dim_family_exists : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u})
    : Specs.SmoothManifolds.Ch07.InvariantExteriorFormula.invariant_positiveType.{u} :=
  invariant_positive_of_local_extensions

end SmoothManifolds.InvariantExteriorFormulaResults

universe v8_closure_4a8f8380421ae355_u0
theorem _root_.«SmoothManifolds».«InvariantExteriorFormulaResults».«invariant_positive» : _root_.«Specs».«SmoothManifolds».«Ch07».«InvariantExteriorFormula».«invariant_positiveType».{v8_closure_4a8f8380421ae355_u0} :=
  @_root_.«SmoothManifolds».«InvariantExteriorFormulaResults».«invariant_positive_conditional».{v8_closure_4a8f8380421ae355_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_4a8f8380421ae355_u0})
theorem _root_.«SmoothManifolds».«InvariantExteriorFormulaResults».«invariant_zero» : _root_.«Specs».«SmoothManifolds».«Ch07».«InvariantExteriorFormula».«invariant_zeroType».{v8_closure_4a8f8380421ae355_u0} :=
  @_root_.«SmoothManifolds».«InvariantExteriorFormulaResults».«invariant_zero_conditional».{v8_closure_4a8f8380421ae355_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_4a8f8380421ae355_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_4a8f8380421ae355_u0})
