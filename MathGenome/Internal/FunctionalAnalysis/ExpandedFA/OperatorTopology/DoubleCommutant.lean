import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.DoubleCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.Composition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
The double commutant theorem, including simultaneous finite-vector approximation.
The finite-amplification proof below is adapted from the publicly available
OAI/Analysis/FactorGeneration/Bicommutant.lean (openai/math, retrieved 2026-11-06).
It uses the projection onto the closed simultaneous orbit in a finite Hilbert
sum. No separability assumption or bounded-approximation theorem is used.
-/
namespace ExpandedFA.OperatorTopology
noncomputable section
namespace DoubleCommutantProof

section
open scoped BigOperators
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

abbrev FiniteHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

def diagonalOperator (T : H →L[𝕜] H) : FiniteHilbert ι H →L[𝕜] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[𝕜] H) (x : FiniteHilbert ι H) (i : ι) :
    diagonalOperator T x i=T (x i) := rfl

theorem diagonalOperator_star (T : H →L[𝕜] H) :
    diagonalOperator (ι := ι) (star T)=star (diagonalOperator (ι := ι) T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left 𝕜
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,diagonalOperator_apply,
    ContinuousLinearMap.adjoint_inner_right]

def tupleOrbitMap (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (x : FiniteHilbert ι H) :
    S →ₗ[𝕜] FiniteHilbert ι H where
  toFun a := diagonalOperator a.val x
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl

def tupleOrbitClosure (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (x : FiniteHilbert ι H) :
    Submodule 𝕜 (FiniteHilbert ι H) := (tupleOrbitMap S x).range.topologicalClosure

instance tupleOrbitClosure_complete (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (x : FiniteHilbert ι H) : CompleteSpace (tupleOrbitClosure S x) :=
  inferInstanceAs (CompleteSpace (tupleOrbitMap S x).range.topologicalClosure)

theorem mem_tupleOrbitClosure (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (x : FiniteHilbert ι H) : x ∈ tupleOrbitClosure S x := by
  apply Submodule.le_topologicalClosure
  refine ⟨1,?_⟩
  ext i
  rfl

theorem tupleOrbitClosure_invariant (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (x : FiniteHilbert ι H) (a : S) {y : FiniteHilbert ι H}
    (hy : y ∈ tupleOrbitClosure S x) : diagonalOperator a.val y ∈ tupleOrbitClosure S x := by
  have h : (tupleOrbitMap S x).range.topologicalClosure ≤
      (tupleOrbitClosure S x).comap (diagonalOperator a.val).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨a*b,?_⟩
      ext i
      rfl
    · exact (Submodule.isClosed_topologicalClosure _).preimage (diagonalOperator a.val).continuous
  exact h hy

theorem starProjection_commutes_of_invariant (K : Submodule 𝕜 H) [K.HasOrthogonalProjection]
    (T : H →L[𝕜] H) (hT : ∀ x ∈ K,T x ∈ K) (hstar : ∀ x ∈ K,star T x ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext x
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (K.starProjection_apply_mem x)
  · intro y hy
    change inner 𝕜 (T x-T (K.starProjection x)) y=0
    rw [← map_sub]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact K.starProjection_inner_eq_zero x _ (hstar y hy)

theorem tupleOrbitProjection_commutes (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (x : FiniteHilbert ι H) (a : S) :
    (tupleOrbitClosure S x).starProjection*diagonalOperator a.val=
      diagonalOperator a.val*(tupleOrbitClosure S x).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => tupleOrbitClosure_invariant S x a hy
  · rw [← diagonalOperator_star]
    exact fun y hy => tupleOrbitClosure_invariant S x (star a) hy

variable [DecidableEq ι]

def tupleSingle (i : ι) : H →L[𝕜] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single 𝕜 (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem tupleSingle_apply (i j : ι) (x : H) :
    tupleSingle (𝕜 := 𝕜) i x j=(Pi.single i x : ι → H) j := rfl

omit [CompleteSpace H] in
theorem tuple_eq_sum_single (x : FiniteHilbert ι H) :
    x=∑ i,tupleSingle (𝕜 := 𝕜) i (x i) := by
  ext j
  simp [WithLp.ofLp_sum,tupleSingle_apply,Pi.single_apply]

omit [CompleteSpace H] [Fintype ι] in
theorem diagonalOperator_single (T : H →L[𝕜] H) (i : ι) (x : H) :
    diagonalOperator T (tupleSingle (𝕜 := 𝕜) i x)=tupleSingle (𝕜 := 𝕜) i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

def operatorEntry (Q : FiniteHilbert ι H →L[𝕜] FiniteHilbert ι H) (i j : ι) : H →L[𝕜] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (Q.comp (tupleSingle (𝕜 := 𝕜) j))

omit [Fintype ι] in
theorem operatorEntry_mem_centralizer (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (Q : FiniteHilbert ι H →L[𝕜] FiniteHilbert ι H)
    (hQ : ∀ a : S,Q*diagonalOperator a.val=diagonalOperator a.val*Q) (i j : ι) :
    operatorEntry Q i j ∈ Set.centralizer (S : Set (H →L[𝕜] H)) := by
  intro a ha
  ext z
  change a (Q (tupleSingle (𝕜 := 𝕜) j z) i)=Q (tupleSingle (𝕜 := 𝕜) j (a z)) i
  have h := congrArg (fun T : FiniteHilbert ι H →L[𝕜] FiniteHilbert ι H =>
    T (tupleSingle (𝕜 := 𝕜) j z) i) (hQ ⟨a,ha⟩)
  simpa only [mul_apply_eq_comp,diagonalOperator_apply,
    diagonalOperator_single] using h.symm

omit [CompleteSpace H] in
theorem diagonalOperator_commutes_of_entries (T : H →L[𝕜] H)
    (Q : FiniteHilbert ι H →L[𝕜] FiniteHilbert ι H)
    (h : ∀ i j,operatorEntry Q i j*T=T*operatorEntry Q i j) :
    Q*diagonalOperator T=diagonalOperator T*Q := by
  ext x i
  rw [tuple_eq_sum_single (𝕜 := 𝕜) x]
  simp only [map_sum,mul_apply_eq_comp,diagonalOperator_single]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,diagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : H →L[𝕜] H => a (x j)) (h i j)

theorem bicommutant_tuple_mem_closure (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (T : H →L[𝕜] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[𝕜] H))))
    (x : FiniteHilbert ι H) : diagonalOperator T x ∈ tupleOrbitClosure S x := by
  let Q := (tupleOrbitClosure S x).starProjection
  have hcomm : Q*diagonalOperator T=diagonalOperator T*Q :=
    diagonalOperator_commutes_of_entries T Q (fun i j => hT _
      (operatorEntry_mem_centralizer S Q (tupleOrbitProjection_commutes S x) i j))
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun a : FiniteHilbert ι H →L[𝕜] FiniteHilbert ι H => a x) hcomm
  change Q (diagonalOperator T x)=diagonalOperator T (Q x) at h
  rw [show Q x=x from Submodule.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure S x)] at h
  exact h

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous approximation constructs a strongly convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem bicommutant_finite_strong_approximation (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (T : H →L[𝕜] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[𝕜] H))))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S,∀ x ∈ s,‖T x-a.val x‖ < ε := by
  classical
  let x : FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := bicommutant_tuple_mem_closure S T hT x
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨a,?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le (diagonalOperator T x-tupleOrbitMap S x a) (⟨y,hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

theorem bicommutant_exists_strong_net (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    (T : H →L[𝕜] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[𝕜] H)))) :
    ∃ a : Finset H × ℕ → S,∀ x : H,
      Tendsto (fun d => (a d).val x) atTop (𝓝 (T x)) := by
  classical
  have hex (d : Finset H × ℕ) := bicommutant_finite_strong_approximation S T hT d.1
    (1/((d.2 : ℝ)+1)) (by positivity)
  choose a ha using hex
  refine ⟨a,?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun d : Finset H × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun d => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H),0)] with d hd
  rw [dist_comm,dist_eq_norm]
  exact (ha d x (hd.1 (Finset.mem_singleton_self x))).le

end
end DoubleCommutantProof
end

open scoped Topology InnerProductSpace
open Filter

/-- The shared Part I topologies have the advertised convergence tests. -/
theorem hilbert_operator_convergence : DoubleCommutantSpec.ConvergenceTests := by
  intro H _ _ _ ι l f T
  exact ⟨strong_tendsto_iff ℂ H H ι l f T, hilbert_tendsto_iff ℂ H H ι l f T⟩

/-- No norm bound is needed: adjunction is globally WOT continuous. -/
theorem weak_adjoint_continuous : DoubleCommutantSpec.AdjointContinuous := by
  intro H _ _ _
  let : TopologicalSpace (H →L[ℂ] H) := weakTopology ℂ H H
  apply continuous_iff_continuousAt.mpr
  intro T
  apply (hilbert_tendsto_iff ℂ H H _ (𝓝 T) (fun A => star A) (star T)).mpr
  intro x y
  have h := (hilbert_tendsto_iff ℂ H H _ (𝓝 T) id T).mp tendsto_id y x
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← starRingEnd_apply, inner_conj_symm, id_eq] using h.star

/-- Multiplication by each fixed factor is continuous everywhere. -/
theorem hilbert_separate_multiplication : DoubleCommutantSpec.SeparateMultiplication := by
  intro H _ _ _ A
  exact ⟨strong_comp_left_continuous ℂ H H H A,
    strong_comp_right_continuous ℂ H H H A,
    weak_comp_left_continuous ℂ H H H A,
    weak_comp_right_continuous ℂ H H H A⟩

theorem bicommutant_finite_approximation : DoubleCommutantSpec.FiniteApproximation := by
  intro H _ _ _ A T hT s ε hε
  obtain ⟨a, ha⟩ := DoubleCommutantProof.bicommutant_finite_strong_approximation A T hT s ε hε
  exact ⟨a, a.property, ha⟩

/-- Every commutant is closed in the canonical WOT. -/
theorem weak_closed_centralizer {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (s : Set (H →L[𝕜] H)) :
    @IsClosed _ (weakTopology 𝕜 H H) (Set.centralizer s) := by
  let : TopologicalSpace (H →L[𝕜] H) := weakTopology 𝕜 H H
  let : T2Space (H →L[𝕜] H) := weak_hausdorff 𝕜 H H
  let : SeparatelyContinuousMul (H →L[𝕜] H) := {
    continuous_const_mul := weak_comp_left_continuous 𝕜 H H H _
    continuous_mul_const := weak_comp_right_continuous 𝕜 H H H _ }
  exact Set.isClosed_centralizer s

/-- The finite-vector argument yields the full strong closure, not merely
one-vector orbit density. -/
theorem bicommutant_subset_strong_closure {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    Set.centralizer (Set.centralizer (A : Set (H →L[𝕜] H))) ⊆
      @closure _ (strongTopology 𝕜 H H) (A : Set (H →L[𝕜] H)) := by
  classical
  intro T hT
  obtain ⟨a, ha⟩ := DoubleCommutantProof.bicommutant_exists_strong_net A T hT
  let : TopologicalSpace (H →L[𝕜] H) := strongTopology 𝕜 H H
  exact isClosed_closure.mem_of_tendsto
    ((strong_tendsto_iff 𝕜 H H _ atTop (fun d => (a d).val) T).mpr ha)
    (Eventually.of_forall fun d => subset_closure (a d).property)

/-- The von Neumann double commutant theorem for an arbitrary complex Hilbert
space and an arbitrary unital star subalgebra of bounded operators. -/
theorem double_commutant : DoubleCommutantSpec.DoubleCommutant := by
  intro H _ _ _ A
  have hWC : @closure _ (weakTopology ℂ H H) (A : Set (H →L[ℂ] H)) ⊆
      Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    let : TopologicalSpace (H →L[ℂ] H) := weakTopology ℂ H H
    exact closure_minimal (fun T hT B hB => (hB T hT).symm)
      (weak_closed_centralizer _)
  have hSW : @closure _ (strongTopology ℂ H H) (A : Set (H →L[ℂ] H)) ⊆
      @closure _ (weakTopology ℂ H H) (A : Set (H →L[ℂ] H)) := by
    exact closure.mono (topology_comparison ℂ H H).2
  have hCS := bicommutant_subset_strong_closure A
  exact ⟨Set.Subset.antisymm hSW (hWC.trans hCS),
    Set.Subset.antisymm hWC (hCS.trans hSW)⟩

/-- The shared Part I topologies have the advertised convergence tests. -/
theorem real_hilbert_operator_convergence : DoubleCommutantSpec.RealConvergenceTests := by
  intro H _ _ _ ι l f T
  exact ⟨strong_tendsto_iff ℝ H H ι l f T, hilbert_tendsto_iff ℝ H H ι l f T⟩

/-- No norm bound is needed: adjunction is globally WOT continuous. -/
theorem real_weak_adjoint_continuous : DoubleCommutantSpec.RealAdjointContinuous := by
  intro H _ _ _
  let : TopologicalSpace (H →L[ℝ] H) := weakTopology ℝ H H
  apply continuous_iff_continuousAt.mpr
  intro T
  apply (hilbert_tendsto_iff ℝ H H _ (𝓝 T) (fun A => star A) (star T)).mpr
  intro x y
  have h := (hilbert_tendsto_iff ℝ H H _ (𝓝 T) id T).mp tendsto_id y x
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← starRingEnd_apply, inner_conj_symm, id_eq] using h.star

/-- Multiplication by each fixed factor is continuous everywhere. -/
theorem real_hilbert_separate_multiplication : DoubleCommutantSpec.RealSeparateMultiplication := by
  intro H _ _ _ A
  exact ⟨strong_comp_left_continuous ℝ H H H A,
    strong_comp_right_continuous ℝ H H H A,
    weak_comp_left_continuous ℝ H H H A,
    weak_comp_right_continuous ℝ H H H A⟩

theorem real_bicommutant_finite_approximation : DoubleCommutantSpec.RealFiniteApproximation := by
  intro H _ _ _ A T hT s ε hε
  obtain ⟨a, ha⟩ := DoubleCommutantProof.bicommutant_finite_strong_approximation A T hT s ε hε
  exact ⟨a, a.property, ha⟩

/-- The von Neumann double commutant theorem for an arbitrary real Hilbert
space and an arbitrary unital star subalgebra of bounded operators. -/
theorem real_double_commutant : DoubleCommutantSpec.RealDoubleCommutant := by
  intro H _ _ _ A
  have hWC : @closure _ (weakTopology ℝ H H) (A : Set (H →L[ℝ] H)) ⊆
      Set.centralizer (Set.centralizer (A : Set (H →L[ℝ] H))) := by
    let : TopologicalSpace (H →L[ℝ] H) := weakTopology ℝ H H
    exact closure_minimal (fun T hT B hB => (hB T hT).symm)
      (weak_closed_centralizer _)
  have hSW : @closure _ (strongTopology ℝ H H) (A : Set (H →L[ℝ] H)) ⊆
      @closure _ (weakTopology ℝ H H) (A : Set (H →L[ℝ] H)) := by
    exact closure.mono (topology_comparison ℝ H H).2
  have hCS := bicommutant_subset_strong_closure A
  exact ⟨Set.Subset.antisymm hSW (hWC.trans hCS),
    Set.Subset.antisymm hWC (hCS.trans hSW)⟩

end ExpandedFA.OperatorTopology

