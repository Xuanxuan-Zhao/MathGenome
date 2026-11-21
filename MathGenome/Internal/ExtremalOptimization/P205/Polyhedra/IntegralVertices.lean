import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.IntegralVertices
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.TotalUnimodularity
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.VertexOptimum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

noncomputable section
open Matrix Set Module
namespace P205.Polyhedra

/-- Select a basis from the active covectors, retaining the original row indices. -/
lemma exists_nonsingular_active_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Coordinate n)
    (hx : IsVertex A b x) :
    ∃ f : Fin n → Fin m, (∀ i, f i ∈ activeRows A b x) ∧
      (A.submatrix f id).det ≠ 0 := by
  classical
  have hs : ⊤ ≤ Submodule.span ℝ (rowCovector A '' activeRows A b x) :=
    ((vertex_iff_activeSpan A b x hx.1).mp hx).ge
  let B := Basis.ofSpan hs
  let e := B.indexEquiv (Pi.basisFun ℝ (Fin n)).dualBasis
  let C := B.reindex e
  have hC : ∀ j : Fin n, ∃ i ∈ activeRows A b x, rowCovector A i = C j := by
    intro j
    exact Basis.ofSpan_subset hs ⟨e.symm j, by simp [C, B]⟩
  choose f hf hfc using hC
  refine ⟨f, hf, ?_⟩
  intro hdet
  obtain ⟨d, hd, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hd
  apply (Module.forall_dual_apply_eq_zero_iff ℝ d).mp
  intro φ
  have hrows : ∀ i, C i d = 0 := by
    intro i
    rw [← hfc i]
    exact congrFun hzero i
  have heval : ∀ ψ ∈ Submodule.span ℝ (Set.range C), ψ d = 0 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ => obtain ⟨i, rfl⟩ := hψ; exact hrows i
    | zero => simp
    | add ψ χ _ _ hψ hχ => simp [hψ, hχ]
    | smul a ψ _ hψ => simp [hψ]
  apply heval
  rw [C.span_eq]
  trivial

/-- Cramer's numerator is integral, and division by a determinant of ±1
preserves integrality. The empty square system is covered as well. -/
theorem square_system_integral : IntegralVerticesSpecs.square_system_integral := by
  intro n B b x hdet heq
  have hcr : (B.map (Int.cast : ℤ → ℝ)).det • x =
      (B.map (Int.cast : ℤ → ℝ)).cramer (fun i => (b i : ℝ)) := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← heq, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro j
  have hj := congrFun hcr j
  have hnum : ((B.cramer b j : ℤ) : ℝ) =
      (B.map (Int.cast : ℤ → ℝ)).cramer (fun i => (b i : ℝ)) j := by
    rw [Matrix.cramer_apply, Matrix.cramer_apply, Int.cast_det, Matrix.map_updateCol]
    rfl
  rw [← Int.cast_det, ← hnum] at hj
  rcases hdet with hdet | hdet
  · refine ⟨B.cramer b j, ?_⟩
    simpa [hdet] using hj
  · refine ⟨-(B.cramer b j), ?_⟩
    simp only [hdet, Int.cast_neg, Int.cast_one, Pi.smul_apply, smul_eq_mul,
      neg_one_mul] at hj
    simpa using (neg_eq_iff_eq_neg.mp hj)

theorem vertex_integral : IntegralVerticesSpecs.vertex_integral := by
  intro m n A b x hA hx
  obtain ⟨f, hf, hdet⟩ := exists_nonsingular_active_rows
    (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) x hx
  let B := A.submatrix f id
  have hB : B.det = 1 ∨ B.det = -1 := by
    have hminor := (TotalUnimodularity.all_minors_iff A).mp hA n f id
    rcases hminor with hzero | hone | hneg
    · exfalso
      apply hdet
      change (B.map (Int.cast : ℤ → ℝ)).det = 0
      rw [← Int.cast_det, hzero, Int.cast_zero]
    · exact Or.inl hone
    · exact Or.inr hneg
  apply square_system_integral B (fun i => b (f i)) x hB
  ext i
  exact hf i

theorem finite_infimum_integral_vertex :
    IntegralVerticesSpecs.finite_infimum_integral_vertex := by
  intro m n A b c p hA hne hpoint hp
  obtain ⟨x, hx, hxp, hopt⟩ := finite_infimum_vertex
    (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) c p hne hpoint hp
  exact ⟨x, hx, vertex_integral A b x hA hx, hxp, hopt⟩

theorem finite_supremum_integral_vertex :
    IntegralVerticesSpecs.finite_supremum_integral_vertex := by
  intro m n A b c p hA hne hpoint hp
  obtain ⟨x, hx, hxp, hopt⟩ := finite_supremum_vertex
    (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) c p hne hpoint hp
  exact ⟨x, hx, vertex_integral A b x hA hx, hxp, hopt⟩

/-- A bounded set in the coordinate space contains no affine line. -/
lemma pointed_of_isBounded {n : ℕ} {P : Set (Coordinate n)}
    (hb : Bornology.IsBounded P) : IsPointed P := by
  rintro ⟨x, d, hd, hline⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let t : ℝ := (|C| + 1) / ‖d‖
  have ht : 0 < t := div_pos (by positivity) hdpos
  have hbound := hC (hline t) (show x ∈ P by simpa using hline 0)
  have hdist : dist (x + t • d) x = |C| + 1 := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact div_mul_cancel₀ _ hdpos.ne'
  rw [hdist] at hbound
  linarith [le_abs_self C]

/-- Closed halfspaces are closed, including an empty intersection. -/
lemma isClosed_polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : IsClosed (polyhedron A b) := by
  have heq : polyhedron A b = ⋂ i, {x | rowCovector A i x ≤ b i} := by
    ext x
    simp only [polyhedron, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro i
  exact isClosed_le (rowCovector A i).continuous_of_finiteDimensional continuous_const

/-- The extreme value theorem supplies an optimizer without any finiteness
assumption on the value; boundedness supplies pointedness for vertex selection. -/
theorem bounded_integral_minimizer : IntegralVerticesSpecs.bounded_integral_minimizer := by
  intro m n A b c hA hne hb
  let Ar := A.map (Int.cast : ℤ → ℝ)
  let br := fun i => (b i : ℝ)
  have hcompact : IsCompact (polyhedron Ar br) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_polyhedron Ar br) hb
  have hcont : Continuous (fun x : Coordinate n => c ⬝ᵥ x) := by
    unfold dotProduct
    fun_prop
  obtain ⟨x₀, hx₀, hopt₀⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  obtain ⟨x, hx, _, hopt⟩ := vertex_optimizer_of_optimizer Ar br c
    (pointed_of_isBounded hb) x₀ hx₀ hopt₀
  exact ⟨x, hx, vertex_integral A b x hA hx, hopt⟩

theorem bounded_integral_maximizer : IntegralVerticesSpecs.bounded_integral_maximizer := by
  intro m n A b c hA hne hb
  obtain ⟨x, hx, hint, hopt⟩ := bounded_integral_minimizer A b (-c) hA hne hb
  refine ⟨x, hx, hint, ?_⟩
  intro y hy
  simpa only [neg_dotProduct, neg_le_neg_iff] using hopt y hy

end P205.Polyhedra
