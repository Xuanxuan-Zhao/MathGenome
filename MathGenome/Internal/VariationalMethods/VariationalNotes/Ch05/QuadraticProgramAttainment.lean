import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.QuadraticProgramAttainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set Matrix
open scoped MatrixOrder
namespace VariationalNotes.Ch05

section LiftedProblem
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Objective on the linear image used to discard the flat directions of Q. -/
def liftedObjective (z : E × ℝ) : ℝ := ‖z.1‖ ^ 2 / 2 + z.2

omit [NormedSpace ℝ E] in
lemma continuous_liftedObjective : Continuous (liftedObjective (E := E)) := by
  unfold liftedObjective
  fun_prop

/-- An affine row splits into its horizontal part and vertical coefficient. -/
lemma affine_row_split (a : (E × ℝ) →ᵃ[ℝ] ℝ) (u : E) (t : ℝ) :
    a (u,t) = a (u,0) + a.linear (0,1) * t := by
  have heq : (u,t) = t • ((0 : E),(1 : ℝ)) +ᵥ (u,(0 : ℝ)) := by simp
  rw [heq, a.map_vadd, a.linear.map_smul]
  simp [smul_eq_mul, add_comm, mul_comm]

/-- Boundedness below excludes a downward vertical ray; one of the finitely
many defining rows must consequently impose a lower bound on height. -/
lemma exists_negative_vertical_row (s : Finset ((E × ℝ) →ᵃ[ℝ] ℝ))
    (hne : {z | ∀ a ∈ s, a z ≤ 0}.Nonempty)
    (hb : BddBelow (liftedObjective '' {z | ∀ a ∈ s, a z ≤ 0})) :
    ∃ a ∈ s, a.linear (0,1) < 0 := by
  classical
  by_contra! h
  obtain ⟨z, hz⟩ := hne
  obtain ⟨b, hb⟩ := hb
  let t := min z.2 (b - ‖z.1‖ ^ 2 / 2 - 1)
  have ht : (z.1,t) ∈ {z | ∀ a ∈ s, a z ≤ 0} := by
    intro a ha
    have hmul := mul_le_mul_of_nonneg_left (min_le_left z.2
      (b - ‖z.1‖ ^ 2 / 2 - 1)) (h a ha)
    have haz := hz a ha
    rw [← Prod.eta z, affine_row_split] at haz
    rw [affine_row_split]
    dsimp [t] at *
    linarith
  have hlow := hb (mem_image_of_mem liftedObjective ht)
  have ht' := min_le_right z.2 (b - ‖z.1‖ ^ 2 / 2 - 1)
  change b ≤ ‖z.1‖ ^ 2 / 2 + t at hlow
  dsimp [t] at hlow
  linarith

variable [FiniteDimensional ℝ E]

/-- Every real affine functional has a linear growth bound. -/
lemma affine_abs_growth (a : E →ᵃ[ℝ] ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |a u| ≤ C * (‖u‖ + 1) := by
  let L := a.linear.toContinuousLinearMap
  refine ⟨‖L‖ + |a 0|, by positivity, fun u => ?_⟩
  have hL : |a.linear u| ≤ ‖L‖ * ‖u‖ := L.le_opNorm u
  have ha : a u = a.linear u + a 0 := congrFun a.decomp u
  rw [ha]
  calc
    |a.linear u + a 0| ≤ |a.linear u| + |a 0| := abs_add_le _ _
    _ ≤ ‖L‖ * ‖u‖ + |a 0| := by linarith
    _ ≤ (‖L‖ + |a 0|) * (‖u‖ + 1) := by
      nlinarith [norm_nonneg L, norm_nonneg u, abs_nonneg (a 0)]

/-- The lower affine bound on height supplied by a negative vertical row. -/
lemma vertical_lower_bound (s : Finset ((E × ℝ) →ᵃ[ℝ] ℝ))
    (ha : ∃ a ∈ s, a.linear (0,1) < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E × ℝ,
      (∀ a ∈ s, a z ≤ 0) → -C * (‖z.1‖ + 1) ≤ z.2 := by
  obtain ⟨a, ha, hneg⟩ := ha
  let b := -a.linear (0,1)
  have hb : 0 < b := neg_pos.mpr hneg
  let l : E →ᵃ[ℝ] ℝ := b⁻¹ • a.comp (LinearMap.inl ℝ E ℝ).toAffineMap
  obtain ⟨C, hC, hbound⟩ := affine_abs_growth l
  refine ⟨C, hC, fun z hz => ?_⟩
  have hl : l z.1 ≤ z.2 := by
    change b⁻¹ * a (z.1,0) ≤ z.2
    rw [← div_eq_inv_mul, div_le_iff₀ hb]
    have haz := hz a ha
    rw [← Prod.eta z, affine_row_split] at haz
    dsimp [b]
    linarith
  have habs := (abs_le.mp (hbound z.1)).1
  linarith

/-- A scalar estimate used to bound every finite sublevel. -/
lemma quadratic_sublevel_norm_bound (C M r t : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (ht : -C * (r + 1) ≤ t) (hf : r ^ 2 / 2 + t ≤ M) :
    r ≤ 2*C + 2*|M+C| + 2 := by
  by_contra! h
  have hdiff : 0 ≤ r - 2*C - 2 := by
    have := abs_nonneg (M+C)
    linarith
  have hprod := mul_nonneg hr hdiff
  have hmc := le_abs_self (M+C)
  nlinarith [abs_nonneg (M+C)]

/-- The transformed polyhedron has compact finite sublevels. Flat directions
of the original feasible polyhedron have already been removed by its image. -/
lemma lifted_sublevel_isCompact (S : Set (E × ℝ))
    (hS : ConvexGeometry.IsPolyhedron S) (hne : S.Nonempty)
    (hb : BddBelow (liftedObjective '' S)) (M : ℝ) :
    IsCompact (S ∩ {z | liftedObjective z ≤ M}) := by
  obtain ⟨s, hs⟩ := hS
  have hrows : ∀ z, z ∈ S ↔ ∀ a ∈ s, a z ≤ 0 := by
    intro z
    rw [hs]
    rfl
  obtain ⟨C, hC, hlower⟩ := vertical_lower_bound s
    (exists_negative_vertical_row s (by simpa [← hs] using hne)
      (by simpa [← hs] using hb))
  let R := 2*C + 2*|M+C| + 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact (ConvexGeometry.polyhedron_isClosed S ⟨s, hs⟩).inter
      (isClosed_le continuous_liftedObjective continuous_const)
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max R (max (C*(R+1)) |M|), ?_⟩
    intro z hz
    obtain ⟨hzS, hzf⟩ := hz
    have ht := hlower z ((hrows z).mp hzS)
    change ‖z.1‖ ^ 2 / 2 + z.2 ≤ M at hzf
    have hu : ‖z.1‖ ≤ R :=
      quadratic_sublevel_norm_bound C M ‖z.1‖ z.2 hC (norm_nonneg _) ht hzf
    have htlo : -(C*(R+1)) ≤ z.2 := by nlinarith
    have hthi : z.2 ≤ |M| := by nlinarith [sq_nonneg ‖z.1‖, le_abs_self M]
    have htnorm : ‖z.2‖ ≤ max (C*(R+1)) |M| := by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · exact (neg_le_neg (le_max_left _ _)).trans htlo
      · exact hthi.trans (le_max_right _ _)
    rw [Prod.norm_def]
    exact max_le (hu.trans (le_max_left _ _)) (htnorm.trans (le_max_right _ _))

lemma liftedObjective_attains_minimum (S : Set (E × ℝ))
    (hS : ConvexGeometry.IsPolyhedron S) (hne : S.Nonempty)
    (hb : BddBelow (liftedObjective '' S)) :
    ∃ z ∈ S, ∀ w ∈ S, liftedObjective z ≤ liftedObjective w := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨z, hz, hmin⟩ := (lifted_sublevel_isCompact S hS ⟨z₀, hz₀⟩ hb
    (liftedObjective z₀)).exists_isMinOn (f := liftedObjective) ⟨z₀, hz₀, le_refl (liftedObjective z₀)⟩
      continuous_liftedObjective.continuousOn
  refine ⟨z, hz.1, fun w hw => ?_⟩
  by_cases hle : liftedObjective w ≤ liftedObjective z₀
  · exact hmin ⟨hw, hle⟩
  · exact hz.2.trans (le_of_not_ge hle)

end LiftedProblem

/-- A PSD real matrix is the Gram matrix of its positive square root.
The statement is valid in dimension zero as well. -/
lemma quadratic_eq_norm_square {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosSemidef) (x : Fin n → ℝ) :
    x ⬝ᵥ (Q *ᵥ x) = ‖(WithLp.toLp 2 (CFC.sqrt Q *ᵥ x) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  let R := CFC.sqrt Q
  have hR : Rᵀ = R := by
    have hh := (CFC.sqrt_nonneg Q).posSemidef.isHermitian.eq
    simpa only [conjTranspose_eq_transpose_of_trivial] using hh
  have hRR : R * R = Q := CFC.sqrt_mul_sqrt_self Q hQ.nonneg
  calc
    x ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (Rᵀ *ᵥ (R *ᵥ x)) := by
      rw [hR, mulVec_mulVec, hRR]
    _ = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := dotProduct_transpose_mulVec R x (R *ᵥ x)
    _ = ‖(WithLp.toLp 2 (R *ᵥ x) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      rfl

/-- Finite infima of convex quadratic objectives on nonempty polyhedra
are attained. The proof uses compactness only after taking a linear image. -/
theorem quadraticProgram_attains_infimum : Specs.quadraticProgram_attains_infimum := by
  intro n Q c P p hQ hP hne hp
  let R := CFC.sqrt Q
  let U : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp R.mulVecLin
  let t : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ c
  let A := U.prod t
  let S := A '' P
  have hS : ConvexGeometry.IsPolyhedron S :=
    ConvexGeometry.polyhedron_affine_image A.toAffineMap P hP
  have hSne : S.Nonempty := hne.image A
  have hobj (x : Fin n → ℝ) : liftedObjective (A x) = Specs.quadraticObjective Q c x := by
    change ‖(WithLp.toLp 2 (R *ᵥ x) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2 +
      c ⬝ᵥ x = (x ⬝ᵥ (Q *ᵥ x)) / 2 + c ⬝ᵥ x
    rw [quadratic_eq_norm_square Q hQ x]
  have hb : BddBelow (liftedObjective '' S) := by
    refine ⟨p, ?_⟩
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rw [hobj]
    exact hp.1 (mem_image_of_mem _ hx)
  obtain ⟨z, hz, hmin⟩ := liftedObjective_attains_minimum S hS hSne hb
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨x, hx, le_antisymm ?_ (hp.1 (mem_image_of_mem _ hx))⟩
  apply hp.2
  rintro y ⟨w, hw, rfl⟩
  simpa only [hobj] using hmin (A w) (mem_image_of_mem A hw)

end VariationalNotes.Ch05
