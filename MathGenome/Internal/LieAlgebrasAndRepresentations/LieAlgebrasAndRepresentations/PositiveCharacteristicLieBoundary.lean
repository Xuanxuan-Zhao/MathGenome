import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PositiveCharacteristicLieBoundary

noncomputable section
universe u
namespace LieAlgebrasAndRepresentations.PositiveCharacteristicLieBoundary
open Polynomial
open Specs.LieAlgebrasAndRepresentations.PositiveCharacteristicLieBoundary
variable (k : Type u) [Field k] (p : ℕ) [CharP k p]
local instance endLieRing : LieRing (Module.End k (V k p)) := LieRing.ofAssociativeRing
local instance endBracket : Bracket (Module.End k (V k p)) (Module.End k (V k p)) :=
  ⟨fun f g => f * g - g * f⟩

theorem D_q (f : k[X]) : D k p (q k p f) = q k p (derivative f) := rfl

theorem T_q (f : k[X]) : T k p (q k p f) = q k p (X * f) := by
  change q k p X * q k p f = q k p (X * f)
  exact (map_mul _ _ _).symm

theorem commutator_DT : ⁅D k p, T k p⁆ = I k p := by
  apply LinearMap.ext
  intro v
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective v
  change D k p (T k p (q k p f)) - T k p (D k p (q k p f)) = q k p f
  rw [T_q, D_q, D_q, T_q, derivative_mul]
  simp only [derivative_X, one_mul, map_add]
  abel

theorem commutator_DI : ⁅D k p, I k p⁆ = 0 := by
  apply LinearMap.ext
  intro v
  change D k p v - D k p v = 0
  exact sub_self _

theorem commutator_TI : ⁅T k p, I k p⁆ = 0 := by
  apply LinearMap.ext
  intro v
  change T k p v - T k p v = 0
  exact sub_self _

theorem no_common_eigenvector (v : V k p) (a b : k)
    (hD : D k p v = a • v) (hT : T k p v = b • v) : v = 0 := by
  have h := congrArg (fun f : Module.End k (V k p) => f v) (commutator_DT k p)
  change D k p (T k p v) - T k p (D k p v) = v at h
  rw [hT, hD, map_smul, map_smul, hD, hT] at h
  simpa [smul_smul, mul_comm] using h.symm

theorem quotient_dimension : Module.finrank k (V k p) = p := by
  change Module.finrank k (k[X] ⧸ Ideal.span {(X : k[X]) ^ p}) = p
  rw [finrank_quotient_span_eq_natDegree, natDegree_X_pow]

theorem quotient_finite : Module.Finite k (V k p) :=
  (monic_X_pow p : ((X : k[X]) ^ p).Monic).finite_quotient

theorem heisenberg_dimension : Module.finrank k (Heisenberg k) = 3 := by
  rw [(coordinatesLinear k).finrank_eq]
  simp [Module.finrank_prod, Module.finrank_self]

theorem heisenberg_brackets :
    ⁅eD k, eT k⁆ = eI k ∧ ⁅eD k, eI k⁆ = 0 ∧ ⁅eT k, eI k⁆ = 0 := by
  constructor
  · apply Heisenberg.ext
    · rfl
    · rfl
    · change (1 : k) * 1 - 0 * 0 = 1
      simp
  constructor
  · apply Heisenberg.ext
    · rfl
    · rfl
    · change (1 : k) * 0 - 0 * 0 = 0
      simp
  · apply Heisenberg.ext
    · rfl
    · rfl
    · change (0 : k) * 0 - 0 * 1 = 0
      simp

private def centralIdeal : LieIdeal k (Heisenberg k) where
  carrier := {x | x.d = 0 ∧ x.t = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    intro x y hx hy
    change x.d + y.d = 0 ∧ x.t + y.t = 0
    simp_all
  smul_mem' := by
    intro a x hx
    change a * x.d = 0 ∧ a * x.t = 0
    simp_all
  lie_mem := by intro x y hy; exact ⟨rfl, rfl⟩

theorem heisenberg_nilpotent : LieRing.IsNilpotent (Heisenberg k) := by
  change LieModule.IsNilpotent (Heisenberg k) (Heisenberg k)
  apply (LieModule.isNilpotent_iff k _ _).mpr
  refine ⟨2, le_bot_iff.mp ?_⟩
  have h : ⁅(⊤ : LieIdeal k (Heisenberg k)), ⊤⁆ ≤ centralIdeal k := by
    rw [LieSubmodule.lie_le_iff]
    intro x hx y hy
    exact ⟨rfl, rfl⟩
  have hc : ⁅(⊤ : LieIdeal k (Heisenberg k)), centralIdeal k⁆ = ⊥ := by
    rw [LieSubmodule.lie_eq_bot_iff]
    intro x hx y hy
    change y.d = 0 ∧ y.t = 0 at hy
    apply Heisenberg.ext
    · rfl
    · rfl
    · change x.d * y.t - y.d * x.t = 0
      simp [hy.1, hy.2]
  simp only [show 2 = 1 + 1 from rfl, LieModule.lowerCentralSeries_succ,
    LieModule.lowerCentralSeries_zero]
  exact (LieSubmodule.mono_lie_right ⊤ h).trans hc.le

theorem heisenberg_solvable : LieAlgebra.IsSolvable (Heisenberg k) := by
  letI := heisenberg_nilpotent k
  infer_instance

theorem representation : ∃ ρ : Heisenberg k →ₗ⁅k⁆ Module.End k (V k p),
    ρ.toLinearMap = action k p := by
  refine ⟨{ __ := action k p, map_lie' := ?_ }, rfl⟩
  intro x y
  change (0 : k) • D k p + (0 : k) • T k p +
    (x.d * y.t - y.d * x.t) • I k p =
    ⁅x.d • D k p + x.t • T k p + x.i • I k p,
      y.d • D k p + y.t • T k p + y.i • I k p⁆
  have hTD : ⁅T k p, D k p⁆ = -I k p := by
    exact (lie_skew (T k p) (D k p)).symm.trans (congrArg Neg.neg (commutator_DT k p))
  have hID : ⁅I k p, D k p⁆ = 0 := by
    simpa [commutator_DI] using (lie_skew (I k p) (D k p)).symm
  have hIT : ⁅I k p, T k p⁆ = 0 := by
    simpa [commutator_TI] using (lie_skew (I k p) (T k p)).symm
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, commutator_DT,
    commutator_DI, commutator_TI, hTD, hID, hIT, smul_zero, zero_smul,
    zero_add, add_zero, smul_neg, smul_smul]
  module

/-- The relation also holds on the last surviving monomial. -/
theorem commutator_top_monomial :
    ⁅D k p, T k p⁆ (q k p (X ^ (p - 1))) = q k p (X ^ (p - 1)) := by
  rw [commutator_DT]
  rfl

theorem quotient_relation : q k p (X ^ p) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

theorem action_generators : action k p (eD k) = D k p ∧
    action k p (eT k) = T k p ∧ action k p (eI k) = I k p := by
  simp [action, eD, eT, eI]

/-- The identity does not satisfy the nilpotence hypothesis in Engel's theorem. -/
theorem identity_not_nilpotent (hp : 0 < p) : ¬ IsNilpotent (I k p) := by
  have hdim : 0 < Module.finrank k (V k p) := by rw [quotient_dimension]; exact hp
  letI : Nontrivial (V k p) := Module.nontrivial_of_finrank_pos hdim
  change ¬ IsNilpotent (1 : Module.End k (V k p))
  exact not_isNilpotent_one

/-- A finite, nonzero module for a nilpotent, solvable, three dimensional algebra,
with the stated operators and no nonzero simultaneous eigenvector. No splitting
hypothesis on k is needed, and p=2 is included. -/
theorem counterexample (hp : 0 < p) :
    Module.Finite k (V k p) ∧ Module.finrank k (V k p) = p ∧
    0 < Module.finrank k (V k p) ∧
    Module.finrank k (Heisenberg k) = 3 ∧
    LieRing.IsNilpotent (Heisenberg k) ∧ LieAlgebra.IsSolvable (Heisenberg k) ∧
    ∃ ρ : Heisenberg k →ₗ⁅k⁆ Module.End k (V k p),
      ρ (eD k) = D k p ∧ ρ (eT k) = T k p ∧ ρ (eI k) = I k p ∧
      ∀ v : V k p, (∀ x : Heisenberg k, ∃ a : k, ρ x v = a • v) → v = 0 := by
  refine ⟨quotient_finite k p, quotient_dimension k p, ?_, heisenberg_dimension k,
    heisenberg_nilpotent k, heisenberg_solvable k, ?_⟩
  · rw [quotient_dimension]; exact hp
  obtain ⟨ρ, hρ⟩ := representation k p
  have heq (x : Heisenberg k) : ρ x = action k p x := by
    exact congrArg (fun f : Heisenberg k →ₗ[k] Module.End k (V k p) => f x) hρ
  obtain ⟨hD, hT, hI⟩ := action_generators k p
  refine ⟨ρ, (heq _).trans hD, (heq _).trans hT, (heq _).trans hI, ?_⟩
  intro v hv
  obtain ⟨a, ha⟩ := hv (eD k)
  obtain ⟨b, hb⟩ := hv (eT k)
  rw [heq, hD] at ha
  rw [heq, hT] at hb
  exact no_common_eigenvector k p v a b ha hb

end LieAlgebrasAndRepresentations.PositiveCharacteristicLieBoundary
