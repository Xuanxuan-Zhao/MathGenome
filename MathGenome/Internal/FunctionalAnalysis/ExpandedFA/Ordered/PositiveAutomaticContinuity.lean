import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Ordered.PositiveDecompositions
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Batteries.Tactic.OpenPrivate

open Set Filter Topology Module

universe u

namespace ExpandedFA.Ordered.PositiveAutomaticContinuity

open Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity (differenceSubspace)

open private tsum_mem_cone from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Ordered.PositiveDecompositions

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An infinite-dimensional normed space has independent unit vectors. -/
theorem exists_independent_unit_sequence (hX : ¬ FiniteDimensional ℝ X) :
    ∃ v : ℕ → X, LinearIndependent ℝ v ∧ ∀ n, ‖v n‖ = 1 := by
  classical
  let b := Basis.ofVectorSpace ℝ X
  let : Infinite (Basis.ofVectorSpaceIndex ℝ X) :=
    not_finite_iff_infinite.mp (fun h => hX (by
      let := h
      exact b.finiteDimensional_of_finite))
  let i := Infinite.natEmbedding (Basis.ofVectorSpaceIndex ℝ X)
  let v : ℕ → X := fun n => b (i n)
  have hv : LinearIndependent ℝ v := b.linearIndependent.comp i i.injective
  let w : ℕ → ℝˣ := fun n => (Units.mk0 ‖v n‖ (norm_ne_zero_iff.mpr (hv.ne_zero n)))⁻¹
  refine ⟨w • v, hv.units_smul w, fun n => ?_⟩
  change ‖(w n : ℝ) • v n‖ = 1
  simpa [w] using norm_smul_inv_norm (𝕜 := ℝ) (hv.ne_zero n)

/-- If every algebraic scalar functional is continuous, the normed space is
finite dimensional. Values growing on independent unit vectors prove this. -/
theorem finiteDimensional_of_all_functionals_continuous
    (h : ∀ f : X →ₗ[ℝ] ℝ, Continuous f) : FiniteDimensional ℝ X := by
  classical
  by_contra hX
  obtain ⟨v, hv, hunit⟩ := exists_independent_unit_sequence hX
  let b := Basis.span hv
  let g := b.constr ℝ (fun n => (n : ℝ))
  obtain ⟨f, hf⟩ := g.exists_extend
  have hval (n : ℕ) : f (v n) = n := by
    have heq := congrArg (fun T => T (b n)) hf
    simpa [g, b] using heq.trans (b.constr_basis ℝ (fun n => (n : ℝ)) n)
  obtain ⟨C, _, hC⟩ := SemilinearMapClass.bound_of_continuous f (h f)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hb := hC (v n)
  rw [hval, hunit, mul_one, Real.norm_natCast] at hb
  exact (not_le_of_gt hn) hb

/-- Positivity of all algebraic annihilators forces `P-P` closed and of finite
algebraic codimension. -/
theorem automatic_continuity_forces_closed_finite_codimension
    (P : ConvexCone ℝ X) (hne : (P : Set X).Nonempty)
    (h : ∀ f : X →ₗ[ℝ] ℝ, (∀ x ∈ P, 0 ≤ f x) → Continuous f) :
    IsClosed (differenceSubspace P hne : Set X) ∧
      FiniteDimensional ℝ (X ⧸ differenceSubspace P hne) := by
  let F := differenceSubspace P hne
  have hPF {x : X} (hx : x ∈ P) : x ∈ F :=
    ⟨x + x, P.add_mem hx hx, x, hx, by simp⟩
  have hann (f : F.dualAnnihilator) : Continuous (f : X →ₗ[ℝ] ℝ) := by
    apply h f
    intro x hx
    have hf : (f : X →ₗ[ℝ] ℝ) x = 0 :=
      (Submodule.mem_dualAnnihilator _).mp f.property x (hPF hx)
    rw [hf]
  have hF : IsClosed (F : Set X) := by
    have heq : (F : Set X) = ⋂ f : F.dualAnnihilator,
        {x : X | (f : X →ₗ[ℝ] ℝ) x = 0} := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq]
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff F x).symm.trans
        (by simp)
    rw [heq]
    exact isClosed_iInter (fun f => isClosed_singleton.preimage (hann f))
  let : IsClosed (F : Set X) := hF
  refine ⟨hF, finiteDimensional_of_all_functionals_continuous (fun f => ?_)⟩
  apply F.isQuotientMap_mkQ.continuous_iff.mpr
  apply h (f.comp F.mkQ)
  intro x hx
  have hxq : F.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero F).mpr (hPF hx)
  simp [hxq]

/-- A positive algebraic functional is bounded on the positive unit ball.
The proof only uses positivity on a series sum minus one term; it does not
exchange an algebraic functional with an infinite sum. -/
theorem exists_positive_unit_bound [CompleteSpace X]
    (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X)) (hzero : (0 : X) ∈ P)
    (f : X →ₗ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 ≤ f x) :
    ∃ B : ℝ, ∀ x ∈ P, ‖x‖ ≤ 1 → f x ≤ B := by
  classical
  by_contra hbound
  push Not at hbound
  choose a ha hnorm hfa using fun n : ℕ => hbound ((n : ℝ) / (1 / 2 : ℝ) ^ n)
  let u : ℕ → X := fun n => (1 / 2 : ℝ) ^ n • a n
  have humem (n : ℕ) : u n ∈ P := P.smul_mem (by positivity) (ha n)
  have hunorm (n : ℕ) : ‖u n‖ ≤ (1 / 2 : ℝ) ^ n := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / 2 : ℝ) ^ n)]
    exact (mul_le_mul_of_nonneg_left (hnorm n) (by positivity)).trans_eq (mul_one _)
  have hs : Summable u :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hunorm summable_geometric_two).of_norm
  have hlarge (n : ℕ) : (n : ℝ) < f (u n) := by
    dsimp [u]
    rw [map_smul, smul_eq_mul]
    simpa [mul_comm] using
      (div_lt_iff₀ (by positivity : 0 < (1 / 2 : ℝ) ^ n)).mp (hfa n)
  have hdom (n : ℕ) : f (u n) ≤ f (∑' i, u i) := by
    let v : ℕ → X := fun i => if i = n then 0 else u i
    have hvnorm (i : ℕ) : ‖v i‖ ≤ (1 / 2 : ℝ) ^ i := by
      dsimp [v]
      split_ifs
      · simp
      · exact hunorm i
    have hvs : Summable v :=
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hvnorm summable_geometric_two).of_norm
    have hvmem (i : ℕ) : v i ∈ P := by
      dsimp [v]
      split_ifs
      · exact hzero
      · exact humem i
    have hvP := tsum_mem_cone P hP hzero hvs hvmem
    have heq : (∑' i, u i) - u n = ∑' i, v i := by
      rw [hs.tsum_eq_add_tsum_ite n]
      dsimp [v]
      abel
    have hh := hf _ (heq ▸ hvP)
    rw [map_sub] at hh
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (f (∑' i, u i))
  exact (not_lt_of_ge (hdom n)) ((hlarge n).trans' hn)

/-- Automatic continuity for a closed generating cone in a Banach space. -/
theorem continuous_of_positive_of_generating [CompleteSpace X]
    (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (hgen : ∀ x : X, ∃ y ∈ P, ∃ z ∈ P, x = y - z)
    (f : X →ₗ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 ≤ f x) : Continuous f := by
  have hzero : (0 : X) ∈ P := by
    obtain ⟨y, hy, _⟩ := hgen 0
    exact ConvexCone.Pointed.of_nonempty_of_isClosed ⟨y, hy⟩ hP
  obtain ⟨B, hB⟩ := exists_positive_unit_bound P hP hzero f hf
  have hBpos : 0 ≤ B := by simpa using hB 0 hzero (by simp)
  have hbound (y : X) (hy : y ∈ P) : f y ≤ B * ‖y‖ := by
    by_cases hy0 : y = 0
    · simp [hy0]
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hm : ‖y‖⁻¹ • y ∈ P := P.smul_mem (inv_pos.mpr hny) hy
    have hn : ‖‖y‖⁻¹ • y‖ ≤ 1 := (norm_smul_inv_norm (𝕜 := ℝ) hy0).le
    have hh := hB _ hm hn
    rw [map_smul, smul_eq_mul] at hh
    calc
      f y = (‖y‖⁻¹ * f y) * ‖y‖ := by field_simp
      _ ≤ B * ‖y‖ := mul_le_mul_of_nonneg_right hh hny.le
  obtain ⟨C, hC, hdecomp⟩ :=
    PositiveDecompositions.exists_bounded_positive_decompositions P hP hgen
  apply (f.mkContinuous (2 * B * C) (fun x => ?_)).continuous
  obtain ⟨y, hy, z, hz, hx, hny, hnz⟩ := hdecomp x
  calc
    ‖f x‖ = ‖f y - f z‖ := by rw [hx, map_sub]
    _ ≤ ‖f y‖ + ‖f z‖ := norm_sub_le _ _
    _ = f y + f z := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf y hy), abs_of_nonneg (hf z hz)]
    _ ≤ B * ‖y‖ + B * ‖z‖ := add_le_add (hbound y hy) (hbound z hz)
    _ ≤ B * (C * ‖x‖) + B * (C * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hny hBpos) (mul_le_mul_of_nonneg_left hnz hBpos)
    _ = 2 * B * C * ‖x‖ := by ring

/-- Restrict to the Banach space `P-P`, extend its continuous restriction by
Hahn–Banach, and factor the remaining algebraic functional through the finite
dimensional quotient. -/
theorem positive_continuous_of_closed_finite_codimension
    [CompleteSpace X] (P : ConvexCone ℝ X) (hne : (P : Set X).Nonempty)
    (hP : IsClosed (P : Set X))
    (hF : IsClosed (differenceSubspace P hne : Set X))
    (hcodim : FiniteDimensional ℝ (X ⧸ differenceSubspace P hne))
    (f : X →ₗ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 ≤ f x) : Continuous f := by
  let F := differenceSubspace P hne
  let : IsClosed (F : Set X) := hF
  let : FiniteDimensional ℝ (X ⧸ F) := hcodim
  have hPF {x : X} (hx : x ∈ P) : x ∈ F :=
    ⟨x + x, P.add_mem hx hx, x, hx, by simp⟩
  let Q : ConvexCone ℝ F := P.comap F.subtype
  have hQ : IsClosed (Q : Set F) := hP.preimage continuous_subtype_val
  have hgen : ∀ x : F, ∃ y ∈ Q, ∃ z ∈ Q, x = y - z := by
    intro x
    obtain ⟨y, hy, z, hz, hx⟩ := x.property
    refine ⟨⟨y, hPF hy⟩, hy, ⟨z, hPF hz⟩, hz, ?_⟩
    exact Subtype.ext hx
  let fr : F →ₗ[ℝ] ℝ := f.comp F.subtype
  have hfr : Continuous fr :=
    continuous_of_positive_of_generating Q hQ hgen fr (fun x hx => hf x hx)
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq F (⟨fr, hfr⟩ : F →L[ℝ] ℝ)
  let d : X →ₗ[ℝ] ℝ := f - g.toLinearMap
  have hd : F ≤ d.ker := by
    intro x hx
    change f x - g x = 0
    exact sub_eq_zero.mpr (hg ⟨x, hx⟩).symm
  let q : (X ⧸ F) →ₗ[ℝ] ℝ := F.liftQ d hd
  have hdcont : Continuous d := by
    change Continuous (fun x => q (F.mkQ x))
    exact q.continuous_of_finiteDimensional.comp F.continuous_mkQ
  have hc := hdcont.add g.continuous
  convert hc using 1
  ext x
  exact (sub_add_cancel (f x) (g x)).symm

/-- The quantitative conclusion is supplied by the accepted generating-cone
theorem, with the same individual bounds on both positive summands. -/
theorem exists_bounded_positive_decompositions
    [CompleteSpace X] (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (hgen : ∀ x : X, ∃ y ∈ P, ∃ z ∈ P, x = y - z) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : X, ∃ y ∈ P, ∃ z ∈ P,
      x = y - z ∧ ‖y‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖ :=
  PositiveDecompositions.exists_bounded_positive_decompositions P hP hgen

end ExpandedFA.Ordered.PositiveAutomaticContinuity
