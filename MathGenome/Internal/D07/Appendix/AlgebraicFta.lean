import MathGenome.Internal.Specs.D07.Appendix.AlgebraicFta
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The fundamental theorem of algebra and its equivalent formulations.

The task permits exact reuse of the proved library FTA. `Complex.exists_root`
is Mathlib's proof via Liouville's theorem, not an assumed algebraic-closedness
certificate. We use it for root existence and derive closedness and complete
factorization. No complex-closedness or transcendence premise is added.
The separately assigned real-odd-extension, quadratic-extension, and Sylow-2
support results retain their own modules.
-/

namespace D07.Appendix.AlgebraicFta

open Polynomial
open Specs.D07.Appendix.AlgebraicFta

theorem root_exists : RootExistence := by
  intro f hf
  exact Complex.exists_root hf

theorem nonconstant_root_exists : NonconstantRootExistence := by
  intro f hf
  apply root_exists f
  exact lt_of_not_ge (fun h => hf (f.coeff 0) (eq_C_of_degree_le_zero h))

/-- This equivalence uses only the general algebraic closedness API. -/
theorem root_iff_algebraic_closedness : RootIffAlgebraicClosedness := by
  constructor
  · intro h
    exact IsAlgClosed.of_exists_root ℂ (fun p _ hp => h p (degree_pos_of_irreducible hp))
  · intro h f hf
    haveI : IsAlgClosed ℂ := h
    exact IsAlgClosed.exists_root f (ne_of_gt hf)

theorem algebraically_closed : AlgebraicClosedness :=
  root_iff_algebraic_closedness.mp root_exists

/-- Factorization counts roots as a multiset rather than discarding repetitions. -/
theorem root_iff_linear_factorization : RootIffLinearFactorization := by
  constructor
  · intro h f n hn hdeg
    haveI : IsAlgClosed ℂ := root_iff_algebraic_closedness.mp h
    have hf : f ≠ 0 := by
      intro hzero
      have : n = 0 := by simpa [hzero] using hdeg.symm
      omega
    refine ⟨leadingCoeff_ne_zero.mpr hf, f.roots, ?_, ?_, ?_⟩
    · exact (IsAlgClosed.card_roots_eq_natDegree).trans hdeg
    · intro z hz
      exact (mem_roots hf).mp hz
    · exact (IsAlgClosed.splits f).eq_prod_roots
  · intro h f hf
    have hpos : 0 < f.natDegree := natDegree_pos_iff_degree_pos.mpr hf
    obtain ⟨_, s, hcard, hroots, _⟩ := h f f.natDegree hpos rfl
    have hs : s ≠ 0 := by
      intro hz
      have : f.natDegree = 0 := by simpa [hz] using hcard.symm
      exact (ne_of_gt hpos) this
    obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hs
    exact ⟨z, hroots z hz⟩

theorem linear_factorization : LinearFactorization :=
  root_iff_linear_factorization.mp root_exists

end D07.Appendix.AlgebraicFta
