import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.NeumannResolvent
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Ring.Invertible

/-! Neumann inversion and the analytic resolvent, with the manuscript's sign convention. -/

namespace ExpandedFA.BanachAlgebra

open Specs.ExpandedFA.BanachAlgebra.NeumannResolvent

universe u

theorem algebra_neumann_series : NeumannSeries.{u} := by
  intro A _ _ hA b hb
  let : CompleteSpace A := hA.1
  exact ⟨(summable_geometric_of_norm_lt_one hb).hasSum,
    mul_neg_geom_series b hb, geom_series_mul_neg b hb⟩

theorem algebra_neumann_invertible : NeumannInvertible.{u} := by
  intro A _ _ hA b hb
  let : CompleteSpace A := hA.1
  exact isUnit_one_sub_of_norm_lt_one hb

theorem algebra_invertibles_open : InvertiblesOpen.{u} := by
  intro A _ _ hA
  let : CompleteSpace A := hA.1
  exact Units.isOpen

theorem algebra_resolventSet_open : ResolventSetOpen.{u} := by
  intro A _ _ hA a
  let : CompleteSpace A := hA.1
  exact spectrum.isOpen_resolventSet a

theorem algebra_resolvent_identity : ResolventIdentity.{u} := by
  intro A _ _ _ a lam mu hlam hmu
  change Ring.inverse (algebraMap ℂ A lam - a) - Ring.inverse (algebraMap ℂ A mu - a) =
    (mu - lam) • (Ring.inverse (algebraMap ℂ A lam - a) *
      Ring.inverse (algebraMap ℂ A mu - a))
  rw [Ring.inverse_sub_inverse (iff_of_true hlam hmu)]
  simp only [sub_sub_sub_cancel_right, Algebra.algebraMap_eq_smul_one, ← sub_smul,
    mul_smul_comm, mul_one, smul_mul_assoc]

theorem algebra_resolvent_analytic : ResolventAnalytic.{u} := by
  intro A _ _ hA a z hz
  let : CompleteSpace A := hA.1
  have hg : AnalyticAt ℂ (fun w : ℂ => w • (1 : A) - a) z :=
    (analyticAt_id.smul analyticAt_const).sub analyticAt_const
  have hi : AnalyticAt ℂ Ring.inverse (z • (1 : A) - a) := by
    apply analyticOnNhd_inverse
    simpa only [Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraResolventSetValue,
      Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one] using hz
  change AnalyticAt ℂ (fun w : ℂ => Ring.inverse (algebraMap ℂ A w - a)) z
  simpa only [Algebra.algebraMap_eq_smul_one, Function.comp_def] using
    hi.comp (f := fun w : ℂ => w • (1 : A) - a) hg

theorem algebra_resolvent_exterior_series : ExteriorSeries.{u} := by
  intro A _ _ hA a lam hlam
  let : CompleteSpace A := hA.1
  let : NormOneClass A := hA.2.2
  have hlampos : 0 < ‖lam‖ := (norm_nonneg a).trans_lt hlam
  have hlamne : lam ≠ 0 := norm_pos_iff.mp hlampos
  have hsmall : ‖lam⁻¹ • a‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ hlampos, mul_one]
    exact hlam
  refine ⟨spectrum.mem_resolventSet_of_norm_lt hlam, ?_⟩
  change HasSum (fun n : ℕ => (lam ^ (n + 1))⁻¹ • a ^ n) (resolvent a lam)
  have hs := (hasSum_geom_series_inverse (lam⁻¹ • a) hsmall).const_smul lam⁻¹
  have hres : lam⁻¹ • Ring.inverse (1 - lam⁻¹ • a) = resolvent a lam := by
    have h := spectrum.units_smul_resolvent_self (r := Units.mk0 lam hlamne) (a := a)
    have h' := congrArg (fun x : A => lam⁻¹ • x) h
    simpa only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val, resolvent,
      map_one, inv_smul_smul₀ hlamne] using h'.symm
  rw [hres] at hs
  simpa only [smul_pow, smul_smul, pow_succ, mul_inv_rev, inv_pow] using hs

end ExpandedFA.BanachAlgebra
