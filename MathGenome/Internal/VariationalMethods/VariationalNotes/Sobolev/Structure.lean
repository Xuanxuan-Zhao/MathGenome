import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Structure
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.WeakLowerSemicontinuity
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import MathGenome.Internal.FourierSobolev.P102.Sobolev.PolyaSzego

noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set
open scoped ENNReal ContDiff

namespace VariationalNotes.Sobolev

theorem banach : StructureExpected.Banach := by
  intro d m Ω p
  infer_instance

theorem reflexive : StructureExpected.Reflexive := by
  intro d m Ω p hp
  open ExpandedFA.PartIV.VectorLpReflexive in
  have hLp : ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ
      (P102.U4.DomainLp ℝ Ω p.ennreal) :=
    lp_reflexive ℝ (endpoint_counterexamples ℝ).1 _ p.ennreal
      (by simpa only [Exponent.ennreal, ← ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff p.pos).mpr hp)
      (by simp [Exponent.ennreal])
  have ht := P102.Sobolev.Rearrangement.finite_pi_reflexive
    (fun _ : P102.U4.SobolevIndex d 1 => P102.U4.DomainLp ℝ Ω p.ennreal) (fun _ => hLp)
  have hs := ExpandedFA.PartIV.VectorLpReflexive.closed_subspace_reflexive
    (P102.U4.sobolevSubmodule ℝ Ω 1 p.ennreal)
    (P102.U4.sobolevSubmodule_isClosed Ω 1 p.ennreal)
    (ExpandedFA.PartIV.VectorLpReflexive.reflexive_of_equiv
      (PiLp.continuousLinearEquiv 1 ℝ _).symm ht)
  exact ExpandedFA.PartIV.VectorLpReflexive.reflexive_of_equiv
    (coordinateEquiv Ω p).symm
    (P102.Sobolev.Rearrangement.finite_pi_reflexive (fun _ : Fin m => P102.U4.Sobolev ℝ Ω 1 p.ennreal)
      (fun _ => hs))

theorem affine_closed : StructureExpected.AffineClosed := by
  intro d m Ω p u₀
  have hc : IsClosed (affineClass Ω m p u₀) :=
    (smoothSubmodule Ω m p).isClosed_topologicalClosure.preimage
      (continuous_id.sub continuous_const)
  refine ⟨hc, VariationalNotes.ConvexAnalysis.normClosed_convex_isWeaklyClosed _ hc ?_⟩
  change Convex ℝ ((fun u : W1p Ω m p => u - u₀) ⁻¹' (zeroSubmodule Ω m p : Set _))
  exact (zeroSubmodule Ω m p).convex.affine_preimage (AffineMap.id ℝ _ - AffineMap.const ℝ _ u₀)


/-- Assemble scalar boundary classes using the Euclidean coordinate basis. -/
def boundaryAssembly {n : ℕ} (Ω : Opens (Domain (n+1))) (m : ℕ) (p : Exponent) :
    (Fin m → P102.Trace.Ordinary.BoundaryLp ℝ Ω p.ennreal) →L[ℝ]
      BoundaryVectorLp Ω m p :=
  ∑ i : Fin m, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).compLpL p.ennreal
      (P102.Trace.Ordinary.boundaryMeasure Ω)).comp (ContinuousLinearMap.proj i)

/-- Coordinates of the assembled boundary representative, simultaneously a.e. -/
theorem boundaryAssembly_ae {n : ℕ} (Ω : Opens (Domain (n+1))) (m : ℕ) (p : Exponent)
    (v : Fin m → P102.Trace.Ordinary.BoundaryLp ℝ Ω p.ennreal) :
    ∀ᵐ x ∂P102.Trace.Ordinary.boundaryMeasure Ω,
      ∀ i, boundaryAssembly Ω m p v x i = v i x := by
  classical
  let J (i : Fin m) := (ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).compLpL p.ennreal
      (P102.Trace.Ordinary.boundaryMeasure Ω)
  have hc := Filter.eventually_all.mpr (fun i : Fin m =>
    (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single i (1 : ℝ))).coeFn_compLpL (v i))
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i => J i (v i))
  simp only [boundaryAssembly, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change ∀ᵐ x ∂P102.Trace.Ordinary.boundaryMeasure Ω,
    ∀ i, (∑ j : Fin m, J j (v j)) x i = v i x
  filter_upwards [hs, hc] with x hx hcx
  intro i
  rw [hx]
  simp [J, hcx, WithLp.ofLp_sum, ContinuousLinearMap.toSpanSingleton_apply,
    Pi.single_apply, mul_ite]

theorem boundaryAssembly_injective {n : ℕ} (Ω : Opens (Domain (n+1)))
    (m : ℕ) (p : Exponent) : Function.Injective (boundaryAssembly Ω m p) := by
  intro v w h
  funext i
  apply Lp.ext
  filter_upwards [boundaryAssembly_ae Ω m p v, boundaryAssembly_ae Ω m p w] with x hv hw
  exact (hv i).symm.trans ((congrArg (fun z : BoundaryVectorLp Ω m p => z x i) h).trans (hw i))

/-- The ordinary trace is transported coordinatewise through the continuous
linear equivalence for the manuscript's full Euclidean Sobolev norm. -/
theorem ordinary_trace : StructureExpected.Trace := by
  intro n m e Ω hΩ p
  obtain ⟨_, _, t, ht, _, _⟩ := P102.Trace.Ordinary.trace_exists n e Ω hΩ ℝ p.ennreal
    (by simp [Exponent.ennreal])
  have hk := P102.Trace.Ordinary.ordinary_trace.2.1 n e Ω hΩ ℝ p.ennreal
    (by simp [Exponent.ennreal]) t ht
  let S : W1p Ω m p →L[ℝ] (Fin m → P102.Trace.Ordinary.BoundaryLp ℝ Ω p.ennreal) :=
    ContinuousLinearMap.pi fun i => t.comp
      ((ContinuousLinearMap.proj i).comp (coordinateEquiv Ω p).toContinuousLinearMap)
  let T : W1p Ω m p →L[ℝ] BoundaryVectorLp Ω m p := (boundaryAssembly Ω m p).comp S
  refine ⟨T, ?_, ?_, ‖T‖, ContinuousLinearMap.opNorm_nonneg T, fun u => T.le_opNorm u⟩
  · intro u f hf hu
    have hc (i : Fin m) :
        (t (coordinateEquiv Ω p u i) : Domain (n+1) → ℝ) =ᵐ[
          P102.Trace.Ordinary.boundaryMeasure Ω] fun x => f x i := by
      apply ht
      · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).contDiff.comp hf
      · rw [coordinateEquiv_apply, toCoordinates_value]
        filter_upwards [coordinateLp_ae Ω p i (value Ω m p u), hu] with x hx hy
        exact hx.trans (congrArg (fun z : Vector m => z i) hy)
    have hcAll := Filter.eventually_all.mpr hc
    filter_upwards [boundaryAssembly_ae Ω m p (S u), hcAll] with x hx hy
    apply PiLp.ext
    intro i
    exact (hx i).trans (hy i)
  · apply Submodule.ext
    intro u
    change boundaryAssembly Ω m p (S u) = 0 ↔ u ∈ zeroSubmodule Ω m p
    rw [← (boundaryAssembly Ω m p).map_zero,
      (boundaryAssembly_injective Ω m p).eq_iff]
    rw [zero_mem_iff_coordinates Ω p u]
    change S u = 0 ↔ _
    rw [funext_iff]
    apply forall_congr'
    intro i
    change t (coordinateEquiv Ω p u i) = 0 ↔ _
    change coordinateEquiv Ω p u i ∈ t.ker ↔ _
    rw [hk]

end VariationalNotes.Sobolev
