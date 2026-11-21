import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.FixedBoundaryMinors
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.MinorDivergence

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped BigOperators ENNReal
namespace VariationalNotes.Sobolev.FixedBoundaryMinors
open Minors MinorDivergence

/-- Strong Sobolev convergence implies convergence of the full minor integral,
including at the critical exponent. -/
theorem minor_integral_tendsto {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1))
    {v : ℕ → W1p Ω m p} {u : W1p Ω m p} (hv : Tendsto v atTop (nhds u)) :
    Tendsto (fun k => ∫ x, minorField a (v k) x ∂domainMeasure Ω) atTop
      (nhds (∫ x, minorField a u x ∂domainMeasure Ω)) := by
  classical
  let : IsFiniteMeasure (domainMeasure Ω) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hΩ.measure_lt_top⟩
  let f (z : W1p Ω m p) (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :=
    coordinateLp Ω p (a.1.val (σ i), a.2.val i) (gradient Ω m p z)
  have ht (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
      Tendsto (fun k => f (v k) σ i) atTop (nhds (f u σ i)) :=
    ((coordinateLp Ω p _).continuous.comp (gradient Ω m p).continuous).continuousAt.tendsto.comp hv
  obtain ⟨w, z, hw, hz, hconv⟩ := tendsto_polynomial_L1
    (by simp [Exponent.ennreal] : p.ennreal ≠ ⊤) (order_le_ennreal p hp)
    (fun σ : Equiv.Perm (Fin (n+1)) => (Equiv.Perm.sign σ : ℝ))
    (fun k => f (v k)) (f u) ht
  have hrep (z : W1p Ω m p) :
      (fun x => ∑ σ : Equiv.Perm (Fin (n+1)),
        (Equiv.Perm.sign σ : ℝ) * ∏ i, f z σ i x) =ᵐ[domainMeasure Ω] minorField a z := by
    have hc (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :=
      coordinateLp_ae Ω p (a.1.val (σ i), a.2.val i) (gradient Ω m p z)
    filter_upwards [eventually_all.mpr (fun σ => eventually_all.mpr (hc σ))] with x hx
    simp only [minorField, minor, Matrix.det_apply', submatrix]
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    exact Finset.prod_congr rfl (fun i _ => hx σ i)
  have heq (k) : L1.integral (w k) = ∫ x, minorField a (v k) x ∂domainMeasure Ω := by
    rw [L1.integral_eq_integral]
    exact integral_congr_ae ((hw k).trans (hrep (v k)))
  have heq' : L1.integral z = ∫ x, minorField a u x ∂domainMeasure Ω := by
    rw [L1.integral_eq_integral]
    exact integral_congr_ae (hz.trans (hrep u))
  simpa only [Function.comp_def, heq, heq'] using
    L1.continuous_integral.continuousAt.tendsto.comp hconv

/-- Weak differentiation does not enlarge compact support inside the open set.
This transfers the scalar locality theorem to the canonical matrix gradient. -/
theorem gradient_zero_off_compact {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (w : W1p Ω m p) (K : Compacts (Domain d))
    (hw : ∀ᵐ x ∂domainMeasure Ω, x ∉ K → value Ω m p w x = 0) :
    ∀ᵐ x ∂domainMeasure Ω, x ∉ K → gradient Ω m p w x = 0 := by
  have hc (i : Fin m) : ∀ᵐ x ∂domainMeasure Ω,
      x ∉ K → P102.U4.sobolevUnderlying (coordinateEquiv Ω p w i) x = 0 := by
    have h := coordinateLp_ae Ω p i (value Ω m p w)
    rw [← toCoordinates_value] at h
    filter_upwards [h, hw] with x hx hy hxK
    exact hx.trans (by rw [hy hxK]; rfl)
  have hd (ij : Fin m × Fin d) := P102.U4.sobolevDerivative_zero_off_compact Ω 1 p.ennreal
    (coordinateEquiv Ω p w ij.1) K (hc ij.1) (⟨{ij.2}, by simp⟩)
  have he (ij : Fin m × Fin d) := coordinateLp_ae Ω p ij (gradient Ω m p w)
  filter_upwards [eventually_all.mpr hd, eventually_all.mpr he] with x hx hy hxK
  apply PiLp.ext
  intro ij
  have h := hx ij hxK
  simp only [coordinateEquiv_apply, toCoordinates_derivative] at h
  exact (hy ij).symm.trans h

/-- Compact support of the difference of the value and gradient fields allows
one cutoff to extract the full integral from the distributional identity. -/
theorem integral_eq_of_fields_eq_off_compact {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (u v : W1p Ω m p)
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω)
    (hv : ∀ᵐ x ∂domainMeasure Ω, x ∉ K → value Ω m p u x = value Ω m p v x)
    (hg : ∀ᵐ x ∂domainMeasure Ω, x ∉ K → gradient Ω m p u x = gradient Ω m p v x) :
    (∫ x, minorField a u x ∂domainMeasure Ω) =
      ∫ x, minorField a v x ∂domainMeasure Ω := by
  classical
  obtain ⟨χ, _, U, hKU, _, hχ⟩ := P102.U4.cutoff d Ω K hK
  have hχK (x : Domain d) (hx : x ∈ K) : χ x = 1 := hχ x (hKU hx)
  have hDχ (j : Fin d) (x : Domain d) (hx : x ∈ K) :
      P102.U4.testPartialWord Ω [j] χ x = 0 := by
    have heq : (χ : Domain d → ℝ) =ᶠ[nhds x] (fun _ => 1) :=
      Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds (hKU hx)) (fun y hy => hχ y hy)
    rw [P102.U4.testPartialWord_coe]
    simp only [P102.U4.partialWord]
    rw [heq.fderiv_eq]
    simp
  have hmu := fields_locallyIntegrable hΩ p hp a u
  have hmv := fields_locallyIntegrable hΩ p hp a v
  have hflux (l : Fin (n+1)) :
      P102.U4.regularDistribution Ω (fluxField a u l)
          (P102.U4.testPartialWord Ω [a.2.val l] χ) =
        P102.U4.regularDistribution Ω (fluxField a v l)
          (P102.U4.testPartialWord Ω [a.2.val l] χ) := by
    rw [P102.U4.regular_pairing d ℝ Ω _ (hmu.2 l),
      P102.U4.regular_pairing d ℝ Ω _ (hmv.2 l)]
    apply integral_congr_ae
    filter_upwards [hv, hg] with x hx hy
    by_cases hxK : x ∈ K
    · simp only [hDχ _ x hxK, mul_zero]
    · simp only [fluxField, hx hxK, hy hxK]
  have hpair (z : W1p Ω m p) :
      P102.U4.regularDistribution Ω (minorField a z) χ =
        ∑ l : Fin (n+1), -P102.U4.regularDistribution Ω (fluxField a z l)
          (P102.U4.testPartialWord Ω [a.2.val l] χ) := by
    have h := congrArg (fun T : P102.U4.DistributionSpace ℝ Ω => T χ)
      (sobolev_minor_divergence Ω hΩ p hp a z).2.2
    simpa only [sum_apply, P102.U4.distributionPartial_singleton_apply] using h
  have hpair_eq : P102.U4.regularDistribution Ω (minorField a u) χ =
      P102.U4.regularDistribution Ω (minorField a v) χ := by
    rw [hpair u, hpair v]
    exact Finset.sum_congr rfl (fun l _ => congrArg Neg.neg (hflux l))
  have hiu := minorField_integrable hΩ p hp a u
  have hiv := minorField_integrable hΩ p hp a v
  have hiχ (z : W1p Ω m p) :
      Integrable (fun x => minorField a z x * χ x) (domainMeasure Ω) := by
    have hi := χ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (fields_locallyIntegrable hΩ p hp a z).1
    exact hi.integrableOn.congr (Eventually.of_forall fun x => mul_comm _ _)
  have heq : (∫ x, (minorField a u x - minorField a v x) ∂domainMeasure Ω) = 0 := by
    calc
      _ = ∫ x, (minorField a u x - minorField a v x) * χ x ∂domainMeasure Ω := by
        apply integral_congr_ae
        filter_upwards [hg] with x hx
        by_cases hxK : x ∈ K
        · rw [hχK x hxK, mul_one]
        · simp only [minorField, hx hxK, sub_self, zero_mul]
      _ = (∫ x, minorField a u x * χ x ∂domainMeasure Ω) -
          ∫ x, minorField a v x * χ x ∂domainMeasure Ω := by
        simp_rw [sub_mul]
        exact integral_sub (hiχ u) (hiχ v)
      _ = 0 := by
        rw [← P102.U4.regular_pairing d ℝ Ω _ hmu.1,
          ← P102.U4.regular_pairing d ℝ Ω _ hmv.1, hpair_eq, sub_self]
  rw [integral_sub hiu hiv, sub_eq_zero] at heq
  exact heq

/-- Adding a Sobolev map supported on a compact subset of Ω preserves every
integral of a minor. No classical boundary trace is used. -/
theorem integral_add_eq_of_compact_support {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (v w : W1p Ω m p)
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω)
    (hw : ∀ᵐ x ∂domainMeasure Ω, x ∉ K → value Ω m p w x = 0) :
    (∫ x, minorField a (v+w) x ∂domainMeasure Ω) =
      ∫ x, minorField a v x ∂domainMeasure Ω := by
  have hgw := gradient_zero_off_compact w K hw
  have hvadd : (value Ω m p (v+w) : Domain d → Vector m) =ᵐ[domainMeasure Ω]
      fun x => value Ω m p v x + value Ω m p w x := by
    simpa only [map_add, Pi.add_def] using Lp.coeFn_add (value Ω m p v) (value Ω m p w)
  have hgadd : (gradient Ω m p (v+w) : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
      fun x => gradient Ω m p v x + gradient Ω m p w x := by
    simpa only [map_add, Pi.add_def] using Lp.coeFn_add (gradient Ω m p v) (gradient Ω m p w)
  apply integral_eq_of_fields_eq_off_compact hΩ p hp a (v+w) v K hK
  · filter_upwards [hvadd, hw] with x hx hy hxK
    rw [hx, hy hxK, add_zero]
  · filter_upwards [hgadd, hgw] with x hx hy hxK
    rw [hx, hy hxK, add_zero]

/-- In particular every smooth compactly supported difference is admissible in
the preceding cutoff argument, using its actual Lp representative. -/
theorem integral_add_eq_of_vector_test {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (v w : W1p Ω m p)
    (φ : VectorTest Ω m) (hw : value Ω m p w = testToValueLp Ω m p φ) :
    (∫ x, minorField a (v+w) x ∂domainMeasure Ω) =
      ∫ x, minorField a v x ∂domainMeasure Ω := by
  let K : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  apply integral_add_eq_of_compact_support hΩ p hp a v w K φ.tsupport_subset
  have hrep : (value Ω m p w : Domain d → Vector m) =ᵐ[domainMeasure Ω] φ := by
    rw [hw]
    exact (φ.continuous.memLp_of_hasCompactSupport
      (p := p.ennreal) (μ := domainMeasure Ω) φ.hasCompactSupport).coeFn_toLp
  filter_upwards [hrep] with x hx hxK
  exact hx.trans (image_eq_zero_of_notMem_tsupport hxK)

/-- The full fixed-boundary identity of Proposition `prop:fixed-trace-minors`.
Approximation is in the stipulated Sobolev norm; strong L¹ convergence of the
minors handles p=j as well as p>j. -/
theorem fixed_boundary_integrals : Expected.FixedBoundaryIntegrals := by
  intro d m n Ω hΩ p hp u v huv a
  change (∫ x, minorField a u x ∂domainMeasure Ω) =
    ∫ x, minorField a v x ∂domainMeasure Ω
  change u - v ∈ (zeroSubmodule Ω m p : Set (W1p Ω m p)) at huv
  rw [zero_closure Ω p] at huv
  obtain ⟨w, hw, hconv⟩ := mem_closure_iff_seq_limit.mp huv
  have heq (k : ℕ) :
      (∫ x, minorField a (v + w k) x ∂domainMeasure Ω) =
        ∫ x, minorField a v x ∂domainMeasure Ω := by
    obtain ⟨φ, hφ⟩ := hw k
    exact integral_add_eq_of_vector_test hΩ p hp a v (w k) φ hφ
  have hsum : v + (u-v) = u := by abel
  have ht : Tendsto (fun k => v + w k) atTop (nhds u) := by
    rw [← hsum]
    exact tendsto_const_nhds.add hconv
  exact tendsto_nhds_unique (minor_integral_tendsto hΩ p hp a ht)
    (by simpa only [heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ∫ x, minorField a v x ∂domainMeasure Ω) atTop
        (nhds (∫ x, minorField a v x ∂domainMeasure Ω))))

end VariationalNotes.Sobolev.FixedBoundaryMinors
