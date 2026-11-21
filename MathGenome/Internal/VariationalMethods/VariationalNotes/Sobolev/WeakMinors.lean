import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.WeakMinors
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Compactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Minors
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.MinorDivergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorLpReflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14ReflexiveExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14WeakSubsequence
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace VariationalNotes.Sobolev.WeakMinors
open Minors

/-- Weak convergence bounds the original Sobolev norms, by uniform boundedness
on the complete dual. Completeness or reflexivity of W¹ᵖ is not needed here. -/
theorem weaklyConverges_bounded {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {u : ℕ → W1p Ω m p} {v : W1p Ω m p} (hu : WeaklyConverges u v) :
    Bornology.IsBounded (range u) := by
  obtain ⟨C, _, hC⟩ :=
    ExpandedFA.P1.C12BoundedSequences.norm_bound_of_scalar_bounds ℝ (W1p Ω m p) ℕ u
      (fun ℓ => by
        obtain ⟨B, hB⟩ := (hu ℓ).norm.bddAbove_range
        exact ⟨B, fun k => hB (mem_range_self k)⟩)
  exact isBounded_iff_forall_norm_le.mpr ⟨C, by
    rintro _ ⟨k, rfl⟩
    exact hC k⟩

/-- Relative compactness together with weak convergence gives strong convergence
of the whole sequence. A compact limit of any subsequence is identified by all
continuous linear functionals, and hence equals the prescribed weak limit. -/
theorem strong_of_weak_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → E} {g : E}
    (hw : ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun k => ℓ (f k)) atTop (nhds (ℓ g)))
    (hc : IsCompact (closure (range f))) : Tendsto f atTop (nhds g) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨z, _, ms, hms, hz⟩ := hc.tendsto_subseq
    (fun k => subset_closure (mem_range_self (ns k)))
  have hzg : z = g := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    exact tendsto_nhds_unique ((ℓ.continuous.tendsto z).comp hz)
      (((hw ℓ).comp hns).comp hms.tendsto_atTop)
  exact ⟨ms, hzg ▸ hz⟩

theorem strong_lipschitz : Expected.StrongLipschitz := by
  intro n e Ω hΩ m p u v hu
  apply strong_of_weak_of_compact
  · intro ℓ
    exact hu (ℓ.comp (value Ω m p))
  · have hc := compactness_lipschitz n e Ω hΩ m p (range u) (weaklyConverges_bounded hu)
    simpa only [← range_comp, Function.comp_def] using hc

theorem strong_affine : Expected.StrongAffine := by
  intro d hd Ω hΩ m p u₀ u v hclass hu
  apply strong_of_weak_of_compact
  · intro ℓ
    exact hu (ℓ.comp (value Ω m p))
  · have hc := compactness_affine hd Ω hΩ m p u₀ (range u)
      (weaklyConverges_bounded hu) (by
        rintro _ ⟨k, rfl⟩
        exact hclass k)
    simpa only [← range_comp, Function.comp_def] using hc

theorem minorExponent_zero (p : Exponent) (hp : (0+1 : ℕ) ≤ p.real) :
    minorExponent p 0 hp = p := by
  cases p
  simp [minorExponent]

theorem first_order : Expected.FirstOrder := by
  intro d m Ω p u v hu
  unfold MinorWeakConvergence
  rw [minorExponent_zero]
  unfold HasWeakLpLimit
  let T : GradientLp Ω m p →L[ℝ]
      Lp (MinorVector m d 1) p.ennreal (domainMeasure Ω) :=
    (firstIsometry m d).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      p.ennreal (domainMeasure Ω)
  refine ⟨fun k => T (gradient Ω m p (u k)), T (gradient Ω m p v), ?_, ?_, ?_⟩
  · intro k
    filter_upwards [(firstIsometry m d).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (p := p.ennreal) (μ := domainMeasure Ω) (gradient Ω m p (u k))] with x hx
    exact hx.trans (firstIsometry_eq _)
  · filter_upwards [(firstIsometry m d).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (p := p.ennreal) (μ := domainMeasure Ω) (gradient Ω m p v)] with x hx
    exact hx.trans (firstIsometry_eq _)
  · intro ℓ
    exact hu (ℓ.comp (T.comp (gradient Ω m p)))

/-- Deleting the first selected row and one selected column preserves the
increasing-index convention of the canonical minor coordinates. -/
def cofactorIndex {m d n : ℕ} (a : Index m d (n+1)) (l : Fin (n+1)) : Index m d n :=
  (⟨fun i => a.1.val i.succ, a.1.property.comp Fin.strictMono_succ⟩,
   ⟨fun i => a.2.val (l.succAbove i), a.2.property.comp (Fin.strictMono_succAbove l)⟩)

theorem cofactor_eq_signed_minor {m d n : ℕ} (a : Index m d (n+1))
    (l : Fin (n+1)) (Z : Gradient m d) :
    cofactor a l Z = (-1 : ℝ) ^ l.val * minor (cofactorIndex a l) Z := rfl

theorem minorExponent_ennreal (p : Exponent) (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real) :
    (minorExponent p n hp).ennreal =
      (∑ _i : Fin (n+1), p.ennreal⁻¹)⁻¹ := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change ENNReal.ofReal (p.real / (n+1)) = _
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < n+1)]
  simp [Exponent.ennreal, ENNReal.mul_inv, div_eq_mul_inv, mul_comm,
    ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ n) zero_le_one]

theorem minorField_memLp {d m n : ℕ} {Ω : Opens (Domain d)}
    (p : Exponent) (hp : (n+1 : ℕ) ≤ p.real)
    (a : Index m d (n+1)) (u : W1p Ω m p) :
    MemLp (MinorDivergence.minorField a u) (minorExponent p n hp).ennreal
      (domainMeasure Ω) := by
  classical
  change MemLp (fun x => minor a (gradient Ω m p u x)) _ _
  simp only [minor, Matrix.det_apply']
  apply memLp_finsetSum
  intro σ _
  apply MemLp.const_mul
  rw [minorExponent_ennreal]
  exact MemLp.fun_prod (s := Finset.univ) (fun i _ =>
    MinorDivergence.coordinate_memLp Ω p
      (a.1.val (σ i), a.2.val i) (gradient Ω m p u))

/-- The entire finite Euclidean vector belongs to the required quotient space. -/
theorem minors_memLp {d m n : ℕ} (Ω : Opens (Domain d))
    (p : Exponent) (hp : (n+1 : ℕ) ≤ p.real) (u : W1p Ω m p) :
    MemLp (fun x => minors (n+1) (gradient Ω m p u x))
      (minorExponent p n hp).ennreal (domainMeasure Ω) := by
  apply memLp_piLp_iff.mpr
  intro a
  exact minorField_memLp p hp a u

/-- Canonical Lp class of the minor vector, independent of representative choices. -/
def minorsLp {d m n : ℕ} (Ω : Opens (Domain d))
    (p : Exponent) (hp : (n+1 : ℕ) ≤ p.real) (u : W1p Ω m p) :
    Lp (MinorVector m d (n+1)) (minorExponent p n hp).ennreal (domainMeasure Ω) :=
  (minors_memLp Ω p hp u).toLp _

theorem minorsLp_ae {d m n : ℕ} (Ω : Opens (Domain d))
    (p : Exponent) (hp : (n+1 : ℕ) ≤ p.real) (u : W1p Ω m p) :
    (minorsLp Ω p hp u : Domain d → MinorVector m d (n+1)) =ᵐ[domainMeasure Ω]
      fun x => minors (n+1) (gradient Ω m p u x) :=
  (minors_memLp Ω p hp u).coeFn_toLp

/-- The representative formulation is equivalent to testing the canonical Lp
classes. In particular it cannot conceal an unrelated choice of weak limit. -/
theorem minorWeakConvergence_iff {d m n : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (hp : (n+1 : ℕ) ≤ p.real) (u : ℕ → W1p Ω m p) (v : W1p Ω m p) :
    MinorWeakConvergence n hp u v ↔
      ∀ ℓ : Lp (MinorVector m d (n+1)) (minorExponent p n hp).ennreal
          (domainMeasure Ω) →L[ℝ] ℝ,
        Tendsto (fun k => ℓ (minorsLp Ω p hp (u k))) atTop
          (nhds (ℓ (minorsLp Ω p hp v))) := by
  constructor
  · rintro ⟨f, g, hf, hg, ht⟩ ℓ
    have hfeq : f = fun k => minorsLp Ω p hp (u k) := by
      funext k
      exact Lp.ext ((hf k).trans (minorsLp_ae Ω p hp (u k)).symm)
    have hgeq : g = minorsLp Ω p hp v :=
      Lp.ext (hg.trans (minorsLp_ae Ω p hp v).symm)
    simpa only [hfeq, hgeq] using ht ℓ
  · intro h
    exact ⟨fun k => minorsLp Ω p hp (u k), minorsLp Ω p hp v,
      fun k => minorsLp_ae Ω p hp (u k), minorsLp_ae Ω p hp v, h⟩

/-- A continuous linear map of the finite-dimensional fibers transports weak
Lp convergence, including the almost-everywhere representative assertions. -/
theorem HasWeakLpLimit.map {d : ℕ} {Ω : Opens (Domain d)} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : Exponent} {f : ℕ → Domain d → E} {g : Domain d → E}
    (h : HasWeakLpLimit Ω q f g) (T : E →L[ℝ] F) :
    HasWeakLpLimit Ω q (fun k x => T (f k x)) (fun x => T (g x)) := by
  obtain ⟨v, w, hv, hw, ht⟩ := h
  refine ⟨fun k => T.compLpL q.ennreal (domainMeasure Ω) (v k),
    T.compLpL q.ennreal (domainMeasure Ω) w, ?_, ?_, ?_⟩
  · intro k
    exact (T.coeFn_compLpL (v k)).trans ((hv k).fun_comp T)
  · exact (T.coeFn_compLpL w).trans (hw.fun_comp T)
  · intro ℓ
    exact ht (ℓ.comp (T.compLpL q.ennreal (domainMeasure Ω)))

/-- Cofactors in an order-(n+2) minor are signed coordinates of the full
order-(n+1) minor vector, with the same Lp exponent as that lower-order vector. -/
theorem weak_cofactor_of_weak_minors {d m n : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (hp : (n+1 : ℕ) ≤ p.real) {u : ℕ → W1p Ω m p} {v : W1p Ω m p}
    (h : MinorWeakConvergence n hp u v)
    (a : Index m d (n+2)) (l : Fin (n+2)) :
    HasWeakLpLimit Ω (minorExponent p n hp)
      (fun k x => cofactor a l (gradient Ω m p (u k) x))
      (fun x => cofactor a l (gradient Ω m p v x)) := by
  let T : MinorVector m d (n+1) →L[ℝ] ℝ :=
    ((-1 : ℝ) ^ l.val) • PiLp.proj 2 (fun _ : Index m d (n+1) => ℝ)
      (cofactorIndex a l)
  exact HasWeakLpLimit.map h T

theorem minor_norm_le {m d j : ℕ} (a : Index m d j) (Z : Gradient m d) :
    ‖minor a Z‖ ≤ (Fintype.card (Equiv.Perm (Fin j)) : ℝ) * ‖Z‖ ^ j := by
  classical
  unfold minor
  rw [Matrix.det_apply']
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin j), ‖Z‖ ^ j := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, norm_prod]
      have hsign : ‖(↑↑(Equiv.Perm.sign σ) : ℝ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [hsign, one_mul]
      have h := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => norm_nonneg _)
        (fun i _ => PiLp.norm_apply_le Z (a.1.val (σ i), a.2.val i))
      simpa [submatrix] using h
    _ = _ := by simp

theorem euclidean_norm_le_sum {ι : Type*} [Fintype ι] (Z : EuclideanSpace ℝ ι) :
    ‖Z‖ ≤ ∑ i, ‖Z i‖ := by
  classical
  have hZ : Z = ∑ i, PiLp.single 2 i (Z i) := by
    ext k
    simp
  calc
    ‖Z‖ = ‖∑ i, PiLp.single 2 i (Z i)‖ := congrArg norm hZ
    _ ≤ ∑ i, ‖(PiLp.single 2 i (Z i) : EuclideanSpace ℝ ι)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem minors_norm_le {m d j : ℕ} (Z : Gradient m d) :
    ‖minors j Z‖ ≤
      ((Fintype.card (Index m d j) * Fintype.card (Equiv.Perm (Fin j)) : ℕ) : ℝ) *
        ‖Z‖ ^ j := by
  classical
  refine (euclidean_norm_le_sum _).trans ?_
  calc
    _ ≤ ∑ a : Index m d j, (Fintype.card (Equiv.Perm (Fin j)) : ℝ) * ‖Z‖ ^ j :=
      Finset.sum_le_sum (fun a _ => minor_norm_le a Z)
    _ = _ := by simp [Nat.cast_mul, mul_assoc]

theorem minorExponent_div (p : Exponent) (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real) :
    (minorExponent p n hp).ennreal = p.ennreal / (n+1 : ℕ) := by
  change ENNReal.ofReal (p.real / (n+1)) = _
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < n+1)]
  congr 1
  simp [ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ n) zero_le_one]

theorem minorExponent_mul (p : Exponent) (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real) :
    (minorExponent p n hp).ennreal * (n+1 : ℕ) = p.ennreal := by
  rw [minorExponent_div, ENNReal.div_mul_cancel (by positivity) (by simp)]

theorem norm_power_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : Exponent) (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real)
    (f : Lp E p.ennreal μ) :
    MemLp (fun x => ‖f x‖ ^ (n+1)) (minorExponent p n hp).ennreal μ := by
  have h := (Lp.memLp f).norm_rpow_div (n+1 : ℕ)
  rw [minorExponent_div]
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using h

theorem norm_power_norm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : Exponent) (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real)
    (f : Lp E p.ennreal μ) :
    ‖(norm_power_memLp p n hp f).toLp _‖ = ‖f‖ ^ (n+1) := by
  rw [Lp.norm_toLp]
  have hr := eLpNorm_norm_rpow (p := (minorExponent p n hp).ennreal) f
    (Lp.aestronglyMeasurable f) (by positivity : (0:ℝ) < (n+1 : ℕ))
  simp only [ENNReal.ofReal_natCast, minorExponent_mul, ENNReal.rpow_natCast] at hr
  simp only [Real.rpow_natCast] at hr
  rw [hr, ENNReal.toReal_pow]
  rfl

/-- A polynomial growth estimate in the exact target exponent. -/
theorem minorsLp_norm_le {d m n : ℕ} (Ω : Opens (Domain d))
    (p : Exponent) (hp : (n+1 : ℕ) ≤ p.real) (u : W1p Ω m p) :
    ‖minorsLp Ω p hp u‖ ≤
      ((Fintype.card (Index m d (n+1)) *
        Fintype.card (Equiv.Perm (Fin (n+1))) : ℕ) : ℝ) *
          ‖gradient Ω m p u‖ ^ (n+1) := by
  let G := gradient Ω m p u
  let H := (norm_power_memLp p n hp G).toLp _
  have hH : (H : Domain d → ℝ) =ᵐ[domainMeasure Ω] fun x => ‖G x‖ ^ (n+1) :=
    (norm_power_memLp p n hp G).coeFn_toLp
  have he : ‖minorsLp Ω p hp u‖ ≤
      ((Fintype.card (Index m d (n+1)) *
        Fintype.card (Equiv.Perm (Fin (n+1))) : ℕ) : ℝ) * ‖H‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [minorsLp_ae Ω p hp u, hH] with x hx hy
    rw [hx, hy, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact minors_norm_le _
  simpa only [H, norm_power_norm, G] using he

theorem minorsLp_bounded {d m n : ℕ} (Ω : Opens (Domain d))
    (p : Exponent) (hp : (n+1 : ℕ) ≤ p.real) {A : Set (W1p Ω m p)}
    (hA : Bornology.IsBounded A) :
    Bornology.IsBounded (minorsLp Ω p hp '' A) := by
  obtain ⟨C, hC⟩ := hA.exists_norm_le
  let K := ((Fintype.card (Index m d (n+1)) *
    Fintype.card (Equiv.Perm (Fin (n+1))) : ℕ) : ℝ)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨K * (‖gradient Ω m p‖ * max C 0) ^ (n+1), ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine (minorsLp_norm_le Ω p hp u).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ K)
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((gradient Ω m p).le_opNorm u).trans
    (mul_le_mul_of_nonneg_left ((hC u hu).trans (le_max_left _ _)) ((gradient Ω m p).opNorm_nonneg))

theorem weak_convergence_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → E} {g : E}
    (hf : ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun k => ℓ (f k)) atTop (nhds (ℓ g))) :
    Bornology.IsBounded (range f) := by
  obtain ⟨C, _, hC⟩ :=
    ExpandedFA.P1.C12BoundedSequences.norm_bound_of_scalar_bounds ℝ E ℕ f
      (fun ℓ => by
        obtain ⟨B, hB⟩ := (hf ℓ).norm.bddAbove_range
        exact ⟨B, fun k => hB (mem_range_self k)⟩)
  exact isBounded_iff_forall_norm_le.mpr ⟨C, by
    rintro _ ⟨k, rfl⟩
    exact hC k⟩

/-- Strong convergence in one argument and weak convergence in the other
suffice for any scalar continuous bilinear pairing. -/
theorem tendsto_strong_weak_bilinear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] F →L[ℝ] ℝ) {f : ℕ → E} {g : ℕ → F} {x : E} {y : F}
    (hf : Tendsto f atTop (nhds x))
    (hg : ∀ ℓ : F →L[ℝ] ℝ, Tendsto (fun k => ℓ (g k)) atTop (nhds (ℓ y))) :
    Tendsto (fun k => B (f k) (g k)) atTop (nhds (B x y)) := by
  obtain ⟨C, hC⟩ := (weak_convergence_bounded hg).exists_norm_le
  have hvanish : Tendsto (fun k => B (f k - x) (g k)) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (by simpa using (hf.sub_const x).norm.mul_const (‖B‖ * max C 0))
    · calc
        ‖B (f k - x) (g k)‖ ≤ ‖B‖ * ‖f k - x‖ * ‖g k‖ := B.le_opNorm₂ _ _
        _ ≤ ‖f k - x‖ * (‖B‖ * max C 0) := by
          have hc := (hC (g k) (mem_range_self k)).trans (le_max_left C 0)
          calc
            _ ≤ ‖B‖ * ‖f k - x‖ * max C 0 :=
              mul_le_mul_of_nonneg_left hc (mul_nonneg B.opNorm_nonneg (norm_nonneg _))
            _ = _ := by ring
  have ht := hvanish.add (hg (B x))
  simpa only [map_sub, sub_apply, sub_add_cancel, zero_add] using ht

/-- Reflexive extraction and uniqueness of regular distributions upgrade bounded
coordinate-test convergence to weak convergence of the entire Lp sequence. -/
theorem weak_of_test_tendsto {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) {ι : Type*} [Fintype ι]
    {f : ℕ → Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)}
    {g : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)}
    (hb : Bornology.IsBounded (range f))
    (ht : ∀ i (φ : P102.U4.TestSpace ℝ Ω),
      Tendsto (fun k => P102.U4.lpTestPairing Ω p.ennreal φ (coordinateLp Ω p i (f k)))
        atTop (nhds (P102.U4.lpTestPairing Ω p.ennreal φ (coordinateLp Ω p i g)))) :
    ∀ ℓ : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω) →L[ℝ] ℝ,
      Tendsto (fun k => ℓ (f k)) atTop (nhds (ℓ g)) := by
  let E := Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)
  have href := ExpandedFA.PartIV.VectorLpReflexive.lp_reflexive ℝ
    (ExpandedFA.P1.C14ReflexiveExamples.hilbert_reflexive ℝ (EuclideanSpace ℝ ι))
    (domainMeasure Ω) p.ennreal
    (by simpa [Exponent.ennreal] using ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hp)
    (by simp [Exponent.ennreal])
  intro ℓ
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hb' : Bornology.IsBounded (range (f ∘ ns)) :=
    hb.subset (range_comp_subset_range _ _)
  obtain ⟨ms, hms, z, hz⟩ :=
    ExpandedFA.P1.C14WeakSubsequence.reflexive_weak_subsequence ℝ E href (f ∘ ns) hb'
  have hzw : ∀ L : E →L[ℝ] ℝ,
      Tendsto (fun k => L (f (ns (ms k)))) atTop (nhds (L z)) := by
    rw [ExpandedFA.P1.dualPairTopology_evaluation ℝ E, nhds_iInf] at hz
    simpa only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def] using hz
  have hzg : z = g := by
    apply coordinateLp_ext Ω p
    intro i
    apply Lp.ext
    apply (P102.U4.regular_injectivity d ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω p.ennreal (coordinateLp Ω p i z))
      (P102.U4.domainLp_locallyIntegrable Ω p.ennreal (coordinateLp Ω p i g))).mp
    ext φ
    rw [P102.U4.regularLp_pairing, P102.U4.regularLp_pairing]
    exact tendsto_nhds_unique
      (hzw ((P102.U4.lpTestPairing Ω p.ennreal φ).comp (coordinateLp Ω p i)))
      (((ht i φ).comp hns).comp hms.tendsto_atTop)
  exact ⟨ms, by simpa only [hzg] using hzw ℓ⟩

def productTestPairing {d : ℕ} (Ω : Opens (Domain d)) (p q r : Exponent)
    [ENNReal.HolderTriple p.ennreal q.ennreal r.ennreal]
    (φ : P102.U4.TestSpace ℝ Ω) :
    Lp ℝ p.ennreal (domainMeasure Ω) →L[ℝ]
      Lp ℝ q.ennreal (domainMeasure Ω) →L[ℝ] ℝ :=
  ((P102.U4.lpTestPairing Ω r.ennreal φ).postcomp
    (Lp ℝ q.ennreal (domainMeasure Ω))).comp
      ((ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure Ω)
        p.ennreal q.ennreal r.ennreal)

theorem productTestPairing_eq {d : ℕ} (Ω : Opens (Domain d)) (p q r : Exponent)
    [ENNReal.HolderTriple p.ennreal q.ennreal r.ennreal]
    (φ : P102.U4.TestSpace ℝ Ω)
    (f : Lp ℝ p.ennreal (domainMeasure Ω)) (g : Lp ℝ q.ennreal (domainMeasure Ω)) :
    productTestPairing Ω p q r φ f g = ∫ x, (f x * g x) * φ x ∂domainMeasure Ω := by
  change P102.U4.lpTestPairing Ω r.ennreal φ
    ((ContinuousLinearMap.mul ℝ ℝ).holder r.ennreal f g) = _
  rw [P102.U4.lpTestPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := r.ennreal) f g] with x hx
  rw [hx]
  rfl

theorem tendsto_test_product {d : ℕ} (Ω : Opens (Domain d)) (p q r : Exponent)
    [ENNReal.HolderTriple p.ennreal q.ennreal r.ennreal]
    (φ : P102.U4.TestSpace ℝ Ω)
    {f : ℕ → Lp ℝ p.ennreal (domainMeasure Ω)}
    {g : ℕ → Lp ℝ q.ennreal (domainMeasure Ω)}
    {x : Lp ℝ p.ennreal (domainMeasure Ω)} {y : Lp ℝ q.ennreal (domainMeasure Ω)}
    (hf : Tendsto f atTop (nhds x))
    (hg : ∀ ℓ : Lp ℝ q.ennreal (domainMeasure Ω) →L[ℝ] ℝ,
      Tendsto (fun k => ℓ (g k)) atTop (nhds (ℓ y))) :
    Tendsto (fun k => ∫ z, (f k z * g k z) * φ z ∂domainMeasure Ω) atTop
      (nhds (∫ z, (x z * y z) * φ z ∂domainMeasure Ω)) := by
  simpa only [productTestPairing_eq] using
    tendsto_strong_weak_bilinear (productTestPairing Ω p q r φ) hf hg

theorem minorExponent_holder (p : Exponent) (n : ℕ)
    (hp1 : (n+1 : ℕ) ≤ p.real) (hp2 : (n+1+1 : ℕ) ≤ p.real) :
    ENNReal.HolderTriple p.ennreal (minorExponent p n hp1).ennreal
      (minorExponent p (n+1) hp2).ennreal := by
  constructor
  rw [minorExponent_div, minorExponent_div,
    ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by positivity)),
    ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by positivity))]
  rw [← one_div p.ennreal, ENNReal.div_add_div_same]
  congr 1
  simp [add_comm, add_left_comm]
  norm_num

/-- The divergence fluxes converge on each smooth test by strong--weak pairing. -/
theorem flux_regular_tendsto {d m n : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp1 : (n+1 : ℕ) ≤ p.real) (hp2 : (n+1+1 : ℕ) ≤ p.real)
    {u : ℕ → W1p Ω m p} {v : W1p Ω m p}
    (hs : Tendsto (fun k => value Ω m p (u k)) atTop (nhds (value Ω m p v)))
    (hw : MinorWeakConvergence n hp1 u v)
    (a : Index m d (n+1+1)) (l : Fin (n+1+1)) (φ : P102.U4.TestSpace ℝ Ω) :
    Tendsto (fun k => P102.U4.regularDistribution Ω (MinorDivergence.fluxField a (u k) l) φ)
      atTop (nhds (P102.U4.regularDistribution Ω (MinorDivergence.fluxField a v l) φ)) := by
  let q := minorExponent p n hp1
  let r := minorExponent p (n+1) hp2
  let : ENNReal.HolderTriple p.ennreal q.ennreal r.ennreal := minorExponent_holder p n hp1 hp2
  obtain ⟨F, G, hF, hG, ht⟩ := weak_cofactor_of_weak_minors hp1 hw a l
  have heq (w : W1p Ω m p) (g : Lp ℝ q.ennreal (domainMeasure Ω))
      (hg : (g : Domain d → ℝ) =ᵐ[domainMeasure Ω]
        fun x => cofactor a l (gradient Ω m p w x)) :
      P102.U4.regularDistribution Ω (MinorDivergence.fluxField a w l) φ =
        ∫ x, (coordinateLp Ω p (a.1.val 0) (value Ω m p w) x * g x) * φ x
          ∂domainMeasure Ω := by
    rw [P102.U4.regular_pairing d ℝ Ω _
      ((MinorDivergence.sobolev_minor_divergence Ω hΩ p hp2 a w).2.1 l)]
    apply integral_congr_ae
    filter_upwards [coordinateLp_ae Ω p (a.1.val 0) (value Ω m p w), hg] with x hx hy
    simp only [hx, hy, MinorDivergence.fluxField]
  simp_rw [heq _ _ (hF _), heq _ _ hG]
  exact tendsto_test_product Ω p q r φ
    (((coordinateLp Ω p (a.1.val 0)).continuous.tendsto _).comp hs) ht

/-- Accepted divergence identities turn flux convergence into convergence of
all order-(n+2) minor distributions. -/
theorem minor_regular_tendsto {d m n : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp1 : (n+1 : ℕ) ≤ p.real) (hp2 : (n+1+1 : ℕ) ≤ p.real)
    {u : ℕ → W1p Ω m p} {v : W1p Ω m p}
    (hs : Tendsto (fun k => value Ω m p (u k)) atTop (nhds (value Ω m p v)))
    (hw : MinorWeakConvergence n hp1 u v)
    (a : Index m d (n+1+1)) (φ : P102.U4.TestSpace ℝ Ω) :
    Tendsto (fun k => P102.U4.regularDistribution Ω (MinorDivergence.minorField a (u k)) φ)
      atTop (nhds (P102.U4.regularDistribution Ω (MinorDivergence.minorField a v) φ)) := by
  have heq (w : W1p Ω m p) :
      P102.U4.regularDistribution Ω (MinorDivergence.minorField a w) φ =
        ∑ l : Fin (n+1+1), -P102.U4.regularDistribution Ω (MinorDivergence.fluxField a w l)
          (P102.U4.testPartialWord Ω [a.2.val l] φ) := by
    have h := congrArg (fun T : P102.U4.DistributionSpace ℝ Ω => T φ)
      (MinorDivergence.sobolev_minor_divergence Ω hΩ p hp2 a w).2.2
    simpa only [sum_apply, P102.U4.distributionPartial_singleton_apply] using h
  simp_rw [heq]
  exact tendsto_finsetSum Finset.univ (fun l _ =>
    (flux_regular_tendsto Ω hΩ p hp1 hp2 hs hw a l
      (P102.U4.testPartialWord Ω [a.2.val l] φ)).neg)

theorem minorsLp_test_eq_regular {d m n : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (u : W1p Ω m p)
    (φ : P102.U4.TestSpace ℝ Ω) :
    P102.U4.lpTestPairing Ω (minorExponent p n hp).ennreal φ
      (coordinateLp Ω (minorExponent p n hp) a (minorsLp Ω p hp u)) =
        P102.U4.regularDistribution Ω (MinorDivergence.minorField a u) φ := by
  rw [P102.U4.lpTestPairing_eq_integral,
    P102.U4.regular_pairing d ℝ Ω _ (MinorDivergence.fields_locallyIntegrable hΩ p hp a u).1]
  apply integral_congr_ae
  filter_upwards [coordinateLp_ae Ω (minorExponent p n hp) a (minorsLp Ω p hp u),
    minorsLp_ae Ω p hp u] with x hx hy
  rw [hx, hy]
  rfl

theorem weak_continuity_step {d m n : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp1 : (n+1 : ℕ) ≤ p.real) (hp2 : (n+1+1 : ℕ) < p.real)
    {u : ℕ → W1p Ω m p} {v : W1p Ω m p}
    (hu : WeaklyConverges u v)
    (hs : Tendsto (fun k => value Ω m p (u k)) atTop (nhds (value Ω m p v)))
    (hw : MinorWeakConvergence n hp1 u v) :
    MinorWeakConvergence (n+1) hp2.le u v := by
  apply (minorWeakConvergence_iff hp2.le u v).mpr
  apply weak_of_test_tendsto Ω (minorExponent p (n+1) hp2.le)
    (by
      dsimp [minorExponent]
      apply (lt_div_iff₀ (by positivity)).mpr
      simpa using hp2)
  · simpa only [← range_comp, Function.comp_def] using
      minorsLp_bounded Ω p hp2.le (weaklyConverges_bounded hu)
  · intro a φ
    simp_rw [minorsLp_test_eq_regular Ω hΩ]
    exact minor_regular_tendsto Ω hΩ p hp1 hp2.le hs hw a φ

/-- Weak continuity of every positive order j<p in its exact exponent p/j. -/
theorem weak_continuity : Expected.WeakContinuity := by
  intro d m Ω hΩ p u v hu hs n
  induction n with
  | zero =>
    intro hp hn
    exact first_order Ω p u v hu
  | succ n ih =>
    intro hp hn
    have hp1 : (n+1 : ℕ) < p.real := by
      have hh : (n+1 : ℕ) < n+1+1 := Nat.lt_succ_self _
      exact (Nat.cast_lt.mpr hh).trans hp
    exact weak_continuity_step Ω hΩ p hp1.le hp hu hs
      (ih hp1 ((Nat.le_succ _).trans hn))


end VariationalNotes.Sobolev.WeakMinors
