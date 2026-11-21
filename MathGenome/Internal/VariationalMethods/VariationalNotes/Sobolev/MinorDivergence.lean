import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.MinorDivergence
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Minors
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.Holder
import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped BigOperators ContDiff ENNReal
namespace VariationalNotes.Sobolev.MinorDivergence
open Minors

/-- An order-one minor is its selected entry, for every increasing selection. -/
theorem minor_one_entry {m d : ℕ} (a : Index m d 1) (Z : Gradient m d) :
    minor a Z = Z (a.1.val 0, a.2.val 0) := by
  exact Matrix.det_fin_one _

@[simp] theorem cofactor_order_one {m d : ℕ} (a : Index m d 1) (l : Fin 1)
    (Z : Gradient m d) : cofactor a l Z = 1 := by
  have hl : l = 0 := Fin.eq_zero l
  rw [hl]
  exact Minors.cofactor_one a Z

theorem smooth_cofactor_one : Expected.SmoothCofactorOne := by
  intro d m a u x
  simp only [Fin.sum_univ_one, cofactor_order_one]
  simp

theorem smooth_minor_one : Expected.SmoothMinorOne := by
  intro d m a u x
  simp only [Fin.sum_univ_one, cofactor_order_one, mul_one, minor_one_entry]
  rfl

/-- Replacing an Lp coordinate representative by the actual pointwise coordinate
preserves its regular distribution and its local integrability. -/
theorem coordinate_regular {ι : Type*} [Fintype ι] {d : ℕ}
    (Ω : Opens (Domain d)) (p : Exponent) (i : ι)
    (v : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    LocallyIntegrableOn (fun x => v x i) Ω volume ∧
    P102.U4.regularDistribution Ω (fun x => v x i) =
      P102.U4.regularDistribution Ω (coordinateLp Ω p i v) := by
  have h := coordinateLp_ae Ω p i v
  have hi := P102.U4.domainLp_locallyIntegrable Ω p.ennreal (coordinateLp Ω p i v)
  have hj := hi.congr h
  exact ⟨hj, (P102.U4.regular_injectivity d ℝ Ω _ _ hj hi).mpr h.symm⟩

/-- No smoothness or boundary regularity is used at order one. -/
theorem sobolev_minor_one : Expected.SobolevMinorOne := by
  intro d m Ω p a u
  have hu := coordinate_regular Ω p (a.1.val 0) (value Ω m p u)
  have hg := coordinate_regular Ω p (a.1.val 0, a.2.val 0) (gradient Ω m p u)
  have hm : minorField a u = fun x => gradient Ω m p u x (a.1.val 0, a.2.val 0) := by
    funext x
    exact minor_one_entry a _
  have hf : ∀ l : Fin 1, fluxField a u l = fun x => value Ω m p u x (a.1.val 0) := by
    intro l
    funext x
    simp [fluxField, cofactor_order_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    exact hg.1
  · intro l
    rw [hf l]
    exact hu.1
  · rw [hm, Fin.sum_univ_one, hf 0, hg.2, hu.2]
    exact (distribution_derivative Ω p u (a.1.val 0) (a.2.val 0)).symm

/-- Determinants are finite polynomials in their entries. -/
theorem contDiffOn_determinant {d k : ℕ} {Ω : Opens (Domain d)}
    (A : Domain d → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A x i j) Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Matrix.det (A x)) Ω := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hA (σ i) i)

/-- Classical gradient entries are smooth on Ω, without conditions outside Ω. -/
theorem classicalGradient_contDiffOn {d m : ℕ} {Ω : Opens (Domain d)}
    {u : Domain d → Vector m} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (classicalGradient u) Ω := by
  apply (contDiffOn_piLp 2).mpr
  intro ij
  have hi := ((contDiffOn_piLp 2).mp hu) ij.1
  exact (hi.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const

/-- The signed cofactor field is smooth, including its empty determinant. -/
theorem cofactor_contDiffOn {d m n : ℕ} {Ω : Opens (Domain d)}
    (a : Index m d (n+1)) (l : Fin (n+1))
    {V : Domain d → Gradient m d} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => cofactor a l (V x)) Ω := by
  unfold cofactor
  apply contDiffOn_const.mul
  apply contDiffOn_determinant
  intro i j
  exact ((contDiffOn_piLp 2).mp hV) (a.1.val i.succ, a.2.val (l.succAbove j))

/-- Once Piola cancellation is proved, the second smooth identity follows
from the ordinary product rule and the accepted first-row expansion. -/
theorem smooth_minor_from_piola
    (hpiola : Expected.SmoothCofactorDivergence) : Expected.SmoothMinorDivergence := by
  intro d m n Ω a u hu x hx
  have huc := ((contDiffOn_piLp 2).mp hu) (a.1.val 0)
  have hdu := (huc.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hdc (l : Fin (n+1)) :=
    ((cofactor_contDiffOn a l (classicalGradient_contDiffOn hu)).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  simp only [fderiv_fun_mul hdu (hdc _), add_apply,
    smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hpiola Ω a u hu x hx, mul_zero, zero_add]
  simpa only [classicalGradient, WithLp.toLp, mul_comm] using
    first_row_expansion a (classicalGradient u x)

/-- Finite Hölder at the endpoint: n+1 factors in L^(n+1) have an L¹ product. -/
theorem integrable_finprod {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} (f : Fin (n+1) → α → ℝ)
    (hf : ∀ i, MemLp (f i) (n+1 : ℝ≥0∞) μ) :
    Integrable (fun x => ∏ i : Fin (n+1), f i x) μ := by
  have hp := MemLp.fun_prod (s := Finset.univ) (fun i _ => hf i)
  have h0 : (n+1 : ℝ≥0∞) ≠ 0 := by positivity
  have ht : (n+1 : ℝ≥0∞) ≠ ⊤ := by finiteness
  have he : (∑ _i : Fin (n+1), (n+1 : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    rw [ENNReal.mul_inv_cancel h0 ht, inv_one]
  rw [he] at hp
  exact memLp_one_iff_integrable.mp hp

/-- On a bounded open set, p≥n+1 suffices for every (n+1)-fold product. -/
theorem integrable_finprod_of_exponent {d n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (f : Fin (n+1) → Domain d → ℝ)
    (hf : ∀ i, MemLp (f i) p.ennreal (domainMeasure Ω)) :
    Integrable (fun x => ∏ i : Fin (n+1), f i x) (domainMeasure Ω) := by
  let : IsFiniteMeasure (domainMeasure Ω) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hΩ.measure_lt_top⟩
  have hle : (n+1 : ℝ≥0∞) ≤ p.ennreal := by
    have hh := ENNReal.ofReal_le_ofReal hp
    simpa only [Exponent.ennreal, Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add
      (by positivity : (0:ℝ) ≤ n) (by positivity : (0:ℝ) ≤ 1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh
  exact integrable_finprod f (fun i => (hf i).mono_exponent hle)

/-- Coordinate integrability is transferred to the actual vector representative. -/
theorem coordinate_memLp {ι : Type*} [Fintype ι] {d : ℕ}
    (Ω : Opens (Domain d)) (p : Exponent) (i : ι)
    (v : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    MemLp (fun x => v x i) p.ennreal (domainMeasure Ω) :=
  (Lp.memLp (coordinateLp Ω p i v)).ae_eq (coordinateLp_ae Ω p i v)

/-- Every selected minor is globally integrable, also at p=j. -/
theorem minorField_integrable {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (u : W1p Ω m p) :
    Integrable (minorField a u) (domainMeasure Ω) := by
  classical
  change Integrable (fun x => minorField a u x) (domainMeasure Ω)
  simp only [minorField, minor, Matrix.det_apply']
  apply integrable_finsetSum
  intro σ _
  apply Integrable.const_mul
  apply integrable_finprod_of_exponent hΩ p hp
  intro i
  exact coordinate_memLp Ω p (a.1.val (σ i), a.2.val i) (gradient Ω m p u)

/-- Multiplying the cofactor by a value adds exactly one Lp factor. -/
theorem fluxField_integrable {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (u : W1p Ω m p)
    (l : Fin (n+1)) : Integrable (fluxField a u l) (domainMeasure Ω) := by
  classical
  change Integrable (fun x => fluxField a u l x) (domainMeasure Ω)
  simp only [fluxField, cofactor, Matrix.det_apply', Finset.mul_sum]
  apply integrable_finsetSum
  intro σ _
  let f : Fin (n+1) → Domain d → ℝ := Fin.cases
    (fun x => value Ω m p u x (a.1.val 0))
    (fun i x => gradient Ω m p u x (a.1.val (σ i).succ, a.2.val (l.succAbove i)))
  have hf : ∀ i, MemLp (f i) p.ennreal (domainMeasure Ω) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact coordinate_memLp Ω p (a.1.val 0) (value Ω m p u)
    · exact coordinate_memLp Ω p (a.1.val (σ j).succ, a.2.val (l.succAbove j))
        (gradient Ω m p u)
  have hi := integrable_finprod_of_exponent hΩ p hp f hf
  have hprod : (fun x => ∏ i : Fin (n+1), f i x) =
      (fun x => value Ω m p u x (a.1.val 0) *
        ∏ i : Fin n, gradient Ω m p u x
          (a.1.val (σ i).succ, a.2.val (l.succAbove i))) := by
    funext x
    rw [Fin.prod_univ_succ]
    rfl
  rw [hprod] at hi
  convert hi.const_mul ((-1 : ℝ)^l.val * (↑(Equiv.Perm.sign σ) : ℝ)) using 1
  funext x
  simp only [Matrix.submatrix_apply, submatrix]
  ring

theorem fields_integrable : Expected.FieldsIntegrable := by
  intro d m n Ω hΩ p hp a u
  exact ⟨minorField_integrable hΩ p hp a u, fluxField_integrable hΩ p hp a u⟩

/-- The full local integrability clause needed for regular distributions. -/
theorem fields_locallyIntegrable {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (u : W1p Ω m p) :
    LocallyIntegrableOn (minorField a u) Ω volume ∧
      ∀ l, LocallyIntegrableOn (fluxField a u l) Ω volume := by
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    (minorField_integrable hΩ p hp a u).locallyIntegrable, ?_⟩
  intro l
  exact locallyIntegrableOn_of_locallyIntegrable_restrict
    (fluxField_integrable hΩ p hp a u l).locallyIntegrable

/-- The scalar density theorem transfers through the accepted coordinate
homeomorphism; both representative equalities are established explicitly. -/
theorem smooth_approximation : Expected.SmoothApproximation := by
  intro d m Ω p u
  have hi (i : Fin m) := P102.U4.meyersSerrin_smoothDensity Ω 1 p.ennreal
    (by simp [Exponent.ennreal]) (coordinateEquiv Ω p u i)
  choose f w hw hconv herr using hi
  let g (n : ℕ) (x : Domain d) : Vector m := WithLp.toLp 2 (fun i => f i n x)
  let v (n : ℕ) : W1p Ω m p := (coordinateEquiv Ω p).symm (fun i => w i n)
  have hcoord (n : ℕ) (i : Fin m) : coordinateEquiv Ω p (v n) i = w i n := by
    change ((coordinateEquiv Ω p) ((coordinateEquiv Ω p).symm _)) i = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hvalue (n : ℕ) (i : Fin m) :
      coordinateLp Ω p i (value Ω m p (v n)) = P102.U4.sobolevUnderlying (w i n) := by
    rw [← toCoordinates_value]
    exact congrArg P102.U4.sobolevUnderlying (hcoord n i)
  have hgradient (n : ℕ) (i : Fin m) (j : Fin d) :
      coordinateLp Ω p (i,j) (gradient Ω m p (v n)) =
        P102.U4.sobolevDerivative (w i n) ⟨{j}, by simp⟩ := by
    rw [← toCoordinates_derivative]
    exact congrArg (fun z => P102.U4.sobolevDerivative z ⟨{j}, by simp⟩) (hcoord n i)
  refine ⟨g, v, ?_, ?_⟩
  · intro n
    refine ⟨(contDiffOn_piLp 2).mpr (fun i => (hw i n).1), ?_, ?_⟩
    · have hc (i : Fin m) :
          (fun x => value Ω m p (v n) x i) =ᵐ[domainMeasure Ω] fun x => f i n x := by
        have hrep := (hw i n).2 (P102.U4.zeroSobolevIndex d 1)
        have ha := coordinateLp_ae Ω p i (value Ω m p (v n))
        rw [hvalue n i] at ha
        exact ha.symm.trans (by simpa [P102.U4.sobolevUnderlying,
          P102.U4.zeroSobolevIndex, P102.U4.multiPartial, P102.U4.partialWord] using hrep)
      filter_upwards [eventually_all.mpr hc] with x hx
      exact PiLp.ext (hx ·)
    · have hc (ij : Fin m × Fin d) :
          (fun x => gradient Ω m p (v n) x ij) =ᵐ[domainMeasure Ω]
            fun x => classicalGradient (g n) x ij := by
        have hrep := (hw ij.1 n).2 (⟨{ij.2}, by simp⟩ : P102.U4.SobolevIndex d 1)
        have ha := coordinateLp_ae Ω p ij (gradient Ω m p (v n))
        rw [hgradient n ij.1 ij.2] at ha
        exact ha.symm.trans (by simpa [P102.U4.multiPartial, P102.U4.partialWord,
          classicalGradient, g] using hrep)
      filter_upwards [eventually_all.mpr hc] with x hx
      exact PiLp.ext (hx ·)
  · have hc : Tendsto (fun n i => w i n) atTop (nhds (coordinateEquiv Ω p u)) :=
      tendsto_pi_nhds.mpr hconv
    simpa only [v, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      (coordinateEquiv Ω p).symm.continuous.tendsto (coordinateEquiv Ω p u) |>.comp hc

/-- A cofactor is a determinant with a basis vector in its first row. -/
theorem cofactor_eq_det_updateRow {m d n : ℕ} (a : Index m d (n+1))
    (l : Fin (n+1)) (Z : Gradient m d) :
    cofactor a l Z = Matrix.det ((submatrix a Z).updateRow 0
      (fun k => if k = l then 1 else 0)) := by
  classical
  rw [Matrix.det_succ_row_zero]
  simp only [Matrix.updateRow_apply]
  rw [Finset.sum_eq_single l]
  · simp only [ite_true, mul_one]
    unfold cofactor
    congr 1
  · intro b _ hb
    simp [hb]
  · simp

/-- Permutation expansion with the column assigned to the first row explicit.
Using a basis row avoids any separate sign convention for deleting a column. -/
theorem cofactor_perm_expansion {m d n : ℕ} (a : Index m d (n+1))
    (l : Fin (n+1)) (Z : Gradient m d) :
    cofactor a l Z = ∑ σ : Equiv.Perm (Fin (n+1)),
      if σ 0 = l then (Equiv.Perm.sign σ : ℝ) *
        ∏ r : Fin n, Z (a.1.val r.succ, a.2.val (σ r.succ)) else 0 := by
  classical
  rw [cofactor_eq_det_updateRow, ← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fin.prod_univ_succ]
  simp only [Matrix.transpose_apply, Matrix.updateRow_apply]
  simp only [Fin.succ_ne_zero]
  by_cases h : σ 0 = l <;> simp only [h, ite_true, ite_false, mul_zero, zero_mul, one_mul]
  all_goals rfl

/-- Differentiating a cofactor and summing over its selected directions
reduces the assertion to the derivatives of its permutation monomials. -/
theorem sum_fderiv_cofactor {m d n : ℕ} (a : Index m d (n+1))
    {V : Domain d → Gradient m d} {x : Domain d}
    (hV : ∀ ij, DifferentiableAt ℝ (fun y => V y ij) x)
    (e : Fin (n+1) → Domain d) :
    (∑ l : Fin (n+1), fderiv ℝ (fun y => cofactor a l (V y)) x (e l)) =
      ∑ σ : Equiv.Perm (Fin (n+1)), (Equiv.Perm.sign σ : ℝ) *
        fderiv ℝ (fun y => ∏ r : Fin n,
          V y (a.1.val r.succ, a.2.val (σ r.succ))) x (e (σ 0)) := by
  classical
  let g (σ : Equiv.Perm (Fin (n+1))) (y : Domain d) :=
    ∏ r : Fin n, V y (a.1.val r.succ, a.2.val (σ r.succ))
  have hg (σ) : DifferentiableAt ℝ (g σ) x := by
    dsimp [g]
    exact (HasFDerivAt.finsetProd (u := Finset.univ)
      (g := fun (r : Fin n) (y : Domain d) => V y (a.1.val r.succ, a.2.val (σ r.succ)))
      (fun r _ => (hV _).hasFDerivAt)).differentiableAt
  have hterm (l : Fin (n+1)) (σ : Equiv.Perm (Fin (n+1))) :
      DifferentiableAt ℝ (fun y => if σ 0 = l then
        (Equiv.Perm.sign σ : ℝ) * g σ y else 0) x := by
    split_ifs
    · exact (hg σ).const_mul _
    · exact differentiableAt_const _
  simp_rw [cofactor_perm_expansion]
  change (∑ l, fderiv ℝ (fun y => ∑ σ, if σ 0 = l then
    (Equiv.Perm.sign σ : ℝ) * g σ y else 0) x (e l)) = _
  simp_rw [fderiv_fun_sum (fun σ _ => hterm _ σ), sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_eq_single (σ 0)]
  · simp only [ite_true]
    rw [fderiv_const_mul (hg σ)]
    rfl
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

/-- In a permutation monomial, exchanging columns assigned to row zero and
row r changes the sign and preserves every other factor. -/
theorem permutation_hessian_cancellation {n : ℕ}
    (G : Fin n → Fin (n+1) → ℝ)
    (H : Fin n → Fin (n+1) → Fin (n+1) → ℝ)
    (hH : ∀ r i j, H r i j = H r j i) :
    (∑ σ : Equiv.Perm (Fin (n+1)), ∑ r : Fin n,
      (Equiv.Perm.sign σ : ℝ) *
        ((∏ s ∈ Finset.univ.erase r, G s (σ s.succ)) * H r (σ 0) (σ r.succ))) = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  let τ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 r.succ
  have hτ0 : τ 0 = r.succ := Equiv.swap_apply_left _ _
  have hτr : τ r.succ = 0 := Equiv.swap_apply_right _ _
  have hτs (s : Fin n) (hs : s ≠ r) : τ s.succ = s.succ := by
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero s) (by simpa only [ne_eq, Fin.succ_inj] using hs)
  have hsign (σ : Equiv.Perm (Fin (n+1))) :
      (Equiv.Perm.sign (σ * τ) : ℝ) = -(Equiv.Perm.sign σ : ℝ) := by
    simp only [Equiv.Perm.sign_mul, τ, Equiv.Perm.sign_swap (Fin.succ_ne_zero r).symm]
    simp
  apply Finset.sum_involution (fun σ _ => σ * τ)
  · intro σ _
    have hprod : (∏ s ∈ Finset.univ.erase r, G s ((σ * τ) s.succ)) =
        ∏ s ∈ Finset.univ.erase r, G s (σ s.succ) := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [Equiv.Perm.mul_apply, hτs s (Finset.ne_of_mem_erase hs)]
    rw [hsign, hprod]
    simp only [Equiv.Perm.mul_apply, hτ0, hτr]
    rw [hH r (σ r.succ) (σ 0)]
    ring
  · intro σ _ _ heq
    have ht : τ = 1 := mul_left_cancel (heq.trans (mul_one σ).symm)
    have := congrArg (fun t : Equiv.Perm (Fin (n+1)) => t 0) ht
    rw [hτ0] at this
    exact Fin.succ_ne_zero r this
  · intro σ _
    exact Finset.mem_univ _
  · intro σ _
    exact Equiv.mul_swap_involutive 0 r.succ σ

/-- Mixed derivatives of each component commute on the open domain. -/
theorem classicalGradient_mixed {d m : ℕ} {Ω : Opens (Domain d)}
    {u : Domain d → Vector m} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Domain d} (hx : x ∈ Ω) (b : Fin m) (i j : Fin d) :
    fderiv ℝ (fun y => classicalGradient u y (b,j)) x
      (P102.U4.coordinateVector d i) =
    fderiv ℝ (fun y => classicalGradient u y (b,i)) x
      (P102.U4.coordinateVector d j) := by
  have hc := (((contDiffOn_piLp 2).mp hu) b).contDiffAt (Ω.isOpen.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => u y b)) x :=
    (hc.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hs := hc.isSymmSndFDerivAt (by simp)
  change fderiv ℝ (fun y => (fderiv ℝ (fun z => u z b) y)
      (P102.U4.coordinateVector d j)) x (P102.U4.coordinateVector d i) = _
  change _ = fderiv ℝ (fun y => (fderiv ℝ (fun z => u z b) y)
      (P102.U4.coordinateVector d i)) x (P102.U4.coordinateVector d j)
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_fun_const,
    Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hs _ _

/-- Piola cancellation for every selected minor, including its constant
order-one cofactor, on an arbitrary open set. -/
theorem smooth_cofactor_divergence : Expected.SmoothCofactorDivergence := by
  classical
  intro d m n Ω a u hu x hx
  have hV (ij) : DifferentiableAt ℝ (fun y => classicalGradient u y ij) x :=
    ((((contDiffOn_piLp 2).mp (classicalGradient_contDiffOn hu)) ij).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  rw [sum_fderiv_cofactor a hV]
  have hprod (σ : Equiv.Perm (Fin (n+1))) :=
    fderiv_finsetProd (u := Finset.univ)
      (fun (r : Fin n) _ => hV (a.1.val r.succ, a.2.val (σ r.succ)))
  simp_rw [hprod, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  exact permutation_hessian_cancellation
    (fun r l => classicalGradient u x (a.1.val r.succ, a.2.val l))
    (fun r i j => fderiv ℝ
      (fun y => classicalGradient u y (a.1.val r.succ, a.2.val j)) x
        (P102.U4.coordinateVector d (a.2.val i)))
    (fun r i j => classicalGradient_mixed hu hx _ _ _)

/-- The first-row expansion and product rule give the full smooth minor identity. -/
theorem smooth_minor_divergence : Expected.SmoothMinorDivergence :=
  smooth_minor_from_piola smooth_cofactor_divergence

/-- Finite Hölder, bundled as a continuous product map. Partial reciprocal
sums at most one ensure that every intermediate space is a Banach Lp space. -/
theorem exists_continuous_lpProduct {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (s : Finset ι) (hr : (∑ _i ∈ s, p⁻¹) = r⁻¹) :
    ∃ F : (ι → Lp ℝ p μ) → Lp ℝ r μ,
      Continuous F ∧ ∀ f, (F f : α → ℝ) =ᵐ[μ] fun x => ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
    have hr' : r = ⊤ := by simpa using (congrArg Inv.inv hr).symm
    subst r
    refine ⟨fun _ => (memLp_top_const (μ := μ) (1 : ℝ)).toLp _, continuous_const, ?_⟩
    intro f
    simpa using (memLp_top_const (μ := μ) (1 : ℝ)).coeFn_toLp
  | @insert i s hi ih =>
    have hs : (∑ _i ∈ insert i s, p⁻¹) ≤ 1 := by
      rw [hr]
      simpa only [inv_one] using ENNReal.inv_le_inv.mpr (Fact.out : 1 ≤ r)
    have hs' : (∑ _i ∈ s, p⁻¹) ≤ 1 :=
      (Finset.sum_le_sum_of_subset (Finset.subset_insert i s)).trans hs
    let : Fact (1 ≤ (∑ _i ∈ s, p⁻¹)⁻¹) :=
      ⟨by simpa only [inv_one] using ENNReal.inv_le_inv.mpr hs'⟩
    obtain ⟨F, hF, hrep⟩ := ih (∑ _i ∈ s, p⁻¹)⁻¹ (by rw [inv_inv])
    let : ENNReal.HolderTriple p (∑ _i ∈ s, p⁻¹)⁻¹ r :=
      ⟨by rw [inv_inv, ← hr, Finset.sum_insert hi]⟩
    let B := (ContinuousLinearMap.mul ℝ ℝ).holderL μ p (∑ _i ∈ s, p⁻¹)⁻¹ r
    refine ⟨fun f => B (f i) (F f), B.continuous₂.comp ((continuous_apply i).prodMk hF), ?_⟩
    intro f
    have hb := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := r) (f i) (F f)
    filter_upwards [hb, hrep f] with x hx hy
    simpa only [B, ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.mul_apply',
      hy, Finset.prod_insert hi] using hx

/-- Strong Lp convergence lowers to any smaller exponent at least one on a
finite measure space. This also treats the empty domain. -/
theorem tendsto_toLp_mono_exponent {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hqp : q ≤ p)
    {f : ℕ → Lp ℝ p μ} {g : Lp ℝ p μ} (hf : Tendsto f atTop (nhds g)) :
    Tendsto (fun n => ((Lp.memLp (f n)).mono_exponent hqp).toLp (f n)) atTop
      (nhds (((Lp.memLp g).mono_exponent hqp).toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top hp hqp
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ q))
  have hδ : 0 ≤ 1 / q.toReal - 1 / p.toReal :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (ENNReal.toReal_pos hq0 hqtop)
      (ENNReal.toReal_mono hp hqp))
  have hC : μ Set.univ ^ (1 / q.toReal - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hδ (measure_ne_top μ _)
  have ht := ENNReal.Tendsto.mul_const
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).mp hf) (Or.inr hC)
  simp only [zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp
      ((Lp.memLp (f n)).sub (Lp.memLp g)).aestronglyMeasurable)

/-- Strong convergence of k factors in Lp, p≥k, gives convergence of their
actual pointwise product in L¹. In particular the endpoint p=k is included. -/
theorem tendsto_finprod_L1 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hnp : (n+1 : ℝ≥0∞) ≤ p)
    (f : ℕ → Fin (n+1) → Lp ℝ p μ) (g : Fin (n+1) → Lp ℝ p μ)
    (hf : ∀ i, Tendsto (fun k => f k i) atTop (nhds (g i))) :
    ∃ (v : ℕ → Lp ℝ 1 μ) (w : Lp ℝ 1 μ),
      (∀ k, (v k : α → ℝ) =ᵐ[μ] fun x => ∏ i, f k i x) ∧
      ((w : α → ℝ) =ᵐ[μ] fun x => ∏ i, g i x) ∧ Tendsto v atTop (nhds w) := by
  have : Fact (1 ≤ (n+1 : ℝ≥0∞)) := ⟨le_add_self⟩
  have hn0 : (n+1 : ℝ≥0∞) ≠ 0 := by positivity
  have hnt : (n+1 : ℝ≥0∞) ≠ ⊤ := by finiteness
  have he : (∑ _i : Fin (n+1), (n+1 : ℝ≥0∞)⁻¹) = (1 : ℝ≥0∞)⁻¹ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [ENNReal.mul_inv_cancel hn0 hnt, inv_one]
  obtain ⟨F, hF, hrep⟩ := exists_continuous_lpProduct (μ := μ) (n+1) 1 Finset.univ he
  let f' (k : ℕ) (i : Fin (n+1)) := ((Lp.memLp (f k i)).mono_exponent hnp).toLp (f k i)
  let g' (i : Fin (n+1)) := ((Lp.memLp (g i)).mono_exponent hnp).toLp (g i)
  have ht : Tendsto f' atTop (nhds g') :=
    tendsto_pi_nhds.mpr (fun i => tendsto_toLp_mono_exponent hp hnp (hf i))
  refine ⟨fun k => F (f' k), F g', ?_, ?_, hF.continuousAt.tendsto.comp ht⟩
  · intro k
    refine (hrep (f' k)).trans ?_
    filter_upwards [eventually_all.mpr (fun i =>
      ((Lp.memLp (f k i)).mono_exponent hnp).coeFn_toLp)] with x hx
    exact Finset.prod_congr rfl (fun i _ => hx i)
  · refine (hrep g').trans ?_
    filter_upwards [eventually_all.mpr (fun i =>
      ((Lp.memLp (g i)).mono_exponent hnp).coeFn_toLp)] with x hx
    exact Finset.prod_congr rfl (fun i _ => hx i)

/-- Finite linear combinations preserve the strong product convergence. -/
theorem tendsto_polynomial_L1 {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} [IsFiniteMeasure μ] {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hnp : (n+1 : ℝ≥0∞) ≤ p) (c : ι → ℝ)
    (f : ℕ → ι → Fin (n+1) → Lp ℝ p μ) (g : ι → Fin (n+1) → Lp ℝ p μ)
    (hf : ∀ σ i, Tendsto (fun k => f k σ i) atTop (nhds (g σ i))) :
    ∃ (v : ℕ → Lp ℝ 1 μ) (w : Lp ℝ 1 μ),
      (∀ k, (v k : α → ℝ) =ᵐ[μ] fun x => ∑ σ, c σ * ∏ i, f k σ i x) ∧
      ((w : α → ℝ) =ᵐ[μ] fun x => ∑ σ, c σ * ∏ i, g σ i x) ∧
      Tendsto v atTop (nhds w) := by
  classical
  choose v w hv hw ht using fun σ => tendsto_finprod_L1 hp hnp
    (fun k => f k σ) (g σ) (hf σ)
  refine ⟨fun k => ∑ σ, c σ • v σ k, ∑ σ, c σ • w σ, ?_, ?_, ?_⟩
  · intro k
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun σ => c σ • v σ k),
      eventually_all.mpr (fun σ => (Lp.coeFn_smul (c σ) (v σ k)).trans
        ((hv σ k).const_smul (c σ)))] with x hx hy
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun σ _ => hy σ)
  · filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun σ => c σ • w σ),
      eventually_all.mpr (fun σ => (Lp.coeFn_smul (c σ) (w σ)).trans
        ((hw σ).const_smul (c σ)))] with x hx hy
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun σ _ => hy σ)
  · exact tendsto_finsetSum _ (fun σ _ => (ht σ).const_smul (c σ))


/-- Strong L¹ convergence of representatives implies convergence on each test. -/
theorem tendsto_regular_of_L1 {d : ℕ} {Ω : Opens (Domain d)}
    (f : ℕ → Domain d → ℝ) (g : Domain d → ℝ)
    (hf : ∀ k, LocallyIntegrableOn (f k) Ω volume)
    (hg : LocallyIntegrableOn g Ω volume)
    (v : ℕ → Lp ℝ 1 (domainMeasure Ω)) (w : Lp ℝ 1 (domainMeasure Ω))
    (hv : ∀ k, (v k : Domain d → ℝ) =ᵐ[domainMeasure Ω] f k)
    (hw : (w : Domain d → ℝ) =ᵐ[domainMeasure Ω] g)
    (ht : Tendsto v atTop (nhds w)) (φ : P102.U4.TestSpace ℝ Ω) :
    Tendsto (fun k => P102.U4.regularDistribution Ω (f k) φ) atTop
      (nhds (P102.U4.regularDistribution Ω g φ)) := by
  have heq (k) : P102.U4.regularDistribution Ω (f k) φ = P102.U4.lpTestPairing Ω 1 φ (v k) := by
    rw [← P102.U4.regularLp_pairing]
    exact congrArg (fun T : P102.U4.DistributionSpace ℝ Ω => T φ)
      ((P102.U4.regular_injectivity d ℝ Ω _ _ (hf k)
        (P102.U4.domainLp_locallyIntegrable Ω 1 (v k))).mpr (hv k).symm)
  have heq' : P102.U4.regularDistribution Ω g φ = P102.U4.lpTestPairing Ω 1 φ w := by
    rw [← P102.U4.regularLp_pairing]
    exact congrArg (fun T : P102.U4.DistributionSpace ℝ Ω => T φ)
      ((P102.U4.regular_injectivity d ℝ Ω _ _ hg
        (P102.U4.domainLp_locallyIntegrable Ω 1 w)).mpr hw.symm)
  simp_rw [heq, heq']
  exact (P102.U4.lpTestPairing Ω 1 φ).continuous.continuousAt.tendsto.comp ht

/-- The source exponent bound in the extended-real convention used by Lp. -/
theorem order_le_ennreal (p : Exponent) {n : ℕ} (hp : (n+1 : ℕ) ≤ p.real) :
    (n+1 : ℝ≥0∞) ≤ p.ennreal := by
  have hh := ENNReal.ofReal_le_ofReal hp
  simpa only [Exponent.ennreal, Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add
    (by positivity : (0:ℝ) ≤ n) (by positivity : (0:ℝ) ≤ 1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh

/-- A strongly converging Sobolev sequence has strongly converging minor fields
in L¹, and hence converges against every test function, including at p=j. -/
theorem minorField_regular_tendsto {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1))
    {v : ℕ → W1p Ω m p} {u : W1p Ω m p} (hv : Tendsto v atTop (nhds u))
    (φ : P102.U4.TestSpace ℝ Ω) :
    Tendsto (fun k => P102.U4.regularDistribution Ω (minorField a (v k)) φ) atTop
      (nhds (P102.U4.regularDistribution Ω (minorField a u) φ)) := by
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
  exact tendsto_regular_of_L1 _ _
    (fun k => (fields_locallyIntegrable hΩ p hp a (v k)).1)
    (fields_locallyIntegrable hΩ p hp a u).1 w z
    (fun k => (hw k).trans (hrep (v k))) (hz.trans (hrep u)) hconv φ

/-- The value times cofactor has j factors, so it obeys the same endpoint
strong-convergence statement as the minor itself. -/
theorem fluxField_regular_tendsto {d m n : ℕ} {Ω : Opens (Domain d)}
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (hp : (n+1 : ℕ) ≤ p.real) (a : Index m d (n+1)) (l : Fin (n+1))
    {v : ℕ → W1p Ω m p} {u : W1p Ω m p} (hv : Tendsto v atTop (nhds u))
    (φ : P102.U4.TestSpace ℝ Ω) :
    Tendsto (fun k => P102.U4.regularDistribution Ω (fluxField a (v k) l) φ) atTop
      (nhds (P102.U4.regularDistribution Ω (fluxField a u l) φ)) := by
  classical
  let : IsFiniteMeasure (domainMeasure Ω) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hΩ.measure_lt_top⟩
  let f (z : W1p Ω m p) (σ : Equiv.Perm (Fin n)) :
      Fin (n+1) → Lp ℝ p.ennreal (domainMeasure Ω) := Fin.cases
    (coordinateLp Ω p (a.1.val 0) (value Ω m p z))
    (fun i => coordinateLp Ω p (a.1.val (σ i).succ, a.2.val (l.succAbove i))
      (gradient Ω m p z))
  let c (σ : Equiv.Perm (Fin n)) : ℝ := (-1 : ℝ)^l.val * (Equiv.Perm.sign σ : ℝ)
  have ht (σ : Equiv.Perm (Fin n)) (i : Fin (n+1)) :
      Tendsto (fun k => f (v k) σ i) atTop (nhds (f u σ i)) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ((coordinateLp Ω p _).continuous.comp (value Ω m p).continuous).continuousAt.tendsto.comp hv
    · exact ((coordinateLp Ω p _).continuous.comp (gradient Ω m p).continuous).continuousAt.tendsto.comp hv
  obtain ⟨w, z, hw, hz, hconv⟩ := tendsto_polynomial_L1
    (by simp [Exponent.ennreal] : p.ennreal ≠ ⊤) (order_le_ennreal p hp)
    c (fun k => f (v k)) (f u) ht
  have hrep (z : W1p Ω m p) :
      (fun x => ∑ σ : Equiv.Perm (Fin n), c σ * ∏ i, f z σ i x)
        =ᵐ[domainMeasure Ω] fluxField a z l := by
    have hc (σ : Equiv.Perm (Fin n)) (i : Fin n) :=
      coordinateLp_ae Ω p (a.1.val (σ i).succ, a.2.val (l.succAbove i)) (gradient Ω m p z)
    filter_upwards [coordinateLp_ae Ω p (a.1.val 0) (value Ω m p z),
      eventually_all.mpr (fun σ => eventually_all.mpr (hc σ))] with x hx hxg
    simp only [fluxField, cofactor, Matrix.det_apply', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Fin.prod_univ_succ]
    change c σ * (coordinateLp Ω p (a.1.val 0) (value Ω m p z) x *
      ∏ i : Fin n, coordinateLp Ω p (a.1.val (σ i).succ, a.2.val (l.succAbove i))
        (gradient Ω m p z) x) = _
    rw [hx]
    have hg := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun (i : Fin n) _ => hxg σ i)
    rw [hg]
    simp only [c, Matrix.submatrix_apply, submatrix]
    ring
  exact tendsto_regular_of_L1 _ _
    (fun k => (fields_locallyIntegrable hΩ p hp a (v k)).2 l)
    ((fields_locallyIntegrable hΩ p hp a u).2 l) w z
    (fun k => (hw k).trans (hrep (v k))) (hz.trans (hrep u)) hconv φ

/-- The divergence formula is closed under convergence on each test function. -/
theorem weakIdentity_of_test_limits {d m n : ℕ} {Ω : Opens (Domain d)}
    {p : Exponent} (a : Index m d (n+1)) (u : W1p Ω m p)
    (v : ℕ → W1p Ω m p)
    (hv : ∀ k, WeakIdentity a (v k))
    (hu : LocallyIntegrableOn (minorField a u) Ω volume)
    (hfu : ∀ l, LocallyIntegrableOn (fluxField a u l) Ω volume)
    (hm : ∀ φ : P102.U4.TestSpace ℝ Ω,
      Tendsto (fun k => P102.U4.regularDistribution Ω (minorField a (v k)) φ)
        atTop (nhds (P102.U4.regularDistribution Ω (minorField a u) φ)))
    (hf : ∀ l (φ : P102.U4.TestSpace ℝ Ω),
      Tendsto (fun k => P102.U4.regularDistribution Ω (fluxField a (v k) l) φ)
        atTop (nhds (P102.U4.regularDistribution Ω (fluxField a u l) φ))) :
    WeakIdentity a u := by
  refine ⟨hu, hfu, ?_⟩
  ext φ
  simp only [sum_apply, P102.U4.distributionPartial_singleton_apply]
  have hseq (k) :
      P102.U4.regularDistribution Ω (minorField a (v k)) φ =
        ∑ l : Fin (n+1),
          -P102.U4.regularDistribution Ω (fluxField a (v k) l)
            (P102.U4.testPartialWord Ω [a.2.val l] φ) := by
    have h := congrArg (fun T : P102.U4.DistributionSpace ℝ Ω => T φ) (hv k).2.2
    simpa only [sum_apply, P102.U4.distributionPartial_singleton_apply] using h
  have ht := tendsto_finsetSum Finset.univ (fun l _ =>
    (hf l (P102.U4.testPartialWord Ω [a.2.val l] φ)).neg)
  exact tendsto_nhds_unique (hm φ) (by simpa only [hseq] using ht)

/-- A smooth map satisfies the minor identity for every Sobolev representative
of its value and classical gradient. No boundary regularity is involved. -/
theorem smooth_weak_identity_of_representatives
    (hformula : Expected.SmoothMinorDivergence)
    {d m n : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (a : Index m d (n+1)) {u : Domain d → Vector m} (v : W1p Ω m p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (hv : (value Ω m p v : Domain d → Vector m) =ᵐ[domainMeasure Ω] u)
    (hg : (gradient Ω m p v : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
      classicalGradient u) : WeakIdentity a v := by
  classical
  let F (l : Fin (n+1)) (x : Domain d) :=
    u x (a.1.val 0) * cofactor a l (classicalGradient u x)
  let D (l : Fin (n+1)) (x : Domain d) :=
    fderiv ℝ (F l) x (P102.U4.coordinateVector d (a.2.val l))
  have hF (l : Fin (n+1)) : ContDiffOn ℝ (⊤ : ℕ∞) (F l) Ω :=
    (((contDiffOn_piLp 2).mp hu) (a.1.val 0)).mul
      (cofactor_contDiffOn a l (classicalGradient_contDiffOn hu))
  have hD (l : Fin (n+1)) : ContDiffOn ℝ (⊤ : ℕ∞) (D l) Ω :=
    ((hF l).fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const
  have hDL (l : Fin (n+1)) : LocallyIntegrableOn (D l) Ω volume :=
    (hD l).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hFL (l : Fin (n+1)) : LocallyIntegrableOn (F l) Ω volume :=
    (hF l).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hminor : LocallyIntegrableOn (fun x => minor a (classicalGradient u x)) Ω volume := by
    have hs : ContinuousOn (fun x => ∑ l, D l x) Ω :=
      continuousOn_finsetSum _ (fun l _ => (hD l).continuousOn)
    apply (hs.locallyIntegrableOn Ω.isOpen.measurableSet).congr
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    exact (hformula Ω a u hu x hx).symm
  have hvm : minorField a v =ᵐ[domainMeasure Ω] fun x => minor a (classicalGradient u x) := by
    filter_upwards [hg] with x hx
    simp only [minorField, hx]
  have hvF (l : Fin (n+1)) : fluxField a v l =ᵐ[domainMeasure Ω] F l := by
    filter_upwards [hv, hg] with x hx hy
    simp only [fluxField, hx, hy, F]
  refine ⟨hminor.congr hvm.symm, fun l => (hFL l).congr (hvF l).symm, ?_⟩
  rw [(P102.U4.regular_injectivity d ℝ Ω _ _ (hminor.congr hvm.symm) hminor).mpr hvm]
  have hflux (l : Fin (n+1)) :
      P102.U4.regularDistribution Ω (fluxField a v l) = P102.U4.regularDistribution Ω (F l) :=
    (P102.U4.regular_injectivity d ℝ Ω _ _ ((hFL l).congr (hvF l).symm) (hFL l)).mpr (hvF l)
  simp_rw [hflux]
  have hderiv (l : Fin (n+1)) :
      P102.U4.distributionPartial {a.2.val l} (P102.U4.regularDistribution Ω (F l)) =
        P102.U4.regularDistribution Ω (D l) := by
    have h := P102.U4.derivative_classicalCompatibility d ℝ Ω {a.2.val l} (F l)
      ((hF l).of_le (by simp))
    simpa [P102.U4.multiPartial, P102.U4.partialWord, D] using h
  simp_rw [hderiv]
  ext φ
  simp only [sum_apply]
  rw [P102.U4.regular_pairing d ℝ Ω _ hminor]
  simp_rw [P102.U4.regular_pairing d ℝ Ω _ (hDL _)]
  calc
    (∫ x in Ω, minor a (classicalGradient u x) * φ x) =
        ∫ x in Ω, (∑ l, D l x) * φ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [hformula Ω a u hu x hx]
    _ = ∑ l, ∫ x in Ω, D l x * φ x := by
      simp_rw [Finset.sum_mul]
      apply integral_finsetSum
      intro l _
      have hi := φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hDL l)
      exact (hi.integrableOn).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The minor divergence formula for every W^{1,p} map with p≥j, including
p=j, on the chapter's arbitrary bounded open domain. -/
theorem sobolev_minor_divergence : Expected.SobolevMinorDivergence := by
  intro d m n Ω hΩ p hp a u
  obtain ⟨f, v, hf, hv⟩ := smooth_approximation Ω p u
  apply weakIdentity_of_test_limits a u v
    (fun k => smooth_weak_identity_of_representatives smooth_minor_divergence
      a (v k) (hf k).1 (hf k).2.1 (hf k).2.2)
    (fields_locallyIntegrable hΩ p hp a u).1
    (fields_locallyIntegrable hΩ p hp a u).2
  · exact fun φ => minorField_regular_tendsto hΩ p hp a hv φ
  · exact fun l φ => fluxField_regular_tendsto hΩ p hp a l hv φ

end VariationalNotes.Sobolev.MinorDivergence
