import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.TaylorArithmetic
import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorPeano
import MathGenome.Internal.MultivariableAnalysis.D04.C03.PolynomialUniqueness
import MathGenome.Internal.MultivariableAnalysis.D04.C02.CrCalculus
import MathGenome.Internal.MultivariableAnalysis.D04.C02.BilinearRules
import MathGenome.Internal.MultivariableAnalysis.D04.C02.QuotientRule
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Filter Topology Asymptotics
open scoped BigOperators ContDiff
namespace D04
namespace TaylorArithmetic
open private mvPolynomial_zero_of_isLittleO from MathGenome.Internal.MultivariableAnalysis.D04.C03.PolynomialUniqueness
section Addition
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The pointwise differentiability predicate is closed under addition; no
continuity assumption on the highest derivative is used. -/
theorem timesDifferentiableAt_add_and_differential (k : ℕ) (U : Set X)
    (f g : X → Y) (a : X)
    (hf : TimesDifferentiableAt k U f a) (hg : TimesDifferentiableAt k U g a) :
    TimesDifferentiableAt k U (fun x => f x + g x) a ∧
    higherDifferential k (fun x => f x + g x) a =
      higherDifferential k f a + higherDifferential k g a := by
  induction k generalizing a with
  | zero =>
    refine ⟨hf, ?_⟩
    ext v
    rfl
  | succ k ih =>
    obtain ⟨V, hV, haV, hVU, hfV, hdf⟩ := hf
    obtain ⟨W, hW, haW, hWU, hgW, hdg⟩ := hg
    have he (x : X) (hx : x ∈ V ∩ W) := (ih x (hfV x hx.1) (hgW x hx.2)).2
    have hevent : higherDifferential k (fun x => f x + g x) =ᶠ[𝓝 a]
        (fun x => higherDifferential k f x + higherDifferential k g x) :=
      eventuallyEq_of_mem ((hV.inter hW).mem_nhds ⟨haV, haW⟩) he
    have hdf' := (totalDifferentiableAt_iff_differentiableAt V _ a hV haV).mp hdf
    have hdg' := (totalDifferentiableAt_iff_differentiableAt W _ a hW haW).mp hdg
    have hd := (hdf'.hasFDerivAt.add hdg'.hasFDerivAt).congr_of_eventuallyEq hevent
    refine ⟨⟨V ∩ W, hV.inter hW, ⟨haV, haW⟩,
      fun x hx => hVU hx.1, fun x hx => (ih x (hfV x hx.1) (hgW x hx.2)).1, ?_⟩, ?_⟩
    · exact (totalDifferentiableAt_iff_differentiableAt (V ∩ W) _ a
        (hV.inter hW) ⟨haV, haW⟩).mpr hd.differentiableAt
    · simp only [higherDifferential_succ]
      change differentialSuccEquiv X Y k (fderiv ℝ _ a) = _
      rw [hd.fderiv]
      exact (differentialSuccEquiv X Y k).map_add _ _

theorem taylorPolynomial_add (k : ℕ) (U : Set X) (f g : X → Y) (a h : X)
    (hf : TimesDifferentiableAt k U f a) (hg : TimesDifferentiableAt k U g a) :
    taylorPolynomial k (fun x => f x + g x) a h =
      taylorPolynomial k f a h + taylorPolynomial k g a h := by
  change (∑ j ∈ Finset.range (k+1), _) =
    (∑ j ∈ Finset.range (k+1), _) + (∑ j ∈ Finset.range (k+1), _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he := (timesDifferentiableAt_add_and_differential j U f g a
    (timesDifferentiableAt_of_le hjk U f a hf)
    (timesDifferentiableAt_of_le hjk U g a hg)).2
  change ((j.factorial : ℝ)⁻¹) •
    (higherDifferential j (fun x => f x + g x) a) (fun _ => h) =
    ((j.factorial : ℝ)⁻¹) • (higherDifferential j f a) (fun _ => h) +
    ((j.factorial : ℝ)⁻¹) • (higherDifferential j g a) (fun _ => h)
  rw [he]
  exact smul_add _ _ _

end Addition

open Specs.D04.C03.TaylorArithmetic.Model

section PolynomialAlgebra
variable {n : ℕ}

@[simp] theorem truncate_coeff (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (α : Fin n →₀ ℕ) : (truncate k p).coeff α =
    if α.sum (fun _ r => r) ≤ k then p.coeff α else 0 := rfl

theorem truncate_degree (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (truncate k p).totalDegree ≤ k := by
  classical
  apply Finset.sup_le
  intro α hα
  change α ∈ (p.coeff.filter (fun α => α.sum (fun _ r => r) ≤ k)).support at hα
  exact (Finset.mem_filter.mp hα).2

@[simp] theorem truncate_add (k : ℕ) (p q : MvPolynomial (Fin n) ℝ) :
    truncate k (p+q) = truncate k p + truncate k q := by
  classical
  ext α
  simp only [truncate_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  split <;> simp

@[simp] theorem truncate_idempotent (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    truncate k (truncate k p) = truncate k p := by
  ext α
  simp only [truncate_coeff]
  split <;> rfl

theorem truncate_eq_self (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ k) : truncate k p = p := by
  classical
  ext α
  rw [truncate_coeff]
  split
  · rfl
  · next hα =>
    exact (MvPolynomial.notMem_support_iff.mp (fun hm => hα
      ((MvPolynomial.le_totalDegree hm).trans hp))).symm

@[simp] theorem truncate_C (k : ℕ) (c : ℝ) :
    truncate (n := n) k (MvPolynomial.C c) = MvPolynomial.C c :=
  truncate_eq_self k _ (by simp)

@[simp] theorem truncate_dimension_zero (k : ℕ) (p : MvPolynomial (Fin 0) ℝ) :
    truncate k p = p := by
  classical
  ext α
  have hα : α = 0 := Subsingleton.elim _ _
  simp [truncate_coeff, hα]

end PolynomialAlgebra

section CoordinateBridge

 theorem taylorCoordinates_eval {n m : ℕ} (k : ℕ) (f : E n → E m) (a h : E n) :
    coordinatePolynomialEval (taylorCoordinates k f a) h = taylorPolynomial k f a h := by
  classical
  ext i
  change MvPolynomial.eval (fun j => h j) (taylorCoordinates k f a i) = _
  simp only [taylorCoordinates, multilinearPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  change _ = (∑ r ∈ Finset.range (k+1),
    ((r.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential r f a) h) i
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  have he := congrArg (fun v : E m => v i)
    (differential_expansion (higherDifferential r f a) (fun _ => h))
  simpa [differentialCoefficients_apply, WithLp.ofLp_sum, PiLp.smul_apply,
    differentialDiagonal, Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal, higherDifferential, standardBasis,
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, smul_eq_mul, mul_comm] using he.symm

 theorem scalarTaylorCoordinates_eval {n : ℕ} (k : ℕ) (f : E n → ℝ) (a h : E n) :
    MvPolynomial.eval (fun j => h j) (scalarTaylorCoordinates k f a) =
      taylorPolynomial k f a h := by
  classical
  simp only [scalarTaylorCoordinates, multilinearPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  change _ = ∑ r ∈ Finset.range (k+1),
    ((r.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential r f a) h
  apply Finset.sum_congr rfl
  intro r hr
  simp only [smul_eq_mul]
  congr 1
  simpa [differentialCoefficients_apply, differentialDiagonal, Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal, higherDifferential,
    standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
    smul_eq_mul, mul_comm] using
    (differential_expansion (higherDifferential r f a) (fun _ => h)).symm

end CoordinateBridge

section PolynomialEstimates
variable {n : ℕ}

theorem monomial_eval_bound (α : Fin n →₀ ℕ) (c : ℝ) (h : E n) :
    ‖MvPolynomial.eval (fun j => h j) (MvPolynomial.monomial α c)‖ ≤
      ‖c‖ * ‖h‖^(α.sum (fun _ r => r)) := by
  classical
  rw [MvPolynomial.eval_monomial, norm_mul, Finsupp.prod, norm_prod]
  apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i hi
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le h i) _

theorem polynomial_eval_isLittleO (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ α ∈ p.support, k < α.sum (fun _ r => r)) :
    (fun h : E n => MvPolynomial.eval (fun j => h j) p) =o[𝓝 0] (fun h => ‖h‖^k) := by
  classical
  have he : (fun h : E n => MvPolynomial.eval (fun j => h j) p) =
      fun h => ∑ α ∈ p.support, MvPolynomial.eval (fun j => h j) (MvPolynomial.monomial α (p.coeff α)) := by
    funext h
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [he]
  apply Asymptotics.IsLittleO.fun_sum
  intro α hα
  have hb : (fun h : E n => MvPolynomial.eval (fun j => h j) (MvPolynomial.monomial α (p.coeff α)))
      =O[𝓝 0] (fun h => ‖h‖^(α.sum (fun _ r => r))) := by
    apply Asymptotics.IsBigO.of_bound ‖p.coeff α‖
    exact Filter.Eventually.of_forall fun h => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg h) _)] using
        monomial_eval_bound α (p.coeff α) h
  exact hb.trans_isLittleO (isLittleO_norm_pow_norm_pow (hp α hα))

theorem truncate_remainder (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (fun h : E n => MvPolynomial.eval (fun j => h j) p -
      MvPolynomial.eval (fun j => h j) (truncate k p)) =o[𝓝 0] (fun h => ‖h‖^k) := by
  have hh := polynomial_eval_isLittleO k (p-truncate k p) ?_
  · simpa only [map_sub] using hh
  · intro α hα
    by_contra hn
    have hd : α.sum (fun _ r => r) ≤ k := by omega
    have hz : (p-truncate k p).coeff α = 0 := by
      simp [truncate_coeff, hd]
    exact MvPolynomial.mem_support_iff.mp hα hz

end PolynomialEstimates

section PolynomialAnalysis

 theorem polynomial_eval_contDiff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (r : ℕ∞ω) :
    ContDiff ℝ r (fun h : E n => MvPolynomial.eval (fun j => h j) p) := by
  classical
  conv => arg 3; ext h; rw [p.as_sum, map_sum]
  apply ContDiff.sum
  intro α hα
  simp only [MvPolynomial.eval_monomial, Finsupp.prod]
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.pow _

 theorem vector_isLittleO_iff {A : Type} {n : ℕ} {l : Filter A}
    {f : A → E n} {g : A → ℝ} :
    f =o[l] g ↔ ∀ i, (fun x => f x i) =o[l] g := by
  let e : E n ≃L[ℝ] (Fin n → ℝ) := (coordinates n).toContinuousLinearEquiv
  constructor
  · intro hf i
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).isBigO_comp f l).trans_isLittleO hf
  · intro hf
    have he : (fun x => e (f x)) =o[l] g := isLittleO_pi.mpr hf
    exact (e.isBigO_comp_rev f l).trans_isLittleO he

 theorem truncate_vector_remainder {n m : ℕ} (k : ℕ) (p : CoordinatePolynomial n m) :
    (fun h : E n => coordinatePolynomialEval p h -
      coordinatePolynomialEval (fun i => truncate k (p i)) h) =o[𝓝 0] (fun h => ‖h‖^k) := by
  apply vector_isLittleO_iff.mpr
  intro i
  exact truncate_remainder k (p i)

 theorem truncate_eval_zero {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval (fun _ => 0) (truncate k p) = MvPolynomial.eval (fun _ => 0) p := by
  rw [MvPolynomial.eval_zero']
  change (truncate k p).coeff 0 = p.coeff 0
  rw [truncate_coeff]
  simp

 theorem polynomialEvaluation_unique {n m : ℕ} (k : ℕ) (f : E n → E m)
    (a : E n) (p : CoordinatePolynomial n m)
    (hp : ∀ i, (p i).totalDegree ≤ k)
    (hzero : coordinatePolynomialEval p 0 = f a)
    (hf : taylorRemainder k f a =o[𝓝 0] (fun h => ‖h‖^k))
    (he : (fun h => f (a+h) - coordinatePolynomialEval p h) =o[𝓝 0] (fun h => ‖h‖^k)) :
    taylorPolynomial k f a = coordinatePolynomialEval p := by
  by_cases hn : n = 0
  · subst n
    funext h
    rw [taylorPolynomial_dimension_zero]
    have hh : h = 0 := Subsingleton.elim _ _
    simpa only [hh] using hzero.symm
  · apply polynomialFunction_eq_of_sub_isLittleO (by omega) k
      (taylorPolynomial k f a) (coordinatePolynomialEval p)
      (polynomialFunctionDegreeLE_taylorPolynomial k f a) ⟨p, hp, rfl⟩
    have hh := he.sub hf
    apply (hh.mono nhdsWithin_le_nhds).congr_left
    intro h
    change (f (a+h)-coordinatePolynomialEval p h) -
      (f (a+h)-taylorPolynomial k f a h) = _
    abel

end PolynomialAnalysis

section Composition

 theorem compositionCoordinates_eval {n m p : ℕ} (P : CoordinatePolynomial m p)
    (Q : CoordinatePolynomial n m) (b : E m) (h : E n) :
    coordinatePolynomialEval (compositionCoordinates P Q b) h =
      coordinatePolynomialEval P (coordinatePolynomialEval Q h - b) := by
  ext i
  change MvPolynomial.eval (fun j => h j)
    (MvPolynomial.eval₂ MvPolynomial.C (fun j => Q j - MvPolynomial.C (b j)) (P i)) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun F : Fin m → ℝ => MvPolynomial.eval F (P i))
  funext j
  simp [coordinatePolynomialEval_apply, Function.comp_def]

 theorem coordinatePolynomialEval_contDiff {n m : ℕ} (P : CoordinatePolynomial n m)
    (r : ℕ∞ω) : ContDiff ℝ r (coordinatePolynomialEval P) := by
  let e : E m ≃L[ℝ] (Fin m → ℝ) := (coordinates m).toContinuousLinearEquiv
  have hh : ContDiff ℝ r (fun h : E n => fun i => MvPolynomial.eval (fun j => h j) (P i)) :=
    contDiff_pi.mpr fun i => polynomial_eval_contDiff (P i) r
  exact e.symm.contDiff.comp hh

 theorem taylorPolynomial_comp_zero {X Y Z : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : X → Y) (g : Y → Z) (a h : X) :
    taylorPolynomial 0 (g ∘ f) a h = g (f a) := taylorPolynomial_zero _ _ _

 theorem taylorPolynomial_comp {n m p : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (U : Set (E n)) (V : Set (E m)) (f : E n → E m) (g : E m → E p) (a h : E n)
    (hU : IsOpen U) (hV : IsOpen V) (ha : a ∈ U) (hmap : MapsTo f U V)
    (hf : CrOn k U f) (hg : CrOn k V g) :
    taylorPolynomial k (g ∘ f) a h = coordinatePolynomialEval (fun i => truncate k
      (compositionCoordinates (taylorCoordinates k g (f a)) (taylorCoordinates k f a) (f a) i)) h := by
  have htf := crOn_timesDifferentiableAt k U f hU hf a ha
  have htg := crOn_timesDifferentiableAt k V g hV hg (f a) (hmap ha)
  have htc := crOn_timesDifferentiableAt k U (g ∘ f) hU
    (crOn_comp k U V f g hU hV hmap hf hg) a ha
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let u : E n → E m := fun z => f (a+z) - f a
  let v : E n → E m := fun z => taylorPolynomial (j+1) f a z - f a
  let P := taylorCoordinates (j+1) g (f a)
  let Q := taylorCoordinates (j+1) f a
  let R := compositionCoordinates P Q (f a)
  have hR (z : E n) : coordinatePolynomialEval R z =
      coordinatePolynomialEval P (v z) := by
    simpa only [P, Q, v, taylorCoordinates_eval] using
      compositionCoordinates_eval P Q (f a) z
  have hdf : DifferentiableAt ℝ f a :=
    (totalDifferentiableAt_iff_differentiableAt U f a hU ha).mp
      ((timesDifferentiableAt_one U f a).mp
        (timesDifferentiableAt_of_le (by omega) U f a htf))
  have ht : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 a) := by
    have ht' : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 (a+0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa only [add_zero] using ht'
  have hu : Tendsto u (𝓝 0) (𝓝 0) := by
    simpa [u] using (hdf.continuousAt.tendsto.comp ht).sub
      (tendsto_const_nhds : Tendsto (fun _ : E n => f a) (𝓝 0) (𝓝 (f a)))
  have hv : Tendsto v (𝓝 0) (𝓝 0) := by
    have hc := (coordinatePolynomialEval_contDiff Q 1).continuous.continuousAt (x := (0 : E n))
    have hc' : ContinuousAt (taylorPolynomial (j+1) f a) 0 := by
      have hQ : coordinatePolynomialEval Q = taylorPolynomial (j+1) f a :=
        funext (taylorCoordinates_eval (j+1) f a)
      rw [hQ] at hc
      exact hc
    simpa [v, taylorPolynomial_zero_increment] using hc'.tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : E n => f a) (𝓝 0) (𝓝 (f a)))
  have hub : u =O[𝓝 0] (fun z : E n => ‖z‖) := by
    simpa only [u, Function.comp_def, add_sub_cancel_left] using
      (hdf.isBigO_sub.comp_tendsto ht).norm_right
  have hout := (taylorPeano_succ j V g (f a) htg).comp_tendsto hu
  have hout' : (fun z => g (f (a+z)) - coordinatePolynomialEval P (u z))
      =o[𝓝 0] (fun z : E n => ‖z‖^(j+1)) := by
    have hh := hout.trans_isBigO (hub.norm_left.pow (j+1))
    simpa [u, P, taylorRemainder, Specs.D04.C03.HigherInterfaces.Model.taylorRemainder,
      Function.comp_def, taylorCoordinates_eval] using hh
  have hpoly := ((coordinatePolynomialEval_contDiff P 1).contDiffAt (x := (0 : E m))).hasStrictFDerivAt (by simp)
  have hb := hpoly.isBigO_sub.comp_tendsto (hu.prodMk_nhds hv)
  have herr : (fun z => u z - v z) =o[𝓝 0] (fun z : E n => ‖z‖^(j+1)) := by
    convert taylorPeano_succ j U f a htf using 1
    funext z
    change (f (a+z)-f a)-(taylorPolynomial (j+1) f a z-f a) =
      f (a+z)-taylorPolynomial (j+1) f a z
    abel
  have hreplace := hb.trans_isLittleO herr
  have hraw : (fun z => g (f (a+z))-coordinatePolynomialEval R z)
      =o[𝓝 0] (fun z : E n => ‖z‖^(j+1)) := by
    convert hout'.add hreplace using 1
    funext z
    change _ = (g (f (a+z))-coordinatePolynomialEval P (u z)) +
      (coordinatePolynomialEval P (u z)-coordinatePolynomialEval P (v z))
    rw [hR]
    abel
  have htrunc := truncate_vector_remainder (j+1) R
  have he : (fun z => (g ∘ f) (a+z)-coordinatePolynomialEval (fun i => truncate (j+1) (R i)) z)
      =o[𝓝 0] (fun z : E n => ‖z‖^(j+1)) := by
    convert hraw.add htrunc using 1
    funext z
    simp only [Function.comp_apply]
    abel
  have hzero : coordinatePolynomialEval (fun i => truncate (j+1) (R i)) 0 = (g ∘ f) a := by
    have hr0 : coordinatePolynomialEval (fun i => truncate (j+1) (R i)) 0 = coordinatePolynomialEval R 0 := by
      ext i
      exact truncate_eval_zero (j+1) (R i)
    rw [hr0, hR]
    simp only [v, taylorPolynomial_zero_increment, sub_self]
    rw [show P = taylorCoordinates (j+1) g (f a) from rfl, taylorCoordinates_eval,
      taylorPolynomial_zero_increment]
    rfl
  exact congrFun (polynomialEvaluation_unique (j+1) (g ∘ f) a _
    (fun i => truncate_degree (j+1) (R i)) hzero
    (taylorPeano_succ j U (g ∘ f) a htc) he) h

end Composition

section PointwiseCalculus
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

 theorem timesDifferentiableAt_congr_germ (k : ℕ) (U : Set X) (f g : X → Y) (a : X)
    (he : f =ᶠ[𝓝 a] g) (hf : TimesDifferentiableAt k U f a) :
    TimesDifferentiableAt k U g a := by
  induction k generalizing a with
  | zero => exact hf
  | succ k ih =>
    obtain ⟨V, hV, haV, hVU, hlow, htop⟩ := hf
    obtain ⟨W, hWmem, hWopen, hWa⟩ := mem_nhds_iff.mp he
    refine ⟨V ∩ W, hV.inter hWopen, ⟨haV, hWa⟩,
      fun x hx => hVU hx.1, ?_, ?_⟩
    · intro x hx
      exact ih x (eventuallyEq_of_mem (hWopen.mem_nhds hx.2) hWmem) (hlow x hx.1)
    · have hd := (totalDifferentiableAt_iff_differentiableAt V _ a hV haV).mp htop
      have hh : higherDifferential k f =ᶠ[𝓝 a] higherDifferential k g := he.iteratedFDeriv ℝ k
      exact (totalDifferentiableAt_iff_differentiableAt (V ∩ W) _ a
        (hV.inter hWopen) ⟨haV, hWa⟩).mpr (hd.congr_of_eventuallyEq hh.symm)

 theorem timesDifferentiableAt_succ_of_fderiv (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hd : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hf : TimesDifferentiableAt k U (fderiv ℝ f) a) : TimesDifferentiableAt (k+1) U f a := by
  induction k generalizing a with
  | zero =>
    have hdom := timesDifferentiableAt_domain 0 U _ a hf
    exact (timesDifferentiableAt_one U f a).mpr
      ((totalDifferentiableAt_iff_differentiableAt U f a hdom.1 hdom.2).mpr hd.self_of_nhds)
  | succ k ih =>
    obtain ⟨V, hV, haV, hVU, hlow, htop⟩ := hf
    obtain ⟨W, hWmem, hWopen, hWa⟩ := mem_nhds_iff.mp hd
    refine ⟨V ∩ W, hV.inter hWopen, ⟨haV, hWa⟩,
      fun x hx => hVU hx.1, ?_, ?_⟩
    · intro x hx
      exact ih x (Filter.mem_of_superset (hWopen.mem_nhds hx.2) hWmem) (hlow x hx.1)
    · have hdiff := (totalDifferentiableAt_iff_differentiableAt V _ a hV haV).mp htop
      let e := continuousMultilinearCurryRightEquiv' ℝ k X Y
      have he : higherDifferential (k+1) f =
          e.symm ∘ higherDifferential k (fderiv ℝ f) := by
        funext x
        exact iteratedFDeriv_succ_eq_comp_right
      apply (totalDifferentiableAt_iff_differentiableAt (V ∩ W) _ a
        (hV.inter hWopen) ⟨haV, hWa⟩).mpr
      change DifferentiableAt ℝ (higherDifferential (k+1) f) a
      rw [he]
      exact e.symm.toContinuousLinearEquiv.differentiableAt.comp a hdiff

end PointwiseCalculus

section BilinearCalculus
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem timesDifferentiableAt_differentiableAt {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (U : Set X) (f : X → Y) (a : X) (hf : TimesDifferentiableAt (k+1) U f a) :
    DifferentiableAt ℝ f a := by
  have hd := timesDifferentiableAt_domain (k+1) U f a hf
  exact (totalDifferentiableAt_iff_differentiableAt U f a hd.1 hd.2).mp
    ((timesDifferentiableAt_one U f a).mp (timesDifferentiableAt_of_le (by omega) U f a hf))

 theorem timesDifferentiableAt_bilinear (k : ℕ)
    {Y Z W : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : Y →L[ℝ] Z →L[ℝ] W) (U : Set X) (f : X → Y) (g : X → Z) (a : X)
    (hf : TimesDifferentiableAt k U f a) (hg : TimesDifferentiableAt k U g a) :
    TimesDifferentiableAt k U (fun x => B (f x) (g x)) a := by
  induction k generalizing Y Z W with
  | zero => exact hf
  | succ k ih =>
    cases k with
    | zero =>
      have hdom := timesDifferentiableAt_domain 1 U f a hf
      have hd := B.hasFDerivAt_of_bilinear
        (timesDifferentiableAt_differentiableAt 0 U f a hf).hasFDerivAt
        (timesDifferentiableAt_differentiableAt 0 U g a hg).hasFDerivAt
      exact (timesDifferentiableAt_one U _ a).mpr
        ((totalDifferentiableAt_iff_differentiableAt U _ a hdom.1 hdom.2).mpr hd.differentiableAt)
    | succ k =>
      have hdf := timesDifferentiableAt_fderiv (k+1) U f a hf
      have hdg := timesDifferentiableAt_fderiv (k+1) U g a hg
      have hfl := timesDifferentiableAt_lower (k+1) U f a hf
      have hgl := timesDifferentiableAt_lower (k+1) U g a hg
      have hR := ih (B.precompR X) f (fderiv ℝ g) hfl hdg
      have hL := ih (B.precompL X) (fderiv ℝ f) g hdf hgl
      have hsum := (timesDifferentiableAt_add_and_differential (k+1) U _ _ a hR hL).1
      obtain ⟨V, hV, haV, _, hfv, _⟩ := hf
      obtain ⟨W', hW, haW, _, hgv, _⟩ := hg
      have hdiff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x := by
        filter_upwards [hV.mem_nhds haV, hW.mem_nhds haW] with x hx hy
        exact ⟨timesDifferentiableAt_differentiableAt k U f x (hfv x hx),
          timesDifferentiableAt_differentiableAt k U g x (hgv x hy)⟩
      have he : (fun x => B.precompR X (f x) (fderiv ℝ g x) +
          B.precompL X (fderiv ℝ f x) (g x)) =ᶠ[𝓝 a]
          fderiv ℝ (fun x => B (f x) (g x)) := by
        filter_upwards [hdiff] with x hx
        exact (B.fderiv_of_bilinear hx.1 hx.2).symm
      apply timesDifferentiableAt_succ_of_fderiv (k+1) U _ a
      · filter_upwards [hdiff] with x hx
        exact (B.hasFDerivAt_of_bilinear hx.1.hasFDerivAt hx.2.hasFDerivAt).differentiableAt
      · exact timesDifferentiableAt_congr_germ (k+1) U _ _ a he hsum

end BilinearCalculus

section BilinearArithmetic

 theorem taylorHypothesis_continuous {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TaylorHypothesis k U f a) : ContinuousAt f a := by
  cases k with
  | zero => exact (by simpa [TaylorHypothesis] using hf : IsOpen U ∧ a ∈ U ∧ ContinuousAt f a).2.2
  | succ k =>
    exact (timesDifferentiableAt_differentiableAt k U f a (by simpa [TaylorHypothesis] using hf)).continuousAt

 theorem taylorHypothesis_peano {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TaylorHypothesis k U f a) :
    taylorRemainder k f a =o[𝓝 0] (fun h => ‖h‖^k) := by
  cases k with
  | zero => exact taylorPeano_zero f a (taylorHypothesis_continuous 0 U f a hf)
  | succ k => exact taylorPeano_succ k U f a (by simpa [TaylorHypothesis] using hf)

 theorem taylorHypothesis_bilinear {X Y Z W : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (k : ℕ) (B : Y →L[ℝ] Z →L[ℝ] W) (U : Set X) (f : X → Y) (g : X → Z) (a : X)
    (hf : TaylorHypothesis k U f a) (hg : TaylorHypothesis k U g a) :
    TaylorHypothesis k U (fun x => B (f x) (g x)) a := by
  cases k with
  | zero =>
    have hf' : IsOpen U ∧ a ∈ U ∧ ContinuousAt f a := by simpa [TaylorHypothesis] using hf
    have hg' := taylorHypothesis_continuous 0 U g a hg
    simp only [TaylorHypothesis, if_pos rfl]
    exact ⟨hf'.1, hf'.2.1, B.isBoundedBilinearMap.continuous.continuousAt.comp
      (hf'.2.2.prodMk hg')⟩
  | succ k =>
    simp only [TaylorHypothesis, Nat.succ_ne_zero, if_false] at *
    exact timesDifferentiableAt_bilinear (k+1) B U f g a hf hg

 theorem bilinear_basis_expansion {m p q : ℕ} (B : E m →ₗ[ℝ] E p →ₗ[ℝ] E q)
    (x : E m) (y : E p) :
    B x y = ∑ j : Fin m, ∑ l : Fin p,
      (x j * y l) • B (standardBasis m j) (standardBasis p l) := by
  have hx : x = ∑ j : Fin m, x j • standardBasis m j := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using ((standardBasis m).sum_repr x).symm
  have hy : y = ∑ l : Fin p, y l • standardBasis p l := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using ((standardBasis p).sum_repr y).symm
  conv_lhs => rw [hx, hy]
  simp only [map_sum, map_smul, smul_smul, Finset.smul_sum,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  simp [mul_comm]

 theorem bilinearCoordinates_eval {n m p q : ℕ} (B : E m →ₗ[ℝ] E p →ₗ[ℝ] E q)
    (P : CoordinatePolynomial n m) (Q : CoordinatePolynomial n p) (h : E n) :
    coordinatePolynomialEval (bilinearCoordinates B P Q) h =
      B (coordinatePolynomialEval P h) (coordinatePolynomialEval Q h) := by
  ext i
  rw [bilinear_basis_expansion]
  simp [bilinearCoordinates, standardBasis,
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, coordinatePolynomialEval_apply, WithLp.ofLp_sum,
    PiLp.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

 theorem taylorPolynomial_bilinear {n m p q : ℕ} (k : ℕ)
    (B : E m →ₗ[ℝ] E p →ₗ[ℝ] E q) (U : Set (E n))
    (f : E n → E m) (g : E n → E p) (a h : E n)
    (hf : TaylorHypothesis k U f a) (hg : TaylorHypothesis k U g a) :
    taylorPolynomial k (fun x => B (f x) (g x)) a h =
      coordinatePolynomialEval (fun i => truncate k
        (bilinearCoordinates B (taylorCoordinates k f a) (taylorCoordinates k g a) i)) h := by
  let P := taylorCoordinates k f a
  let Q := taylorCoordinates k g a
  let R := bilinearCoordinates B P Q
  let C := B.toContinuousBilinearMap
  have ht : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 a) := by
    have hh : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 (a+0)) := tendsto_const_nhds.add tendsto_id
    simpa only [add_zero] using hh
  have hfrem := taylorHypothesis_peano k U f a hf
  have hgrem := taylorHypothesis_peano k U g a hg
  have hgb := ((taylorHypothesis_continuous k U g a hg).tendsto.comp ht).isBigO_one ℝ
  have hpb := ((coordinatePolynomialEval_contDiff P 0).continuous.continuousAt (x := (0 : E n))).tendsto.isBigO_one ℝ
  have h1 := (C.isBoundedBilinearMap.isBigO_comp (g := taylorRemainder k f a)
    (h := fun z => g (a+z))).trans_isLittleO (hfrem.norm_left.mul_isBigO hgb.norm_left)
  have h2 := (C.isBoundedBilinearMap.isBigO_comp (g := coordinatePolynomialEval P)
    (h := taylorRemainder k g a)).trans_isLittleO (hpb.norm_left.mul_isLittleO hgrem.norm_left)
  have hraw : (fun z => B (f (a+z)) (g (a+z)) - coordinatePolynomialEval R z)
      =o[𝓝 0] (fun z : E n => ‖z‖^k) := by
    simp only [mul_one] at h1
    simp only [one_mul] at h2
    have hh := h1.add h2
    apply hh.congr_left
    intro z
    change B (f (a+z)-taylorPolynomial k f a z) (g (a+z)) +
      B (coordinatePolynomialEval P z) (g (a+z)-taylorPolynomial k g a z) = _
    rw [show R = bilinearCoordinates B P Q from rfl, bilinearCoordinates_eval]
    simp only [P, Q, taylorCoordinates_eval, map_sub, LinearMap.sub_apply]
    abel
  have he := hraw.add (truncate_vector_remainder k R)
  have he' : (fun z => B (f (a+z)) (g (a+z)) -
      coordinatePolynomialEval (fun i => truncate k (R i)) z) =o[𝓝 0] (fun z : E n => ‖z‖^k) := by
    apply he.congr_left
    intro z
    abel
  have hz : coordinatePolynomialEval (fun i => truncate k (R i)) 0 = B (f a) (g a) := by
    have hz' : coordinatePolynomialEval (fun i => truncate k (R i)) 0 = coordinatePolynomialEval R 0 := by
      ext i
      exact truncate_eval_zero k (R i)
    rw [hz', show R = bilinearCoordinates B P Q from rfl, bilinearCoordinates_eval]
    simp only [P, Q, taylorCoordinates_eval, taylorPolynomial_zero_increment]
  exact congrFun (polynomialEvaluation_unique k (fun x => B (f x) (g x)) a _
    (fun i => truncate_degree k (R i)) hz
    (taylorHypothesis_peano k U _ a (taylorHypothesis_bilinear k C U f g a hf hg)) he') h

end BilinearArithmetic

section ReciprocalCalculus
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

 theorem timesDifferentiableAt_reciprocal (k : ℕ) (U : Set X) (q : X → ℝ) (a : X)
    (hq : TimesDifferentiableAt k U q a) (hc : q a ≠ 0) :
    TimesDifferentiableAt k U (fun x => (q x)⁻¹) a := by
  induction k with
  | zero => exact hq
  | succ k ih =>
    have hdq := timesDifferentiableAt_differentiableAt k U q a hq
    have hdom := timesDifferentiableAt_domain (k+1) U q a hq
    cases k with
    | zero =>
      exact (timesDifferentiableAt_one U _ a).mpr
        ((totalDifferentiableAt_iff_differentiableAt U _ a hdom.1 hdom.2).mpr
          (hdq.inv hc))
    | succ k =>
      have hi := ih (timesDifferentiableAt_lower (k+1) U q a hq)
      have hs := timesDifferentiableAt_bilinear (k+1)
        (ContinuousLinearMap.mul ℝ ℝ) U (fun x => (q x)⁻¹) (fun x => (q x)⁻¹) a hi hi
      let S : ℝ →L[ℝ] (X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
        (ContinuousLinearMap.lsmul ℝ ℝ).comp (ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ))
      have hexp := timesDifferentiableAt_bilinear (k+1) S U
        (fun x => (q x)⁻¹ * (q x)⁻¹) (fderiv ℝ q) a hs
        (timesDifferentiableAt_fderiv (k+1) U q a hq)
      have hne : ∀ᶠ x in 𝓝 a, q x ≠ 0 := hdq.continuousAt.eventually_ne hc
      obtain ⟨V, hV, haV, _, hlow, _⟩ := hq
      have hdiff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ q x := by
        filter_upwards [hV.mem_nhds haV] with x hx
        exact timesDifferentiableAt_differentiableAt k U q x (hlow x hx)
      have he : (fun x => S ((q x)⁻¹ * (q x)⁻¹) (fderiv ℝ q x)) =ᶠ[𝓝 a]
          fderiv ℝ (fun x => (q x)⁻¹) := by
        filter_upwards [hdiff, hne] with x hx hnx
        have hh := ((hasFDerivAt_inv hnx).comp x hx.hasFDerivAt).fderiv
        change fderiv ℝ (fun z => (q z)⁻¹) x = _ at hh
        rw [hh]
        ext v
        simp only [S, ContinuousLinearMap.lsmul_apply, smul_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
        simp [pow_two, mul_assoc, mul_comm]
      apply timesDifferentiableAt_succ_of_fderiv (k+1) U _ a
      · filter_upwards [hdiff, hne] with x hx hnx
        exact hx.inv hnx
      · exact timesDifferentiableAt_congr_germ (k+1) U _ _ a he hexp

 theorem taylorHypothesis_reciprocal (k : ℕ) (U : Set X) (q : X → ℝ) (a : X)
    (hq : TaylorHypothesis k U q a) (hc : q a ≠ 0) :
    TaylorHypothesis k U (fun x => (q x)⁻¹) a := by
  cases k with
  | zero =>
    have hh : IsOpen U ∧ a ∈ U ∧ ContinuousAt q a := by simpa [TaylorHypothesis] using hq
    exact (by simpa [TaylorHypothesis] using (⟨hh.1, hh.2.1, hh.2.2.inv₀ hc⟩ :
      IsOpen U ∧ a ∈ U ∧ ContinuousAt (fun x => (q x)⁻¹) a))
  | succ k =>
    simp only [TaylorHypothesis, Nat.succ_ne_zero, ite_false] at *
    exact timesDifferentiableAt_reciprocal (k+1) U q a hq hc

end ReciprocalCalculus

section ScalarPolynomials
variable {n : ℕ}

 theorem multilinearPolynomial_degree (r : ℕ) (c : (Fin r → Fin n) → ℝ) :
    (multilinearPolynomial r c).totalDegree ≤ r := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans (by simp)

 theorem scalarTaylorCoordinates_degree (k : ℕ) (f : E n → ℝ) (a : E n) :
    (scalarTaylorCoordinates k f a).totalDegree ≤ k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r hr
  apply le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (multilinearPolynomial_degree r _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hr))

 theorem scalarPolynomialEvaluation_unique (k : ℕ) (f : E n → ℝ) (a : E n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ k)
    (hzero : MvPolynomial.eval (fun _ => 0) p = f a)
    (hf : taylorRemainder k f a =o[𝓝 0] (fun h => ‖h‖^k))
    (he : (fun h => f (a+h)-MvPolynomial.eval (fun j => h j) p) =o[𝓝 0] (fun h => ‖h‖^k)) :
    ∀ h, taylorPolynomial k f a h = MvPolynomial.eval (fun j => h j) p := by
  by_cases hn : n = 0
  · subst n
    intro h
    rw [taylorPolynomial_dimension_zero]
    rw [show (fun j : Fin 0 => h j) = (fun _ => (0 : ℝ)) from Subsingleton.elim _ _]
    exact hzero.symm
  · have ho : (fun h : E n => MvPolynomial.eval (fun j => h j)
        (scalarTaylorCoordinates k f a - p)) =o[𝓝[≠] 0] (fun h => ‖h‖^k) := by
      have hh := he.sub hf
      apply (hh.mono nhdsWithin_le_nhds).congr_left
      intro h
      rw [map_sub, scalarTaylorCoordinates_eval]
      change (f (a+h)-MvPolynomial.eval (fun j => h j) p) -
        (f (a+h)-taylorPolynomial k f a h) = _
      abel
    have hz := mvPolynomial_zero_of_isLittleO (by omega : 0 < n) k _
      ((MvPolynomial.totalDegree_sub _ _).trans (max_le (scalarTaylorCoordinates_degree k f a) hp)) ho
    have hpq := sub_eq_zero.mp hz
    intro h
    rw [← hpq, scalarTaylorCoordinates_eval]

 theorem finite_reciprocal_identity (N : ℕ) (c u : ℝ) (hc : c ≠ 0) (hu : c+u ≠ 0) :
    (c+u)⁻¹ - ∑ j ∈ Finset.range N, (-u)^j / c^(j+1) =
      (-u)^N / (c^N * (c+u)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    simp only [pow_succ]
    field_simp
    <;> ring

end ScalarPolynomials

section ReciprocalArithmetic
variable {n : ℕ}

 theorem reciprocalCoordinates_eval_zero (k : ℕ) (P : MvPolynomial (Fin n) ℝ) (c : ℝ)
    (hP : MvPolynomial.eval (fun _ => 0) P = c) :
    MvPolynomial.eval (fun _ => 0) (reciprocalCoordinates k P c) = c⁻¹ := by
  rw [reciprocalCoordinates, truncate_eval_zero]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_pow, map_neg, map_sub, hP, sub_self, neg_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

 theorem polynomial_reciprocal_approximation (k : ℕ) (P : MvPolynomial (Fin n) ℝ) (c : ℝ)
    (hP : MvPolynomial.eval (fun _ => 0) P = c) (hc : c ≠ 0) :
    (fun h : E n => (MvPolynomial.eval (fun j => h j) P)⁻¹ -
      MvPolynomial.eval (fun j => h j) (reciprocalCoordinates k P c)) =o[𝓝 0] (fun h => ‖h‖^k) := by
  let F : E n → ℝ := fun h => MvPolynomial.eval (fun j => h j) P
  let S : MvPolynomial (Fin n) ℝ := ∑ j ∈ Finset.range (k+1),
    MvPolynomial.C ((c^(j+1))⁻¹) * (-(P-MvPolynomial.C c))^j
  have hF0 : F 0 = c := hP
  have hFcont : ContinuousAt F 0 := (polynomial_eval_contDiff P 1).continuous.continuousAt
  have hdF : DifferentiableAt ℝ F 0 := (polynomial_eval_contDiff P 1).differentiable (by simp) 0
  have hu : (fun h => -(F h-c)) =O[𝓝 0] (fun h : E n => ‖h‖) := by
    simpa only [sub_zero, hF0] using hdF.isBigO_sub.neg_left.norm_right
  have huPower := (hu.pow (k+1)).trans_isLittleO (isLittleO_norm_pow_norm_pow (Nat.lt_succ_self k))
  have hD : (fun h => (c^(k+1) * F h)⁻¹) =O[𝓝 (0 : E n)] (fun _ => (1 : ℝ)) := by
    have hn : c^(k+1) * F 0 ≠ 0 := by
      rw [hF0]
      exact mul_ne_zero (pow_ne_zero (k+1) hc) hc
    exact ((continuousAt_const.mul hFcont).inv₀ hn).tendsto.isBigO_one ℝ
  have hraw := huPower.mul_isBigO hD
  simp only [mul_one] at hraw
  have heq : (fun h => (F h)⁻¹ - MvPolynomial.eval (fun j => h j) S) =ᶠ[𝓝 (0 : E n)]
      (fun h => (-(F h-c))^(k+1) * (c^(k+1)*F h)⁻¹) := by
    filter_upwards [hFcont.eventually_ne (by rwa [hF0])] with h hh
    have he := finite_reciprocal_identity (k+1) c (F h-c) hc (by simpa using hh)
    simpa [S, F, map_sum, div_eq_mul_inv, mul_comm] using he
  have hsmall : (fun h => (F h)⁻¹ - MvPolynomial.eval (fun j => h j) S)
      =o[𝓝 (0 : E n)] (fun h => ‖h‖^k) := hraw.congr' heq.symm Filter.EventuallyEq.rfl
  have hsum := hsmall.add (truncate_remainder k S)
  apply hsum.congr_left
  intro h
  change ((F h)⁻¹-MvPolynomial.eval (fun j => h j) S) +
    (MvPolynomial.eval (fun j => h j) S - MvPolynomial.eval (fun j => h j) (truncate k S)) =
      (F h)⁻¹-MvPolynomial.eval (fun j => h j) (truncate k S)
  abel


 theorem taylorPolynomial_reciprocal (k : ℕ) (U : Set (E n)) (q : E n → ℝ) (a h : E n)
    (hq : TaylorHypothesis k U q a) (hc : q a ≠ 0) :
    taylorPolynomial k (fun x => (q x)⁻¹) a h =
      MvPolynomial.eval (fun j => h j) (reciprocalCoordinates k (scalarTaylorCoordinates k q a) (q a)) := by
  let P := scalarTaylorCoordinates k q a
  let c := q a
  have hP0 : MvPolynomial.eval (fun _ => 0) P = c := by
    calc
      _ = taylorPolynomial k q a 0 := scalarTaylorCoordinates_eval k q a 0
      _ = c := taylorPolynomial_zero_increment k q a
  have ht : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 a) := by
    have hh : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 (a+0)) := tendsto_const_nhds.add tendsto_id
    simpa only [add_zero] using hh
  have hqt : Tendsto (fun z : E n => q (a+z)) (𝓝 0) (𝓝 c) :=
    (taylorHypothesis_continuous k U q a hq).tendsto.comp ht
  have hpt : Tendsto (fun z : E n => MvPolynomial.eval (fun j => z j) P) (𝓝 0) (𝓝 c) := by
    have hh := (polynomial_eval_contDiff P 0).continuous.continuousAt (x := (0 : E n))
    have hP0' : (fun z : E n => MvPolynomial.eval (fun j => z j) P) 0 = c := hP0
    simpa only [hP0'] using hh.tendsto
  have hdiff := (hasStrictFDerivAt_inv (𝕜 := ℝ) hc).isBigO_sub.comp_tendsto
    (hqt.prodMk_nhds hpt)
  have hrem : (fun z : E n => q (a+z) - MvPolynomial.eval (fun j => z j) P)
      =o[𝓝 0] (fun z => ‖z‖^k) := by
    simp only [P, scalarTaylorCoordinates_eval]
    exact taylorHypothesis_peano k U q a hq
  have hreplace := hdiff.trans_isLittleO hrem
  have hpoly := polynomial_reciprocal_approximation k P c hP0 hc
  have hsum := hreplace.add hpoly
  have he : (fun z : E n => (q (a+z))⁻¹ -
      MvPolynomial.eval (fun j => z j) (reciprocalCoordinates k P c)) =o[𝓝 0] (fun z => ‖z‖^k) := by
    apply hsum.congr_left
    intro z
    change ((q (a+z))⁻¹-(MvPolynomial.eval (fun j => z j) P)⁻¹) +
      ((MvPolynomial.eval (fun j => z j) P)⁻¹-MvPolynomial.eval (fun j => z j) (reciprocalCoordinates k P c)) = _
    abel
  exact scalarPolynomialEvaluation_unique k (fun x => (q x)⁻¹) a _
    (truncate_degree k _) (reciprocalCoordinates_eval_zero k P c hP0)
    (taylorHypothesis_peano k U _ a (taylorHypothesis_reciprocal k U q a hq hc)) he h

 theorem taylorPolynomial_quotient {m : ℕ} (k : ℕ) (U : Set (E n))
    (f : E n → E m) (q : E n → ℝ) (a h : E n)
    (hf : TaylorHypothesis k U f a) (hq : TaylorHypothesis k U q a) (hc : q a ≠ 0) :
    taylorPolynomial k (fun x => (q x)⁻¹ • f x) a h =
      coordinatePolynomialEval (fun i => truncate k
        (reciprocalCoordinates k (scalarTaylorCoordinates k q a) (q a) * taylorCoordinates k f a i)) h := by
  let P := reciprocalCoordinates k (scalarTaylorCoordinates k q a) (q a)
  let Q := taylorCoordinates k f a
  let R : CoordinatePolynomial n m := fun i => P * Q i
  have hR (z : E n) : coordinatePolynomialEval R z =
      MvPolynomial.eval (fun j => z j) P • coordinatePolynomialEval Q z := by
    ext i
    simp [R, coordinatePolynomialEval_apply, PiLp.smul_apply, smul_eq_mul]
  have hinv := taylorHypothesis_reciprocal k U q a hq hc
  have hir : (fun z : E n => (q (a+z))⁻¹-MvPolynomial.eval (fun j => z j) P)
      =o[𝓝 0] (fun z => ‖z‖^k) := by
    have hh := taylorHypothesis_peano k U (fun x => (q x)⁻¹) a hinv
    change (fun z => (q (a+z))⁻¹-taylorPolynomial k (fun x => (q x)⁻¹) a z) =o[𝓝 0] _ at hh
    simpa only [taylorPolynomial_reciprocal k U q a _ hq hc] using hh
  have ht : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 a) := by
    have hh : Tendsto (fun z : E n => a+z) (𝓝 0) (𝓝 (a+0)) := tendsto_const_nhds.add tendsto_id
    simpa only [add_zero] using hh
  have hfb := ((taylorHypothesis_continuous k U f a hf).tendsto.comp ht).isBigO_one ℝ
  have hpb := ((polynomial_eval_contDiff P 0).continuous.continuousAt (x := (0 : E n))).tendsto.isBigO_one ℝ
  have h1 := hir.smul_isBigO hfb
  have h2 := hpb.smul_isLittleO (taylorHypothesis_peano k U f a hf)
  simp only [smul_eq_mul, mul_one] at h1
  simp only [smul_eq_mul, one_mul] at h2
  have hraw : (fun z : E n => (q (a+z))⁻¹ • f (a+z)-coordinatePolynomialEval R z)
      =o[𝓝 0] (fun z => ‖z‖^k) := by
    apply (h1.add h2).congr_left
    intro z
    change ((q (a+z))⁻¹ - MvPolynomial.eval (fun j => z j) P) • f (a+z) +
      MvPolynomial.eval (fun j => z j) P • (f (a+z)-taylorPolynomial k f a z) = _
    rw [hR, show Q = taylorCoordinates k f a from rfl, taylorCoordinates_eval]
    simp only [sub_smul, smul_sub]
    abel
  have he : (fun z : E n => (q (a+z))⁻¹ • f (a+z)-
      coordinatePolynomialEval (fun i => truncate k (R i)) z) =o[𝓝 0] (fun z => ‖z‖^k) := by
    apply (hraw.add (truncate_vector_remainder k R)).congr_left
    intro z
    abel
  have hz : coordinatePolynomialEval (fun i => truncate k (R i)) 0 = (q a)⁻¹ • f a := by
    have hz' : coordinatePolynomialEval (fun i => truncate k (R i)) 0 = coordinatePolynomialEval R 0 := by
      ext i
      exact truncate_eval_zero k (R i)
    rw [hz', hR, show Q = taylorCoordinates k f a from rfl, taylorCoordinates_eval,
      taylorPolynomial_zero_increment]
    congr 1
    exact reciprocalCoordinates_eval_zero k _ _ (by
      calc
        _ = taylorPolynomial k q a 0 := scalarTaylorCoordinates_eval k q a 0
        _ = q a := taylorPolynomial_zero_increment k q a)
  have hprod := taylorHypothesis_bilinear k (ContinuousLinearMap.lsmul ℝ ℝ) U
    (fun x => (q x)⁻¹) f a hinv hf
  exact congrFun (polynomialEvaluation_unique k (fun x => (q x)⁻¹ • f x) a _
    (fun i => truncate_degree k (R i)) hz (taylorHypothesis_peano k U _ a hprod) he) h

end ReciprocalArithmetic
abbrev truncate : Specs.D04.C03.TaylorArithmetic.truncateType :=
  @Specs.D04.C03.TaylorArithmetic.Model.truncate

abbrev multilinearPolynomial : Specs.D04.C03.TaylorArithmetic.multilinearPolynomialType :=
  @Specs.D04.C03.TaylorArithmetic.Model.multilinearPolynomial

abbrev taylorCoordinates : Specs.D04.C03.TaylorArithmetic.taylorCoordinatesType :=
  @Specs.D04.C03.TaylorArithmetic.Model.taylorCoordinates

abbrev scalarTaylorCoordinates : Specs.D04.C03.TaylorArithmetic.scalarTaylorCoordinatesType :=
  @Specs.D04.C03.TaylorArithmetic.Model.scalarTaylorCoordinates

abbrev bilinearCoordinates : Specs.D04.C03.TaylorArithmetic.bilinearCoordinatesType :=
  @Specs.D04.C03.TaylorArithmetic.Model.bilinearCoordinates

abbrev compositionCoordinates : Specs.D04.C03.TaylorArithmetic.compositionCoordinatesType :=
  @Specs.D04.C03.TaylorArithmetic.Model.compositionCoordinates

abbrev reciprocalCoordinates : Specs.D04.C03.TaylorArithmetic.reciprocalCoordinatesType :=
  @Specs.D04.C03.TaylorArithmetic.Model.reciprocalCoordinates

abbrev TaylorHypothesis : Specs.D04.C03.TaylorArithmetic.TaylorHypothesisType :=
  @Specs.D04.C03.TaylorArithmetic.Model.TaylorHypothesis

end TaylorArithmetic
end D04
