import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ExponentialComponent
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
namespace ExpandedFA.BanachAlgebra.ExponentialComponent

open Set Filter
open scoped Topology
open ContourCalculus HolomorphicHomomorphism HolomorphicSpectralMapping

universe u

local instance rationalNormedAlgebra {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] :
    NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

section Components
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The exponential as a continuous map into the invertible group. -/
def expUnit (a : A) : Aˣ := (NormedSpace.isUnit_exp a).unit

@[simp] lemma coe_expUnit (a : A) : (expUnit a : A) = NormedSpace.exp a :=
  (NormedSpace.isUnit_exp a).unit_spec

@[simp] lemma expUnit_zero : expUnit (0 : A) = 1 := by
  ext; simp

@[simp] lemma expUnit_neg (a : A) : expUnit (-a) = (expUnit a)⁻¹ := by
  apply Units.ext
  calc
    ↑(expUnit (-a)) = NormedSpace.exp (-a) := coe_expUnit _
    _ = Ring.inverse (NormedSpace.exp a) := (Ring.inverse_exp a).symm
    _ = ↑((expUnit a)⁻¹) := by rw [← coe_expUnit a, Ring.inverse_unit]

lemma continuous_expUnit : Continuous (expUnit : A → Aˣ) :=
  Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
    (by simpa only [Function.comp_def, coe_expUnit] using (NormedSpace.exp_continuous : Continuous (NormedSpace.exp : A → A)))

/-- Finite words, allowing the empty word, form a subgroup. -/
def exponentialSubgroup : Subgroup Aˣ where
  carrier := {u | ∃ l : List A, (l.map expUnit).prod = u}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨l, rfl⟩ ⟨m, rfl⟩
    exact ⟨l ++ m, by simp⟩
  inv_mem' := by
    rintro _ ⟨l, rfl⟩
    refine ⟨l.reverse.map Neg.neg, ?_⟩
    simp [List.map_map, Function.comp_def, List.prod_inv_reverse]

lemma exponentialSubgroup_mem_nhds : (exponentialSubgroup (A := A) : Set Aˣ) ∈ 𝓝 1 := by
  have hd : HasStrictFDerivAt (NormedSpace.exp : A → A)
      (ContinuousLinearEquiv.refl ℂ A : A →L[ℂ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hr : range (NormedSpace.exp : A → A) ∈ 𝓝 (1 : A) := by
    rw [← NormedSpace.exp_zero (𝔸 := A), ← hd.map_nhds_eq_of_equiv]
    exact Filter.mem_map.mpr (by simp)
  have hp := (Units.continuous_val.continuousAt (x := (1 : Aˣ))).preimage_mem_nhds (by simpa using hr)
  apply Filter.mem_of_superset hp
  rintro u ⟨a, ha⟩
  refine ⟨[a], ?_⟩
  apply Units.ext
  simpa using ha

lemma exponentialSubgroup_isOpen : IsOpen (exponentialSubgroup (A := A) : Set Aˣ) :=
  (exponentialSubgroup (A := A)).isOpen_of_mem_nhds exponentialSubgroup_mem_nhds

lemma expUnit_mem_component (a : A) : expUnit a ∈ connectedComponent (1 : Aˣ) := by
  have h := continuous_expUnit.image_connectedComponent_subset (0 : A)
  have ha : a ∈ connectedComponent (0 : A) := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial
  simpa using h ⟨a, ha, rfl⟩

lemma coe_expUnit_prod (l : List A) :
    ((l.map expUnit).prod : A) = (l.map NormedSpace.exp).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa only [List.map_cons, List.prod_cons, Units.val_mul, coe_expUnit] using
      (congrArg (fun x : A => NormedSpace.exp a * x) ih)

lemma component_eq_exponentialSubgroup : connectedComponent (1 : Aˣ) =
    (exponentialSubgroup (A := A) : Set Aˣ) := by
  apply Subset.antisymm
  · exact (show IsClopen (exponentialSubgroup (A := A) : Set Aˣ) from
      ⟨(exponentialSubgroup (A := A)).isClosed_of_isOpen exponentialSubgroup_isOpen,
        exponentialSubgroup_isOpen⟩).connectedComponent_subset
      (exponentialSubgroup (A := A)).one_mem
  · rintro u ⟨l, rfl⟩
    induction l with
    | nil => simpa using (mem_connectedComponent (x := (1 : Aˣ)))
    | cons a l ih =>
      simpa using mul_mem_connectedComponent_one (expUnit_mem_component a) ih

end Components

theorem exponential_identity_component : Spec.ExponentialIdentityComponent.{u} := by
  intro A _ _ hA u
  let : CompleteSpace A := hA.1
  rw [component_eq_exponentialSubgroup]
  change (∃ l : List A, (l.map expUnit).prod = u) ↔ _
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l, (coe_expUnit_prod l).symm⟩
  · rintro ⟨l, hl⟩
    refine ⟨l, Units.ext ?_⟩
    exact (coe_expUnit_prod l).trans hl

theorem invertibles_locally_path_connected : Spec.InvertiblesLocallyPathConnected.{u} := by
  intro A _ _ hA
  let : CompleteSpace A := hA.1
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let : LocallyPathConnectedSpace Aˣ :=
    Units.isOpenEmbedding_val.locallyPathConnectedSpace
  exact ⟨inferInstance, fun u => (pathComponent_eq_connectedComponent u).symm⟩

section Calculus
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

lemma holomorphicValue_function_pow (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hKU : algebraSpectrum ℂ A a ⊆ U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    holomorphicValue A a U (fun z => f z ^ n) = (holomorphicValue A a U f) ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using unitality A hA a U hU hKU
  | succ n ih =>
    simpa only [pow_succ, ih] using
      multiplicativity A hA a U (fun z => f z ^ n) f hU hKU (hf.pow n) hf

lemma holomorphicValue_function_sum (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} (hU : IsOpen U) (hKU : algebraSpectrum ℂ A a ⊆ U)
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    holomorphicValue A a U (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, holomorphicValue A a U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holomorphicValue_const hA a hU hKU 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hh := scalar_linearity A hA a U (f i) (fun z => ∑ j ∈ s, f j z)
      1 1 hU hKU (hf i (Finset.mem_insert_self _ _))
      (DifferentiableOn.fun_sum (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [one_mul, one_smul, hs] using hh

lemma holomorphicValue_function_smul (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hKU : algebraSpectrum ℂ A a ⊆ U)
    (hf : DifferentiableOn ℂ f U) (c : ℂ) :
    holomorphicValue A a U (fun z => c * f z) = c • holomorphicValue A a U f := by
  have h := scalar_linearity A hA a U f f c 0 hU hKU hf hf
  simpa only [zero_mul, add_zero, zero_smul] using h

/-- Uniform convergence on the actual selected contour, not on a larger
neighborhood, suffices for exponentiating a calculus value. -/
theorem holomorphic_exponential : Spec.HolomorphicExponential.{u} := by
  intro A _ _ hA a U f hU hKU hf
  let : CompleteSpace A := hA.1
  let Γ := selectedCycle (algebraSpectrum ℂ A a) U
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  have htr : Γ.trace ⊆ U := fun z hz => (hΓ.1 hz).1
  obtain ⟨R, hR⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn
    (hf.continuousOn.mono htr)
  let F : ℕ → ℂ → ℂ := fun N z =>
    ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ * f z ^ n
  have hF (N : ℕ) : DifferentiableOn ℂ (F N) U :=
    DifferentiableOn.fun_sum (fun n _ =>
      (differentiableOn_const ((n.factorial : ℂ)⁻¹)).mul (hf.pow n))
  have hfe : DifferentiableOn ℂ (fun z => Complex.exp (f z)) U :=
    Complex.differentiable_exp.comp_differentiableOn hf
  have ht : TendstoUniformlyOn F (fun z => Complex.exp (f z)) atTop Γ.trace := by
    have hs := tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial R)
      (f := fun n z => (n.factorial : ℂ)⁻¹ * f z ^ n) (s := Γ.trace) (by
        intro n z hz
        simp only [norm_mul, norm_inv, norm_natCast, norm_pow]
        calc
          (n.factorial : ℝ)⁻¹ * ‖f z‖ ^ n ≤ (n.factorial : ℝ)⁻¹ * R ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hR z hz) n)
              (by positivity)
          _ = R ^ n / (n.factorial : ℝ) := by rw [div_eq_mul_inv, mul_comm])
    simpa only [F, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ, smul_eq_mul] using hs
  have hv := holomorphic_fixed_contour_convergence A hA a U (fun _ => U)
    (fun z => Complex.exp (f z)) F hU (fun _ => hU) hKU (fun _ => hKU)
    hfe hF Γ hΓ (fun _ => hΓ) ht
  have he (N : ℕ) : holomorphicValue A a U (F N) =
      ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ • (holomorphicValue A a U f) ^ n := by
    calc
      _ = ∑ n ∈ Finset.range N,
          holomorphicValue A a U (fun z => (n.factorial : ℂ)⁻¹ * f z ^ n) :=
        holomorphicValue_function_sum hA a hU hKU (Finset.range N)
          (fun n z => (n.factorial : ℂ)⁻¹ * f z ^ n)
          (fun n _ => (differentiableOn_const _).mul (hf.pow n))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n _
        exact (holomorphicValue_function_smul hA a hU hKU (hf.pow n) _).trans
          (congrArg (fun x : A => (n.factorial : ℂ)⁻¹ • x)
            (holomorphicValue_function_pow hA a hU hKU hf n))
  have hv' : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (n.factorial : ℂ)⁻¹ • (holomorphicValue A a U f) ^ n) atTop
      (𝓝 (holomorphicValue A a U (fun z => Complex.exp (f z)))) := by
    simpa only [he] using hv
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ)
    (holomorphicValue A a U f)).tendsto_sum_nat
  have hs' : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (n.factorial : ℂ)⁻¹ • (holomorphicValue A a U f) ^ n) atTop
      (𝓝 (NormedSpace.exp (holomorphicValue A a U f))) := by
    simpa only [inv_natCast_smul_eq ℚ ℂ] using hs
  exact tendsto_nhds_unique hs' hv'

/-- Every branch of the scalar holomorphic logarithm works. -/
theorem holomorphic_logarithm : Spec.HolomorphicLogarithm.{u} := by
  intro A _ _ hA a U L hU hKU hL hexp
  symm
  exact (holomorphic_exponential A hA a U L hU hKU hL).trans
    ((holomorphicValue_congr hA a hU hKU (f := fun z => Complex.exp (L z))
      (g := id) hexp).trans (coordinate A hA a U hU hKU))

theorem holomorphic_root : Spec.HolomorphicRoot.{u} := by
  intro A _ _ hA a U f n _hn hU hKU hf hroot
  change (holomorphicValue A a U f) ^ n = a
  rw [← holomorphicValue_function_pow hA a hU hKU hf n,
    holomorphicValue_congr hA a hU hKU hroot]
  exact coordinate A hA a U hU hKU

theorem roots_from_logarithm : Spec.RootsFromLogarithm.{u} := by
  intro A _ _ hA a U L hU hKU hL hexp n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  apply holomorphic_root A hA a U (fun z => Complex.exp (L z / (n : ℂ))) n hn hU hKU
    (Complex.differentiable_exp.comp_differentiableOn (hL.div_const _))
  intro z hz
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hn0]
  exact hexp z hz

end Calculus

end ExpandedFA.BanachAlgebra.ExponentialComponent
