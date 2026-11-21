import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.CompactSupportPDESolvability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.ExponentialTypePolynomialDivision
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

noncomputable section
open Set TopologicalSpace Filter
open scoped ContDiff Topology
namespace ExpandedFA.Fourier.CompactSupportPDE
open ExpandedFA.Distributions ExpandedFA.Fourier.PaleyWiener
open ExpandedFA.Fourier.DistributionPaleyWiener

/-- Explicit bridge to the upstream distribution derivative and its transpose sign. -/
lemma normalizedWord_apply {d : ℕ} (w : List (Fin d)) (u : Distribution d)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    normalizedWord w u φ = (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ w.length *
      u (testPartialCLM w φ) := by
  induction w generalizing u with
  | nil => simp [normalizedWord, testPartialCLM]
  | cons i w ih =>
    rw [normalizedWord, ih]
    simp [normalizedPartial, testPartialCLM, pow_succ, mul_assoc, mul_left_comm]

lemma normalizedWord_eq_derivative {d : ℕ} (w : List (Fin d)) (u : Distribution d) :
    normalizedWord w u = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ w.length) •
      distributionDerivative ℂ d ⊤ w u := by
  ext φ
  rw [normalizedWord_apply, smul_apply, distributionDerivative_apply]
  rw [show -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ =
    (-1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ by ring, mul_pow]
  simp only [smul_eq_mul]
  ring

lemma distributionSupport_isClosed {d : ℕ} (u : Distribution d) :
    IsClosed (distributionSupport u) := by
  change IsClosed (Set.univ \ vanishingRegion u)
  rw [show Set.univ \ vanishingRegion u = (vanishingRegion u)ᶜ by ext x; simp]
  exact (support_vanishing ℂ d ⊤ u).1.isClosed_compl

lemma support_zero {d : ℕ} : distributionSupport (0 : Distribution d) = ∅ := by
  apply subset_antisymm _ (empty_subset _)
  apply (support_subset_iff_vanishes _ isClosed_empty).mpr
  intro φ _
  rfl

lemma euclideanSupport_zero {d : ℕ} : euclideanSupport (0 : Distribution d) = ∅ := by
  simp [euclideanSupport, support_zero]

lemma support_smul_subset {d : ℕ} (c : ℂ) (u : Distribution d) :
    distributionSupport (c • u) ⊆ distributionSupport u := by
  apply (support_subset_iff_vanishes _ (distributionSupport_isClosed u)).mpr
  intro φ hφ
  have h := (support_subset_iff_vanishes u (distributionSupport_isClosed u)).mp
    (Subset.refl _) φ hφ
  simp [h]

lemma support_sum_subset {d : ℕ} {ι : Type*} (s : Finset ι) (u : ι → Distribution d) :
    distributionSupport (∑ i ∈ s, u i) ⊆ ⋃ i ∈ s, distributionSupport (u i) := by
  classical
  have hclosed : IsClosed (⋃ i ∈ s, distributionSupport (u i)) :=
    s.finite_toSet.isClosed_biUnion (fun i _ => distributionSupport_isClosed (u i))
  apply (support_subset_iff_vanishes _ hclosed).mpr
  intro φ hφ
  simp only [sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply (support_subset_iff_vanishes _ (distributionSupport_isClosed (u i))).mp
    (Subset.refl _) φ
  exact hφ.trans (compl_subset_compl.mpr (by intro x hx; exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx⟩⟩))

lemma testPartial_support {d : ℕ} (i : Fin d) (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    tsupport (testPartialCLM [i] φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have heq : (φ : Domain d → ℂ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  rw [testPartial_single_apply, heq.fderiv_eq]
  simp

lemma support_normalizedPartial {d : ℕ} (i : Fin d) (u : Distribution d) :
    distributionSupport (normalizedPartial i u) ⊆ distributionSupport u := by
  apply (support_subset_iff_vanishes _ (distributionSupport_isClosed u)).mpr
  intro φ hφ
  have h := (support_subset_iff_vanishes u (distributionSupport_isClosed u)).mp
    (Subset.refl _) (testPartialCLM [i] φ) ((testPartial_support i φ).trans hφ)
  simp [normalizedPartial, h]

lemma support_normalizedWord {d : ℕ} (w : List (Fin d)) (u : Distribution d) :
    distributionSupport (normalizedWord w u) ⊆ distributionSupport u := by
  induction w generalizing u with
  | nil => exact Subset.refl _
  | cons i w ih => exact (ih _).trans (support_normalizedPartial i u)

lemma support_polynomialOperator {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (u : Distribution d) :
    distributionSupport (polynomialOperator P u) ⊆ distributionSupport u := by
  apply (support_sum_subset P.support _).trans
  simp only [iUnion_subset_iff]
  intro α _
  exact (support_smul_subset _ _).trans (support_normalizedWord _ u)

lemma compact_of_support_subset {d : ℕ} {u v : Distribution d}
    (hu : IsCompact (euclideanSupport u)) (h : distributionSupport v ⊆ distributionSupport u) :
    IsCompact (euclideanSupport v) :=
  hu.of_isClosed_subset (isClosed_euclideanSupport v) (image_mono h)

lemma compact_polynomialOperator {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) : IsCompact (euclideanSupport (polynomialOperator P u)) :=
  compact_of_support_subset hu (support_polynomialOperator P u)



lemma fourierLaplace_smul {d : ℕ} (c : ℂ) (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) :
    fourierLaplace (c • u) = fun z => c * fourierLaplace u z := by
  have hcu := compact_of_support_subset hu (support_smul_subset c u)
  have hext : smoothExtension (c • u) = c • smoothExtension u := by
    apply smoothExtension_eq hcu
    intro φ
    simp [extension d u hu]
  funext z
  simp [DistributionPaleyWiener.fourierLaplace, hext]

lemma compact_sum {d : ℕ} {ι : Type*} (s : Finset ι) (u : ι → Distribution d)
    (hu : ∀ i ∈ s, IsCompact (euclideanSupport (u i))) :
    IsCompact (euclideanSupport (∑ i ∈ s, u i)) := by
  classical
  have hK : IsCompact (⋃ i ∈ s, distributionSupport (u i)) :=
    s.finite_toSet.isCompact_biUnion (fun i hi => isCompact_distributionSupport (hu i hi))
  exact (hK.image (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous).of_isClosed_subset
    (isClosed_euclideanSupport _) (image_mono (support_sum_subset s u))

lemma fourierLaplace_sum {d : ℕ} {ι : Type*} (s : Finset ι) (u : ι → Distribution d)
    (hu : ∀ i ∈ s, IsCompact (euclideanSupport (u i))) :
    fourierLaplace (∑ i ∈ s, u i) = fun z => ∑ i ∈ s, fourierLaplace (u i) z := by
  classical
  have hext : smoothExtension (∑ i ∈ s, u i) = ∑ i ∈ s, smoothExtension (u i) := by
    apply smoothExtension_eq (compact_sum s u hu)
    intro φ
    simp only [sum_apply]
    exact Finset.sum_congr rfl (fun i hi => extension d (u i) (hu i hi) φ)
  funext z
  simp [DistributionPaleyWiener.fourierLaplace, hext]

lemma fourierLaplace_normalizedPartial {d : ℕ} (i : Fin d) (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) (z : ComplexEuclidean d) :
    fourierLaplace (normalizedPartial i u) z = z i * fourierLaplace u z := by
  obtain ⟨χ0, V, hV, hs, hχ0⟩ := cutoff_existence d ⊤
    (distributionSupport u) (isCompact_distributionSupport hu) (subset_univ _)
  let χ := scalarCutoff ℂ χ0
  have hχ : EqOn χ 1 V := by
    intro x hx
    simp [χ, hχ0 hx]
  have hd := compact_of_support_subset hu (support_normalizedPartial i u)
  rw [fourierLaplace_cutoff hd χ V hV ((support_normalizedPartial i u).trans hs) hχ z,
    fourierLaplace_cutoff hu χ V hV hs hχ z]
  let ψ := smoothCutoffCLM χ (laplaceKernel z)
  have heq : u (testPartialCLM [i] ψ) =
      u ((-2 * (Real.pi : ℂ) * Complex.I * z i) • ψ) := by
    apply pairing_locality ℂ d ⊤ u _ _ V hV hs
    intro x hx
    rw [testPartial_single_apply]
    have hloc : (ψ : Domain d → ℂ) =ᶠ[𝓝 x] (laplaceKernel z).val := by
      filter_upwards [hV.mem_nhds hx] with y hy
      simp [ψ, hχ hy]
    rw [hloc.fderiv_eq]
    have hk := laplaceKernel_coordinate_derivative z 1 x (fun _ => i)
    simp only [iteratedFDeriv_one_apply, Finset.prod_const, Finset.card_fin, pow_one] at hk
    change fderiv ℝ (laplaceKernel z).val x (coordinateVector i) =
      (-2 * (Real.pi : ℂ) * Complex.I * z i) * ψ x
    rw [show ψ x = (laplaceKernel z).val x by simp [ψ, hχ hx]]
    exact hk
  change -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * u (testPartialCLM [i] ψ) = z i * u ψ
  rw [heq, map_smul, smul_eq_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma compact_normalizedWord {d : ℕ} (w : List (Fin d)) (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) : IsCompact (euclideanSupport (normalizedWord w u)) :=
  compact_of_support_subset hu (support_normalizedWord w u)

lemma fourierLaplace_normalizedWord {d : ℕ} (w : List (Fin d)) (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) (z : ComplexEuclidean d) :
    fourierLaplace (normalizedWord w u) z = (w.map (fun i => z i)).prod * fourierLaplace u z := by
  induction w generalizing u with
  | nil => simp [normalizedWord]
  | cons i w ih =>
    rw [normalizedWord, ih _ (compact_of_support_subset hu (support_normalizedPartial i u)),
      fourierLaplace_normalizedPartial i u hu z]
    simp [List.map_cons, mul_left_comm, mul_assoc]

lemma multiIndexWord_prod {d : ℕ} (α : Fin d →₀ ℕ) (z : ComplexEuclidean d) :
    ((multiIndexWord (fun j => α j)).map (fun i => z i)).prod = α.prod (fun j n => z j ^ n) := by
  classical
  have hprod (l : List (Fin d)) :
      ((l.flatMap fun i => List.replicate (α i) i).map (fun i => z i)).prod =
        (l.map fun i => z i ^ α i).prod := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]
  rw [multiIndexWord, hprod]
  simp only [List.map_ofFn, List.prod_ofFn]
  exact (Finsupp.prod_fintype α (fun j n => z j ^ n) (fun j => pow_zero (z j))).symm

lemma fourierLaplace_polynomialOperator {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (u : Distribution d) (hu : IsCompact (euclideanSupport u)) (z : ComplexEuclidean d) :
    fourierLaplace (polynomialOperator P u) z =
      MvPolynomial.eval (fun j => z j) P * fourierLaplace u z := by
  classical
  have hc (α : Fin d →₀ ℕ) : IsCompact (euclideanSupport
      (P.coeff α • normalizedWord (multiIndexWord (fun j => α j)) u)) :=
    compact_of_support_subset (compact_normalizedWord _ u hu) (support_smul_subset _ _)
  rw [polynomialOperator, fourierLaplace_sum P.support _ (fun α _ => hc α)]
  simp_rw [fourierLaplace_smul _ _ (compact_normalizedWord _ u hu),
    fourierLaplace_normalizedWord _ u hu, multiIndexWord_prod, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1



/-- Cancellation uses entire functions on complex lines, not division on real axes. -/
lemma entire_polynomial_cancel {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (F G : ComplexEuclidean d → ℂ) (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ z, MvPolynomial.eval (fun j => z j) P * F z =
      MvPolynomial.eval (fun j => z j) P * G z) : F = G := by
  obtain ⟨a, ha⟩ : ∃ a : Fin d → ℂ, MvPolynomial.eval a P ≠ 0 := by
    by_contra! hn
    exact hP (MvPolynomial.funext (fun a => by simpa using hn a))
  let z₀ : ComplexEuclidean d := WithLp.toLp 2 a
  have hp₀ : MvPolynomial.eval (fun j => z₀ j) P ≠ 0 := ha
  have hpcont : Continuous (fun z : ComplexEuclidean d => MvPolynomial.eval (fun j => z j) P) :=
    P.continuous_eval.comp (by fun_prop)
  have hn : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun j => z j) P ≠ 0 :=
    hpcont.continuousAt.eventually_ne hp₀
  funext z
  let l : ℂ → ComplexEuclidean d := fun t => z₀ + t • (z - z₀)
  have hl : Differentiable ℂ l := (differentiable_id.smul_const _).const_add _
  have hlocal : (fun t => F (l t)) =ᶠ[𝓝 (0 : ℂ)] (fun t => G (l t)) := by
    have ht : Tendsto l (𝓝 0) (𝓝 z₀) := by simpa [l] using hl.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [ht.eventually hn] with t ht
    exact mul_left_cancel₀ ht (h (l t))
  have heq := ((hF.comp hl).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    ((hG.comp hl).differentiableOn.analyticOnNhd isOpen_univ) hlocal
  simpa [l] using congrFun heq 1

theorem uniqueness : Specs.ExpandedFA.Fourier.CompactSupportPDESolvability.uniquenessType := by
  intro d P hP u w hu hw heq
  apply injectivity d u w hu hw
  apply entire_polynomial_cancel P hP _ _ (entire d u hu) (entire d w hw)
  intro z
  rw [← fourierLaplace_polynomialOperator P u hu z,
    ← fourierLaplace_polynomialOperator P w hw z, heq]

/-- Barycentres of at most n points in K. -/
def barycentreSet {d : ℕ} (K : Set (Euclidean d)) (n : ℕ) : Set (Euclidean d) :=
  (fun p : (Fin n → ℝ) × (Fin n → Euclidean d) => ∑ i, p.1 i • p.2 i) ''
    ((stdSimplex ℝ (Fin n)) ×ˢ (Set.pi Set.univ (fun _ : Fin n => K)))

lemma compact_barycentreSet {d : ℕ} {K : Set (Euclidean d)} (hK : IsCompact K) (n : ℕ) :
    IsCompact (barycentreSet K n) := by
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hK)).image
  fun_prop

/-- Finite-dimensional compactness follows from Carathéodory's theorem and
compactness of the coefficient simplex times the finite product of K. -/
lemma compact_convexHull {d : ℕ} {K : Set (Euclidean d)} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  classical
  have heq : convexHull ℝ K = ⋃ n ∈ Finset.range (Module.finrank ℝ (Euclidean d) + 2),
      barycentreSet K n := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨ι, hι, z, w, hz, ha, hw, hsum, heq⟩ := eq_pos_convex_span_of_mem_convexHull hx
      let := hι
      let n := Fintype.card ι
      let e := Fintype.equivFin ι
      have hn : n < Module.finrank ℝ (Euclidean d) + 2 := by
        have hle := ha.card_le_finrank_succ
        have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        omega
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hn, ?_⟩⟩
      refine ⟨((fun i => w (e.symm i)), (fun i => z (e.symm i))), ⟨?_, ?_⟩, ?_⟩
      · exact ⟨fun i => (hw _).le, (e.symm.sum_comp w).trans hsum⟩
      · intro i _
        exact hz (Set.mem_range_self _)
      · exact (e.symm.sum_comp (fun i => w i • z i)).trans heq
    · rintro x hx
      obtain ⟨n, _, ⟨p, hp, rfl⟩⟩ := Set.mem_iUnion₂.mp hx
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => hp.1.1 i) hp.1.2
        (fun i _ => subset_convexHull ℝ K (hp.2 i (Set.mem_univ _)))
  rw [heq]
  exact (Finset.range _).finite_toSet.isCompact_biUnion (fun n _ => compact_barycentreSet hK n)



@[simp] lemma normalizedPartial_zero {d : ℕ} (i : Fin d) :
    normalizedPartial i (0 : Distribution d) = 0 := by
  ext φ
  simp [normalizedPartial]

@[simp] lemma normalizedWord_zero {d : ℕ} (w : List (Fin d)) :
    normalizedWord w (0 : Distribution d) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa [normalizedWord] using ih

@[simp] lemma polynomialOperator_zero {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    polynomialOperator P (0 : Distribution d) = 0 := by
  classical
  ext φ
  simp [polynomialOperator]

lemma nonempty_support_of_ne_zero {d : ℕ} {v : Distribution d} (hv : v ≠ 0) :
    (euclideanSupport v).Nonempty := by
  by_contra hn
  have he : euclideanSupport v = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  have hs : distributionSupport v ⊆ ∅ := by
    intro x hx
    have hmem := Set.mem_image_of_mem (EuclideanSpace.equiv (Fin d) ℝ).symm hx
    change (EuclideanSpace.equiv (Fin d) ℝ).symm x ∈ euclideanSupport v at hmem
    rw [he] at hmem
    exact hmem.elim
  apply hv
  ext φ
  exact (support_subset_iff_vanishes v isClosed_empty).mp hs φ (by simpa using subset_univ (tsupport φ))

/-- The inverse transform has the exact convex support type. The zero case
uses the zero distribution directly, before any support function is evaluated. -/
lemma exists_supported_solution {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (v : Distribution d) (hv : IsCompact (euclideanSupport v))
    (G : ComplexEuclidean d → ℂ) (hG : Differentiable ℂ G)
    (hdiv : ∀ z, fourierLaplace v z = MvPolynomial.eval (fun j => z j) P * G z) :
    ∃ u : Distribution d, IsCompact (euclideanSupport u) ∧ polynomialOperator P u = v ∧
      SupportedIn (convexHull ℝ (euclideanSupport v)) u := by
  by_cases hv0 : v = 0
  · subst v
    refine ⟨0, ?_, polynomialOperator_zero P, ?_⟩
    · rw [euclideanSupport_zero]
      exact isCompact_empty
    · change euclideanSupport (0 : Distribution d) ⊆ _
      rw [euclideanSupport_zero]
      exact empty_subset _
  let K := convexHull ℝ (euclideanSupport v)
  have hK : IsCompact K := compact_convexHull hv
  have hne : K.Nonempty := (nonempty_support_of_ne_zero hv0).convexHull
  have hc : Convex ℝ K := convex_convexHull ℝ _
  have hvK : SupportedIn K v := subset_convexHull ℝ _
  have hbound := (DistributionPaleyWiener.forward d K hne hK hc v hvK).2
  have hproduct : (fun z => MvPolynomial.eval (fun j => z j) P * G z) =
      fourierLaplace v := funext (fun z => (hdiv z).symm)
  have hGbound : PolynomialExponentialType K G :=
    ExponentialTypePolynomialDivision.polynomial_division d K hne hK hc P hP G hG
      (hproduct.symm ▸ hbound)
  obtain ⟨u, huK, htransform⟩ := DistributionPaleyWiener.inverse_exists d K hne hK hc G hG hGbound
  have hu := isCompact_euclideanSupport_of_supportedIn hK huK
  refine ⟨u, hu, ?_, huK⟩
  apply injectivity d _ v (compact_polynomialOperator P u hu) hv
  funext z
  rw [fourierLaplace_polynomialOperator P u hu z, htransform, hdiv]

theorem solvability : Specs.ExpandedFA.Fourier.CompactSupportPDESolvability.solvabilityType := by
  intro d P hP v hv
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fourierLaplace u, entire d u hu, fourierLaplace_polynomialOperator P u hu⟩
  · rintro ⟨G, hG, hdiv⟩
    obtain ⟨u, hu, heq, _⟩ := exists_supported_solution P hP v hv G hG hdiv
    exact ⟨u, hu, heq⟩

theorem solution_support : Specs.ExpandedFA.Fourier.CompactSupportPDESolvability.supportType := by
  intro d P hP u v hu hv heq
  have hdiv (z : ComplexEuclidean d) : fourierLaplace v z =
      MvPolynomial.eval (fun j => z j) P * fourierLaplace u z := by
    rw [← heq, fourierLaplace_polynomialOperator P u hu z]
  obtain ⟨w, hw, hwv, hws⟩ := exists_supported_solution P hP v hv
    (fourierLaplace u) (entire d u hu) hdiv
  have huw : u = w := uniqueness d P hP u w hu hw (heq.trans hwv.symm)
  rw [huw]
  exact hws

theorem zero_case : Specs.ExpandedFA.Fourier.CompactSupportPDESolvability.zeroType := by
  intro d P hP
  refine ⟨polynomialOperator_zero P, euclideanSupport_zero, ?_⟩
  intro u hu heq
  exact uniqueness d P hP u 0 hu (by rw [euclideanSupport_zero]; exact isCompact_empty)
    (heq.trans (polynomialOperator_zero P).symm)

end ExpandedFA.Fourier.CompactSupportPDE
