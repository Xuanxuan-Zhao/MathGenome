import MathGenome.Internal.FourierSobolev.Specs.P102.U4.PointSupport
import MathGenome.Internal.FourierSobolev.P102.U4.CompactSupportExtension
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set TopologicalSpace Filter Metric
open scoped ContDiff Distributions Topology
namespace P102.U4

abbrev dirac : PointSupportExpected.DiracType := @pointMass

@[simp] theorem pointMass_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (φ : TestSpace 𝕜 Ω) :
    pointMass 𝕜 Ω a φ = φ a := rfl

/-- The finite jet really is the canonical upstream multi-index derivative. -/
@[simp] theorem testJet_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (m : ℕ)
    (φ : TestSpace 𝕜 Ω) (α : BoundedMultiIndex d m) :
    testJet 𝕜 Ω a m φ α = multiPartial φ α.val a := by
  exact congrFun (testPartialWord_coe Ω _ φ) a

theorem dirac_derivative_formula : PointSupportExpected.DerivativeFormula := by
  intro d 𝕜 _ Ω a α φ
  change (-1 : 𝕜) ^ α.card * (testPartialWord Ω (α.sort (· ≤ ·)) φ) a = _
  rw [testPartialWord_coe]
  rfl

/-- Pairing with the finite sum, including the transpose sign. -/
theorem pointDerivativeSum_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (m : ℕ)
    (c : BoundedMultiIndex d m → 𝕜) (φ : TestSpace 𝕜 Ω) :
    pointDerivativeSum Ω a m c φ =
      ∑ α, c α * ((-1 : 𝕜) ^ α.val.card * multiPartial φ α.val a) := by
  change (∑ α, c α • distributionPartial α.val (pointMass 𝕜 Ω a)) φ = _
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  change c α * distributionPartial α.val (pointMass 𝕜 Ω a) φ = _
  rw [dirac_derivative_formula d 𝕜 Ω a α.val φ]

theorem pointSupport_zero : PointSupportExpected.ZeroRepresentation := by
  intro d 𝕜 _ Ω a m
  unfold pointDerivativeSum
  apply Finset.sum_eq_zero
  intro α _
  exact zero_smul 𝕜 (distributionPartial α.val (pointMass 𝕜 Ω a))

/-- The point mass has the support required in the source. -/
theorem pointMass_support_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) : relativeSupport (pointMass 𝕜 Ω a) ⊆ {a} := by
  intro x hx
  by_contra hxa
  have hxa' : x ≠ a := by simpa using hxa
  let U : Set (Space d) := (Ω : Set (Space d)) ∩ {a}ᶜ
  have hvan : VanishesOn (pointMass 𝕜 Ω a) U := by
    intro φ hφ
    change φ a = 0
    exact image_eq_zero_of_notMem_tsupport (fun ha => (hφ ha).2 (mem_singleton a))
  exact notMem_relativeSupport_of_vanishes _
    (Ω.isOpen.inter isClosed_singleton.isOpen_compl) inter_subset_left hvan
    (show x ∈ U from ⟨hx.1, hxa'⟩) hx

/-- A test with value one at an arbitrary interior point, for either scalar field. -/
theorem exists_test_value_one {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (ha : a ∈ Ω) :
    ∃ φ : TestSpace 𝕜 Ω, φ a = 1 := by
  obtain ⟨χ, _, U, hU, _, hχ⟩ := cutoff d Ω ⟨{a}, isCompact_singleton⟩
    (by simpa using ha)
  refine ⟨TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ, ?_⟩
  change (χ a : 𝕜) = 1
  rw [hχ a (hU (mem_singleton a))]
  simp

/-- In zero dimensions no derivative of positive order is needed. -/
theorem pointSupport_dimensionZero : PointSupportExpected.DimensionZero := by
  intro 𝕜 _ Ω a ha S
  obtain ⟨χ, hχ⟩ := exists_test_value_one 𝕜 Ω a ha
  have hconst (φ : TestSpace 𝕜 Ω) : φ = φ a • χ := by
    ext x
    have hx : x = a := Subsingleton.elim _ _
    subst x
    simp [hχ]
  refine ⟨S χ, ?_, ?_⟩
  · ext φ
    calc
      S φ = S (φ a • χ) := congrArg S (hconst φ)
      _ = φ a * S χ := by simp
      _ = (S χ • pointMass 𝕜 Ω a) φ := by simp [mul_comm]
  · intro c hc
    have h := congrArg (fun T : DistributionSpace 𝕜 Ω => T χ) hc
    simpa [hχ] using h.symm

/-- The multiplicity-vector bridge is injective on the bounded index type. -/
theorem boundedMultiIndex_counts_injective (d m : ℕ) :
    Function.Injective (fun α : BoundedMultiIndex d m => multiIndexCountsEquiv d α.val) := by
  intro α β h
  exact Subtype.ext ((multiIndexCountsEquiv d).injective h)

/-- There is one bounded index for each vector of nonnegative integer
multiplicities of total degree at most m, with no duplication from mixed partials. -/
theorem boundedMultiIndex_coordinate_bridge : PointSupportExpected.MultiIndexBridge := by
  intro d m
  let e : BoundedMultiIndex d m ≃ {v : Fin d → ℕ // ∑ i, v i ≤ m} :=
    (multiIndexCountsEquiv d).subtypeEquiv (fun α => by
      rw [(multiIndexCoordinates d α).2])
  exact ⟨e, fun _ _ => rfl⟩

/-- A finite list of coordinate unit jets is enough for both the coefficient
construction and its uniqueness; these are genuine scalar-linear jet identities. -/
theorem exists_unitJet_family {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (m : ℕ)
    (h : ∀ α : MultiIndex d, α.card ≤ m →
      ∃ φ : TestSpace 𝕜 Ω, ∀ β : MultiIndex d, β.card ≤ m →
        multiPartial φ β a = if β = α then 1 else 0) :
    ∃ b : BoundedMultiIndex d m → TestSpace 𝕜 Ω,
      ∀ α β, testJet 𝕜 Ω a m (b α) β = if β = α then 1 else 0 := by
  classical
  let b : BoundedMultiIndex d m → TestSpace 𝕜 Ω :=
    fun α => Classical.choose (h α.val α.property)
  refine ⟨b, fun α β => ?_⟩
  rw [testJet_apply]
  have hb := Classical.choose_spec (h α.val α.property) β.val β.property
  simpa only [Subtype.ext_iff] using hb

/-- Finite-dimensional reconstruction from annihilation and coordinate unit jets.
The transpose sign is absorbed into the coefficients. -/
theorem representation_of_unitJets {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (m : ℕ) (S : DistributionSpace 𝕜 Ω)
    (hkill : ∀ φ : TestSpace 𝕜 Ω, testJet 𝕜 Ω a m φ = 0 → S φ = 0)
    (b : BoundedMultiIndex d m → TestSpace 𝕜 Ω)
    (hb : ∀ α β, testJet 𝕜 Ω a m (b α) β = if β = α then 1 else 0) :
    ∃ c : BoundedMultiIndex d m → 𝕜, S = pointDerivativeSum Ω a m c := by
  classical
  let c : BoundedMultiIndex d m → 𝕜 := fun α => (-1 : 𝕜) ^ α.val.card * S (b α)
  refine ⟨c, ?_⟩
  ext φ
  let p : TestSpace 𝕜 Ω := ∑ α, testJet 𝕜 Ω a m φ α • b α
  have hp : testJet 𝕜 Ω a m p = testJet 𝕜 Ω a m φ := by
    dsimp only [p]
    rw [map_sum]
    ext β
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hb]
    simp
  have hz : S (φ - p) = 0 := hkill _ (by rw [map_sub, hp, sub_self])
  have heq : S φ = S p := sub_eq_zero.mp (by simpa only [map_sub] using hz)
  rw [heq, pointDerivativeSum_apply]
  change S (∑ α, testJet 𝕜 Ω a m φ α • b α) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [map_smul, testJet_apply]
  change multiPartial φ α.val a * S (b α) =
    ((-1 : 𝕜) ^ α.val.card * S (b α)) *
      ((-1 : 𝕜) ^ α.val.card * multiPartial φ α.val a)
  have hs : (-1 : 𝕜) ^ α.val.card * (-1 : 𝕜) ^ α.val.card = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = 1 * (S (b α) * multiPartial φ α.val a) := by ring
    _ = ((-1 : 𝕜) ^ α.val.card * (-1 : 𝕜) ^ α.val.card) *
        (S (b α) * multiPartial φ α.val a) := by rw [hs]
    _ = _ := by ring

/-- Evaluating on each unit jet separates all distinct multi-index coefficients. -/
theorem coefficients_unique_of_unitJets {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (a : Space d) (m : ℕ)
    (b : BoundedMultiIndex d m → TestSpace 𝕜 Ω)
    (hb : ∀ α β, testJet 𝕜 Ω a m (b α) β = if β = α then 1 else 0)
    (c c' : BoundedMultiIndex d m → 𝕜)
    (h : pointDerivativeSum Ω a m c = pointDerivativeSum Ω a m c') : c = c' := by
  classical
  funext α
  have hpair := congrArg (fun T : DistributionSpace 𝕜 Ω => T (b α)) h
  simp only [pointDerivativeSum_apply, ← testJet_apply] at hpair
  have hc : ∀ v : BoundedMultiIndex d m → 𝕜,
      (∑ β, v β * ((-1 : 𝕜) ^ β.val.card * testJet 𝕜 Ω a m (b α) β)) =
        v α * (-1 : 𝕜) ^ α.val.card := by
    intro v
    simp [hb]
  rw [hc c, hc c'] at hpair
  exact mul_right_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hpair

/-- No representation or uniqueness conclusion is assumed by this assembly. -/
theorem pointSupport_of_finiteJets : PointSupportExpected.Assembly := by
  intro hkill hinterp
  constructor
  · intro d 𝕜 _ Ω a ha S hS
    obtain ⟨m, hm⟩ := hkill d 𝕜 Ω a ha S hS
    obtain ⟨b, hb⟩ := exists_unitJet_family 𝕜 Ω a m (hinterp d 𝕜 Ω a ha m)
    obtain ⟨c, hc⟩ := representation_of_unitJets Ω a m S (fun φ hφ => hm φ (by
      intro α hα
      exact (testJet_apply Ω a m φ ⟨α, hα⟩).symm.trans
        (congrFun hφ ⟨α, hα⟩))) b hb
    exact ⟨m, c, hc⟩
  · intro d 𝕜 _ Ω a ha m c c' h
    obtain ⟨b, hb⟩ := exists_unitJet_family 𝕜 Ω a m (hinterp d 𝕜 Ω a ha m)
    exact coefficients_unique_of_unitJets Ω a m b hb c c' h


/-- One coordinate derivative of a product of one-variable factors. -/
theorem coordinateDerivative_separable {d : ℕ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin d) (x : Space d) :
    fderiv ℝ (fun y : Space d => ∏ i, f i (y i)) x (coordinateVector d j) =
      deriv (f j) (x j) * ∏ i ∈ Finset.univ.erase j, f i (x i) := by
  have h (i : Fin d) : HasFDerivAt (fun y : Space d => f i (y i))
      ((deriv (f i) (x i)) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    convert! ((hf i (x i)).hasDerivAt.comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt) using 1
  rw [(HasFDerivAt.finsetProd (fun i _ => h i)).fderiv]
  simp [coordinateVector, EuclideanSpace.basisFun_apply, mul_comm]

/-- Derivatives of a separated product are indexed by coordinate multiplicities. -/
theorem partialWord_separable {d : ℕ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (l : List (Fin d)) :
    partialWord (fun x : Space d => ∏ i, f i (x i)) l =
      fun x => ∏ i, iteratedDeriv (l.count i) (f i) (x i) := by
  induction l with
  | nil => simp [partialWord]
  | cons j l ih =>
    funext x
    simp only [partialWord, ih]
    rw [coordinateDerivative_separable _
      (fun i => (hf i).differentiable_iteratedDeriv (l.count i) (by exact_mod_cast (ENat.natCast_lt_top (l.count i))))]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    apply congrArg₂ (· * ·)
    · simp [iteratedDeriv_succ]
    · apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [Ne.symm hij]

/-- A normalized one-variable monomial has its sole nonzero jet at its degree. -/
theorem iteratedDeriv_normalizedMonomial (a : ℝ) (n k : ℕ) :
    iteratedDeriv k (fun t : ℝ => (t - a) ^ n / n.factorial) a =
      if k = n then 1 else 0 := by
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp_rw [div_eq_mul_inv]
  rw [iteratedDeriv_mul_const_field]
  rw [show iteratedDeriv k (fun t : ℝ => (t - a) ^ n) =
    fun t => iteratedDeriv k (fun z : ℝ => z ^ n) (t - a) from
      iteratedDeriv_comp_sub_const k (fun z : ℝ => z ^ n) a]
  simp only [sub_self, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp_all

/-- Normalized coordinate monomials separate every distinct multi-index. -/
theorem multiPartial_normalizedMonomial {d : ℕ} (a : Space d) (α β : MultiIndex d) :
    multiPartial (fun x : Space d =>
      ∏ i, (x i - a i) ^ (α.count i) / (α.count i).factorial) β a =
      if β = α then 1 else 0 := by
  classical
  unfold multiPartial
  rw [partialWord_separable (fun i t => (t - a i) ^ (α.count i) / (α.count i).factorial)
    (fun i => (contDiff_id.sub contDiff_const).pow _ |>.div_const _)]
  simp only [iteratedDeriv_normalizedMonomial]
  have hc (i : Fin d) : (β.sort (· ≤ ·)).count i = β.count i :=
    (Multiset.coe_count i (β.sort (· ≤ ·))).symm.trans
      (congrArg (Multiset.count i) (Multiset.sort_eq _ _))
  simp only [hc]
  by_cases h : β = α
  · simp [h]
  · have hi : ∃ i, β.count i ≠ α.count i := by
      by_contra! hn
      exact h (Multiset.ext.mpr hn)
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Real-linear postcomposition commutes with all coordinate derivatives. -/
theorem partialWord_postcomp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (L : ℝ →L[ℝ] 𝕜) {f : Space d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (l : List (Fin d)) :
    partialWord (L ∘ f) l = L ∘ partialWord f l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    funext x
    simp only [partialWord, ih]
    rw [fderiv_comp x L.differentiableAt
      ((partialWord_contDiff hf l).differentiable (by simp)).differentiableAt]
    simp

/-- Every finite unit jet is realized by a test function supported inside Ω. -/
theorem pointSupport_jetInterpolation : PointSupportExpected.JetInterpolation := by
  intro d 𝕜 _ Ω a ha m α _
  classical
  let p : Space d → ℝ := fun x =>
    ∏ i, (x i - a i) ^ (α.count i) / (α.count i).factorial
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := by
    apply contDiff_prod
    intro i _
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.sub contDiff_const).pow _ |>.div_const _
  obtain ⟨χ, _, U, hU, _, hχ⟩ := cutoff d Ω ⟨{a}, isCompact_singleton⟩
    (by simpa using ha)
  let q : TestSpace ℝ Ω := coefficientTestProduct ⟨p, hp.contDiffOn⟩ χ
  let φ : TestSpace 𝕜 Ω :=
    TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) q
  refine ⟨φ, fun β _ => ?_⟩
  have hqp : (q : Space d → ℝ) =ᶠ[𝓝 a] p := by
    filter_upwards [U.isOpen.mem_nhds (hU (mem_singleton a))] with x hx
    change p x * χ x = p x
    rw [hχ x hx, mul_one]
  change partialWord ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ∘ q) (β.sort (· ≤ ·)) a = _
  rw [partialWord_postcomp _ q.contDiff]
  change ((multiPartial q β a : ℝ) : 𝕜) = _
  rw [show multiPartial q β a = multiPartial p β a from
    (partialWord_eventuallyEq hqp _).eq_of_nhds]
  rw [multiPartial_normalizedMonomial]
  split_ifs <;> simp

/-- Fixed-order uniqueness follows directly from the realized unit jets. -/
theorem pointSupport_uniqueness : PointSupportExpected.Uniqueness := by
  intro d 𝕜 _ Ω a ha m c c' h
  obtain ⟨b, hb⟩ := exists_unitJet_family 𝕜 Ω a m
    (pointSupport_jetInterpolation d 𝕜 Ω a ha m)
  exact coefficients_unique_of_unitJets Ω a m b hb c c' h


/-- Vanishing coordinate jets imply vanishing Fréchet derivatives. -/
theorem iteratedFDeriv_eq_zero_of_multiPartial {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a : Space d) (k : ℕ)
    (h : ∀ α : MultiIndex d, α.card = k → multiPartial φ α a = 0) :
    iteratedFDeriv ℝ k φ a = 0 := by
  apply norm_le_zero_iff.mp
  have hb := operatorNormBound d k 𝕜 (iteratedFDeriv ℝ k φ a) 0 le_rfl (fun v => by
    rw [← multiPartial_ofFn hφ v]
    rw [h (List.ofFn v) (by simp)]
    simp)
  simpa using hb

/-- A global Taylor bound obtained by repeated mean-value estimates. -/
theorem norm_iteratedFDeriv_le_of_zeroJet {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : Space d) (N : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖iteratedFDeriv ℝ N f x‖ ≤ M)
    (hz : ∀ k < N, iteratedFDeriv ℝ k f a = 0) :
    ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ M * ‖x - a‖ ^ (N - k) := by
  have H : ∀ r k, k + r = N → ∀ x,
      ‖iteratedFDeriv ℝ k f x‖ ≤ M * ‖x - a‖ ^ r := by
    intro r
    induction r with
    | zero =>
      intro k hk x
      have hkn : k = N := by omega
      subst k
      simpa only [pow_zero, mul_one] using hb x
    | succ r ih =>
      intro k hk x
      have hd : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
        hf.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k)
      have h := Convex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (f := iteratedFDeriv ℝ k f)
        (s := segment ℝ a x) (C := M * ‖x - a‖ ^ r)
        (fun y _ => hd y) (fun y hy => ?_) (convex_segment a x)
        (left_mem_segment ℝ a x) (right_mem_segment ℝ a x)
      · rw [hz k (by omega), sub_zero] at h
        simpa [pow_succ, mul_assoc] using h
      · rw [norm_fderiv_iteratedFDeriv]
        exact (ih (k + 1) (by omega) y).trans (by
          gcongr
          exact norm_sub_le_of_mem_segment hy)
  intro k hk x
  exact H (N - k) k (Nat.add_sub_cancel' hk) x

/-- Exact scaling of derivative norms about a center. -/
theorem norm_iteratedFDeriv_dilation {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {χ : Space d → 𝕜} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (a x : Space d) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => χ (t • (y - a))) x‖ =
      t ^ k * ‖iteratedFDeriv ℝ k χ (t • (x - a))‖ := by
  rw [show (fun y => χ (t • (y - a))) = (fun y => (fun z => χ (t • z)) (y - a)) from rfl,
    iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun z => χ (t • z)) k a x,
    iteratedFDeriv_comp_const_smul t (hχ.of_le (by simp)),
    norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg ht]

/-- A shrinking cutoff times a sufficiently flat function has small derivatives.
The larger vanishing order avoids having to track a separate scale in each
Leibniz term. -/
theorem shrinkingCutoff_derivative_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {χ f : Space d → 𝕜} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : Space d) (m : ℕ)
    (A M R : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hχb : ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ A)
    (hχR : ∀ y ∈ tsupport χ, ‖y‖ ≤ R)
    (hfb : ∀ j ≤ 2 * m + 1, ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ M * ‖x - a‖ ^ (2 * m + 1 - j))
    (t : ℝ) (ht : R ≤ t) (k : ℕ) (hk : k ≤ m) (x : Space d) :
    ‖iteratedFDeriv ℝ k (fun y => χ (t • (y - a)) * f y) x‖ ≤
      2 ^ m * A * M * R ^ (m + 1) / t := by
  have ht1 : 1 ≤ t := hR.trans ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hRt : 0 ≤ R / t := div_nonneg (by linarith) ht0.le
  have hc (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (fun y => χ (t • (y - a))) x‖ ≤ t ^ m * A := by
    rw [norm_iteratedFDeriv_dilation hχ a x t ht0.le i]
    exact mul_le_mul (pow_le_pow_right₀ ht1 hi) (hχb i hi _) (norm_nonneg _) (by positivity)
  have hprod := norm_iteratedFDeriv_mul_le (f := fun y => χ (t • (y - a)))
    (hχ.comp ((contDiff_const_smul t).comp (contDiff_id.sub contDiff_const)))
    hf x (n := k) (by simp)
  by_cases hx : ‖t • (x - a)‖ ≤ R
  · have hxa : ‖x - a‖ ≤ R / t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hx
      exact (le_div_iff₀ ht0).mpr (by nlinarith)
    have hx1 : ‖x - a‖ ≤ 1 := hxa.trans ((div_le_one ht0).mpr ht)
    have hsmall (j : ℕ) (hj : j ≤ m) :
        ‖iteratedFDeriv ℝ j f x‖ ≤ M * (R / t) ^ (m + 1) := by
      apply (hfb j (by omega) x).trans
      apply mul_le_mul_of_nonneg_left _ hM
      exact (pow_le_pow_of_le_one (norm_nonneg _) hx1 (by omega)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hxa _)
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          (t ^ m * A) * (M * (R / t) ^ (m + 1)) := by
        apply hprod.trans
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · exact hc i ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hk)
        · exact hsmall (k - i) ((Nat.sub_le _ _).trans hk)
      _ = 2 ^ k * (t ^ m * A) * (M * (R / t) ^ (m + 1)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
      _ ≤ 2 ^ m * (t ^ m * A) * (M * (R / t) ^ (m + 1)) := by
        gcongr
        norm_num
      _ = _ := by
        rw [div_pow, pow_succ t m]
        field_simp
  · have hy : t • (x - a) ∉ tsupport χ := fun hy => hx (hχR _ hy)
    have hz (i : ℕ) : iteratedFDeriv ℝ i χ (t • (x - a)) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_iteratedFDeriv_subset i h))
    have hzero : ‖iteratedFDeriv ℝ k (fun y => χ (t • (y - a)) * f y) x‖ ≤ 0 := by
      apply hprod.trans
      simp [norm_iteratedFDeriv_dilation hχ a x t ht0.le, hz]
    exact hzero.trans (by positivity)

/-- Point support and finite global order force annihilation of a finite jet. -/
theorem pointSupport_finiteJetAnnihilation : PointSupportExpected.FiniteJetAnnihilation := by
  intro d 𝕜 _ Ω a ha S hS
  obtain ⟨E, _, _, hES, ⟨K, hK, m, C, hC, hbound⟩, _⟩ :=
    compactSupportExtension d 𝕜 Ω S ((finite_singleton a).subset hS).isCompact
  obtain ⟨χr, _, U, hU, _, hχU⟩ := cutoff d ⊤
    ⟨{(0 : Space d)}, isCompact_singleton⟩ (subset_univ _)
  let χ : TestSpace 𝕜 (⊤ : Opens (Space d)) :=
    TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χr
  have hχ1 (x : Space d) (hx : x ∈ U) : χ x = 1 := by
    change (χr x : 𝕜) = 1
    rw [hχU x hx]
    simp
  obtain ⟨R₀, hR₀⟩ := χ.hasCompactSupport.isBounded.exists_norm_le
  let R : ℝ := max R₀ 1
  have hR : 1 ≤ R := le_max_right _ _
  have hχR : ∀ x ∈ tsupport χ, ‖x‖ ≤ R :=
    fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  obtain ⟨A, hA, hχb⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff m
  refine ⟨2 * m, fun φ hφ => ?_⟩
  obtain ⟨M, hM, hfb⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff (2 * m + 1)
  have hflat := norm_iteratedFDeriv_le_of_zeroJet φ.contDiff a (2 * m + 1) M hM
    (hfb _ le_rfl) (fun k hk => iteratedFDeriv_eq_zero_of_multiPartial φ φ.contDiff a k
      (fun α hα => hφ α (by omega)))
  have hχt (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ (t • (y - a))) :=
    χ.contDiff.comp ((contDiff_const_smul t).comp (contDiff_id.sub contDiff_const))
  let ψ (t : ℝ) : TestSpace 𝕜 Ω :=
    coefficientTestProduct ⟨fun y => χ (t • (y - a)), (hχt t).contDiffOn⟩ φ
  have hpair (t : ℝ) : S (ψ t) = S φ := by
    let V : Set (Space d) := (fun y => t • (y - a)) ⁻¹' (U : Set (Space d))
    have hVo : IsOpen V := U.isOpen.preimage (by fun_prop)
    apply supportLocality d 𝕜 Ω S (ψ t) φ V hVo
      (hS.trans (singleton_subset_iff.mpr (by simpa [V] using hU (mem_singleton 0))))
    intro x hx
    change χ (t • (x - a)) * φ x = φ x
    rw [hχ1 _ hx, one_mul]
  let D : ℝ := 2 ^ m * A * M * R ^ (m + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖S φ‖ ≤ C * (D / t) := by
    filter_upwards [eventually_ge_atTop R] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (hR.trans ht)
    calc
      ‖S φ‖ = ‖E (testToSmooth 𝕜 (ψ t))‖ := by rw [hES, hpair]
      _ ≤ C * smoothSeminorm 𝕜 K hK m (testToSmooth 𝕜 (ψ t)) := hbound _
      _ ≤ C * (D / t) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply (smoothSeminorm_le_iff K hK m _ (D / t) (div_nonneg hD ht0.le)).mpr
        intro k hk v x _
        apply (coordinateEvaluationBound d k 𝕜 _ v).trans
        exact shrinkingCutoff_derivative_bound χ.contDiff φ.contDiff a m A M R
          hA hM hR hχb hχR hflat t ht k hk x
  have hlim : Tendsto (fun t : ℝ => C * (D / t)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.const_mul D).const_mul C
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hsmall)

/-- Every point-supported distribution is a finite sum of Dirac derivatives. -/
theorem pointSupport_representation : PointSupportExpected.Representation :=
  (pointSupport_of_finiteJets pointSupport_finiteJetAnnihilation
    pointSupport_jetInterpolation).1

end P102.U4
