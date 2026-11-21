import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products

/-! Proper oriented and finite-dimensional Darboux integration.
The proofs use restriction and splitting of the accepted Darboux integral.
Euclidean norm integrability follows from scalar norm integrability, products,
finite sums and continuous square root. The norm inequality is obtained by
passing the finite tagged-sum triangle inequality to its common limit. -/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators
namespace O
export Specs.SingleVariableAnalysis.Ch08.Oriented
  (realIntegrableValue realIntegralValue complexIntegrableValue complexIntegralValue
   realVectorIntegrableValue realVectorIntegralValue
   complexVectorIntegrableValue complexVectorIntegralValue)
end O

abbrev OrientedRealIntegrable := O.realIntegrableValue
noncomputable abbrev orientedRealIntegral := @O.realIntegralValue
abbrev OrientedRealVectorIntegrable := O.realVectorIntegrableValue
noncomputable abbrev orientedRealVectorIntegral := @O.realVectorIntegralValue

abbrev OrientedComplexIntegrable := O.complexIntegrableValue
noncomputable abbrev orientedComplexIntegral := @O.complexIntegralValue
abbrev OrientedComplexVectorIntegrable := O.complexVectorIntegrableValue
noncomputable abbrev orientedComplexVectorIntegral := @O.complexVectorIntegralValue

/-- The algebraic sorting argument includes coincident endpoints. -/
theorem ordered_cocycle {α E : Type*} [LinearOrder α] [AddCommGroup E]
    (J : α → α → E) (hs : ∀ x y, J x y = -J y x)
    (ha : ∀ x y z, x ≤ y → y ≤ z → J x y + J y z = J x z)
    (a b c : α) : J a b + J b c = J a c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ha a b c hab hbc
    · rcases le_total a c with hac | hca
      · rw [← ha a c b hac hcb, hs b c]
        abel
      · rw [hs a c, hs b c, ← ha c a b hca hab]
        abel
  · rcases le_total a c with hac | hca
    · rw [hs a b, ← ha b a c hba hac]
      abel
    · rcases le_total b c with hbc | hcb
      · rw [hs a b, hs a c, ← ha b c a hbc hca]
        abel
      · rw [hs a b, hs b c, hs a c, ← ha c b a hcb hba]
        abel

theorem RealIntegrable.subinterval {f : ℝ → ℝ} {L U a b : ℝ}
    (h : RealIntegrable f L U) (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U) :
    RealIntegrable f a b := by
  have hr := ((real_split f hLa (hab.trans hbU) h.bounded).1.mp h).2
  exact ((real_split f hab hbU (RealIntegrable.bounded hr)).1.mp hr).1

theorem ComplexIntegrable.subinterval {f : ℝ → ℂ} {L U a b : ℝ}
    (h : ComplexIntegrable f L U) (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U) :
    ComplexIntegrable f a b :=
  ⟨RealIntegrable.subinterval h.1 hLa hab hbU, RealIntegrable.subinterval h.2 hLa hab hbU⟩

theorem oriented_real_agreement : Specs.SingleVariableAnalysis.Ch08.Oriented.realAgreement := by
  intro f a b hab h ho
  simp only [O.realIntegralValue, ite_eq_left hab, min_eq_left hab, max_eq_right hab]

theorem oriented_real_degenerate : Specs.SingleVariableAnalysis.Ch08.Oriented.realDegenerate := by
  intro f a
  have ho : RealIntegrable f a a := realIntegrable_degenerate f a
  have h : OrientedRealIntegrable f a a := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue] using ho
  refine ⟨h, ?_⟩
  rw [oriented_real_agreement f le_rfl h ho]
  exact realIntegral_degenerate f a ho

theorem oriented_real_symmetry : Specs.SingleVariableAnalysis.Ch08.Oriented.realSymmetry := by
  intro f a b h hr
  by_cases hab : a ≤ b
  · by_cases hba : b ≤ a
    · obtain rfl := le_antisymm hab hba
      have hz := (oriented_real_degenerate f a).choose_spec
      simp only [show O.realIntegralValue f h = 0 from hz, neg_zero]
    · simp [O.realIntegralValue, hab, hba]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [O.realIntegralValue, hab, hba]

theorem oriented_real_integrable_of_mem {f : ℝ → ℝ} {L U a b : ℝ}
    (h : RealIntegrable f L U) (ha : a ∈ Set.Icc L U) (hb : b ∈ Set.Icc L U) :
    OrientedRealIntegrable f a b :=
  RealIntegrable.subinterval h (le_min ha.1 hb.1) min_le_max (max_le ha.2 hb.2)

theorem oriented_real_ordered_add {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : OrientedRealIntegrable f a b) (h2 : OrientedRealIntegrable f b c)
    (h3 : OrientedRealIntegrable f a c) :
    orientedRealIntegral f h1 + orientedRealIntegral f h2 = orientedRealIntegral f h3 := by
  have h1' : RealIntegrable f a b := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_left hab, max_eq_right hab] using h1
  have h2' : RealIntegrable f b c := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_left hbc, max_eq_right hbc] using h2
  have h3' : RealIntegrable f a c := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_left (hab.trans hbc), max_eq_right (hab.trans hbc)] using h3
  change O.realIntegralValue f h1 + O.realIntegralValue f h2 = O.realIntegralValue f h3
  rw [oriented_real_agreement f hab h1 h1', oriented_real_agreement f hbc h2 h2',
    oriented_real_agreement f (hab.trans hbc) h3 h3']
  exact ((real_split f hab hbc h3'.bounded).2 h3' h1' h2').symm

theorem oriented_real_additivity : Specs.SingleVariableAnalysis.Ch08.Oriented.realAdditivity := by
  intro f a b c h
  let L := min a (min b c)
  let U := max a (max b c)
  have ha : a ∈ Set.Icc L U := ⟨min_le_left _ _, le_max_left _ _⟩
  have hb : b ∈ Set.Icc L U := ⟨(min_le_right _ _).trans (min_le_left _ _),
    (le_max_left _ _).trans (le_max_right _ _)⟩
  have hc : c ∈ Set.Icc L U := ⟨(min_le_right _ _).trans (min_le_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩
  let H (x y : Set.Icc L U) := oriented_real_integrable_of_mem h x.property y.property
  let J (x y : Set.Icc L U) := orientedRealIntegral f (H x y)
  refine ⟨H ⟨a, ha⟩ ⟨b, hb⟩, H ⟨b, hb⟩ ⟨c, hc⟩, H ⟨a, ha⟩ ⟨c, hc⟩, ?_⟩
  exact ordered_cocycle J (fun x y => oriented_real_symmetry f x y (H x y) (H y x))
    (fun x y z hxy hyz => oriented_real_ordered_add hxy hyz (H x y) (H y z) (H x z))
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩

theorem oriented_real_norm_estimate : Specs.SingleVariableAnalysis.Ch08.Oriented.realNormEstimate := by
  intro f a b h
  obtain ⟨hn, hbound, _⟩ := real_norm_estimate f h
  refine ⟨hn, ?_⟩
  unfold O.realIntegralValue
  split <;> simpa only [norm_neg] using hbound

theorem oriented_complex_agreement : Specs.SingleVariableAnalysis.Ch08.Oriented.complexAgreement := by
  intro f a b hab h ho
  simp only [O.complexIntegralValue, ite_eq_left hab, min_eq_left hab, max_eq_right hab]

theorem oriented_complex_degenerate : Specs.SingleVariableAnalysis.Ch08.Oriented.complexDegenerate := by
  intro f a
  have ho : ComplexIntegrable f a a := ⟨realIntegrable_degenerate _ a, realIntegrable_degenerate _ a⟩
  have h : OrientedComplexIntegrable f a a := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue] using ho
  refine ⟨h, ?_⟩
  rw [oriented_complex_agreement f le_rfl h ho]
  apply Complex.ext
  · exact (complexIntegral_components f ho).1.trans (realIntegral_degenerate _ a ho.1)
  · exact (complexIntegral_components f ho).2.trans (realIntegral_degenerate _ a ho.2)

theorem oriented_complex_symmetry : Specs.SingleVariableAnalysis.Ch08.Oriented.complexSymmetry := by
  intro f a b h hr
  by_cases hab : a ≤ b
  · by_cases hba : b ≤ a
    · obtain rfl := le_antisymm hab hba
      have hz := (oriented_complex_degenerate f a).choose_spec
      simp only [show O.complexIntegralValue f h = 0 from hz, neg_zero]
    · simp [O.complexIntegralValue, hab, hba]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [O.complexIntegralValue, hab, hba]

theorem oriented_complex_integrable_of_mem {f : ℝ → ℂ} {L U a b : ℝ}
    (h : ComplexIntegrable f L U) (ha : a ∈ Set.Icc L U) (hb : b ∈ Set.Icc L U) :
    OrientedComplexIntegrable f a b :=
  ComplexIntegrable.subinterval h (le_min ha.1 hb.1) min_le_max (max_le ha.2 hb.2)

theorem oriented_complex_ordered_add {f : ℝ → ℂ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : OrientedComplexIntegrable f a b) (h2 : OrientedComplexIntegrable f b c)
    (h3 : OrientedComplexIntegrable f a c) :
    orientedComplexIntegral f h1 + orientedComplexIntegral f h2 = orientedComplexIntegral f h3 := by
  have h1' : ComplexIntegrable f a b := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_left hab, max_eq_right hab] using h1
  have h2' : ComplexIntegrable f b c := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_left hbc, max_eq_right hbc] using h2
  have h3' : ComplexIntegrable f a c := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_left (hab.trans hbc), max_eq_right (hab.trans hbc)] using h3
  change O.complexIntegralValue f h1 + O.complexIntegralValue f h2 = O.complexIntegralValue f h3
  rw [oriented_complex_agreement f hab h1 h1', oriented_complex_agreement f hbc h2 h2',
    oriented_complex_agreement f (hab.trans hbc) h3 h3']
  exact ((complex_split f hab hbc h3'.norm_bound).2 h3' h1' h2').symm

theorem oriented_complex_additivity : Specs.SingleVariableAnalysis.Ch08.Oriented.complexAdditivity := by
  intro f a b c h
  let L := min a (min b c)
  let U := max a (max b c)
  have ha : a ∈ Set.Icc L U := ⟨min_le_left _ _, le_max_left _ _⟩
  have hb : b ∈ Set.Icc L U := ⟨(min_le_right _ _).trans (min_le_left _ _),
    (le_max_left _ _).trans (le_max_right _ _)⟩
  have hc : c ∈ Set.Icc L U := ⟨(min_le_right _ _).trans (min_le_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩
  let H (x y : Set.Icc L U) := oriented_complex_integrable_of_mem h x.property y.property
  let J (x y : Set.Icc L U) := orientedComplexIntegral f (H x y)
  refine ⟨H ⟨a, ha⟩ ⟨b, hb⟩, H ⟨b, hb⟩ ⟨c, hc⟩, H ⟨a, ha⟩ ⟨c, hc⟩, ?_⟩
  exact ordered_cocycle J (fun x y => oriented_complex_symmetry f x y (H x y) (H y x))
    (fun x y z hxy hyz => oriented_complex_ordered_add hxy hyz (H x y) (H y z) (H x z))
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩

theorem oriented_complex_norm_estimate : Specs.SingleVariableAnalysis.Ch08.Oriented.complexNormEstimate := by
  intro f a b h
  obtain ⟨hn, hbound, _⟩ := complex_norm_estimate f h
  refine ⟨hn, ?_⟩
  unfold O.complexIntegralValue
  split <;> simpa only [norm_neg] using hbound

/-- Finite sums preserve the unrestricted fine-tagged limit. -/
theorem FineTaggedLimit.sum {ι E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (s : Finset ι) {f : ι → ℝ → E} {I : ι → E} {a b : ℝ}
    (hf : ∀ j ∈ s, FineTaggedLimit (f j) a b (I j)) :
    FineTaggedLimit (fun x => ∑ j ∈ s, f j x) a b (∑ j ∈ s, I j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FineTaggedLimit.zero (E := E) a b
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (hf j (Finset.mem_insert_self j s)).add (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- Evaluation of a finite Euclidean sum is componentwise. -/
theorem euclidean_sum_apply {K : Type*} [RCLike K] {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → EuclideanSpace K (Fin n)) (j : Fin n) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  change (WithLp.ofLp (∑ i ∈ s, f i)) j = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

/-- Embedding one scalar coordinate is an isometry for the Euclidean norm. -/
theorem FineTaggedLimit.euclidean_single {K : Type*} [RCLike K] {n : ℕ}
    {f : ℝ → K} {I : K} {a b : ℝ} (hf : FineTaggedLimit f a b I) (j : Fin n) :
    FineTaggedLimit (fun x => EuclideanSpace.single j (f x)) a b
      (EuclideanSpace.single j I) := by
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hf ε hε
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  have he : taggedSum P ξ (fun x => EuclideanSpace.single j (f x)) =
      EuclideanSpace.single j (taggedSum P ξ f) := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [taggedSum, S.sumValue, euclidean_sum_apply]
    · simp [taggedSum, S.sumValue, euclidean_sum_apply, PiLp.smul_apply, hk]
  change ‖taggedSum P ξ (fun x => EuclideanSpace.single j (f x)) - EuclideanSpace.single j I‖ < ε
  rw [he, ← PiLp.single_sub, PiLp.norm_single]
  exact hc P ξ hP

/-- The componentwise limit is the Euclidean limit, in every finite dimension. -/
theorem FineTaggedLimit.euclidean {K : Type*} [RCLike K] {n : ℕ}
    {f : ℝ → EuclideanSpace K (Fin n)} {I : EuclideanSpace K (Fin n)} {a b : ℝ}
    (hf : ∀ j, FineTaggedLimit (fun x => f x j) a b (I j)) :
    FineTaggedLimit f a b I := by
  have hs := FineTaggedLimit.sum Finset.univ (fun j _ => (hf j).euclidean_single j)
  have he (v : EuclideanSpace K (Fin n)) : (∑ j, EuclideanSpace.single j (v j)) = v := by
    ext k
    simp [euclidean_sum_apply, PiLp.single_apply]
  simpa only [he] using hs

/-- Finite sums of real integrable functions, including the empty sum. -/
theorem realIntegrable_fin_sum {n : ℕ} {f : Fin n → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ j, RealIntegrable (f j) a b) :
    RealIntegrable (fun x => ∑ j, f j x) a b := by
  simpa only [one_mul] using
    (real_finite_linearity n (fun _ => 1) f hab hf).choose

/-- Scalar coordinate norms suffice for integrability of a Euclidean norm.
The square root is applied on a bounded real range; no continuity of f is used. -/
theorem euclidean_norm_integrable {K : Type*} [RCLike K] {n : ℕ}
    {f : ℝ → EuclideanSpace K (Fin n)} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ j, RealIntegrable (fun x => ‖f x j‖) a b) :
    RealIntegrable (fun x => ‖f x‖) a b := by
  have hs := realIntegrable_fin_sum hab (fun j => real_product (hf j) (hf j))
  obtain ⟨M, hM⟩ := (RealIntegrable.bounded hs).abs_bound
  have hr : ∀ x ∈ Set.Icc a b, (∑ j, ‖f x j‖ * ‖f x j‖) ∈ Set.Icc (-M) M := by
    intro x hx
    exact abs_le.mp (hM x hx)
  have hc := real_composition hs Real.continuous_sqrt.continuousOn hr
  simpa only [PiLp.norm_eq_of_L2, pow_two] using hc

theorem oriented_real_vector_components :
    Specs.SingleVariableAnalysis.Ch08.Oriented.realVectorComponents := by
  intro n f a b h j
  rfl

theorem oriented_real_vector_symmetry :
    Specs.SingleVariableAnalysis.Ch08.Oriented.realVectorSymmetry := by
  intro n f a b h hr
  ext j
  exact oriented_real_symmetry (fun x => f x j) a b (h j) (hr j)

theorem oriented_real_vector_degenerate :
    Specs.SingleVariableAnalysis.Ch08.Oriented.realVectorDegenerate := by
  intro n f a
  let H := fun j => (oriented_real_degenerate (fun x => f x j) a).choose
  refine ⟨H, ?_⟩
  ext j
  exact (oriented_real_degenerate (fun x => f x j) a).choose_spec

theorem oriented_real_vector_additivity :
    Specs.SingleVariableAnalysis.Ch08.Oriented.realVectorAdditivity := by
  intro n f a b c h
  have hLU : min a (min b c) ≤ max a (max b c) :=
    (min_le_left _ _).trans (le_max_left _ _)
  have H (j : Fin n) := oriented_real_additivity (fun x => f x j) a b c
    (by simpa [O.realIntegrableValue, min_eq_left hLU, max_eq_right hLU] using h j)
  refine ⟨fun j => (H j).choose, fun j => (H j).choose_spec.choose,
    fun j => (H j).choose_spec.choose_spec.choose, ?_⟩
  ext j
  exact (H j).choose_spec.choose_spec.choose_spec

theorem oriented_complex_vector_components :
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexVectorComponents := by
  intro n f a b h j
  rfl

theorem oriented_complex_vector_symmetry :
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexVectorSymmetry := by
  intro n f a b h hr
  ext j
  exact oriented_complex_symmetry (fun x => f x j) a b (h j) (hr j)

theorem oriented_complex_vector_degenerate :
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexVectorDegenerate := by
  intro n f a
  let H := fun j => (oriented_complex_degenerate (fun x => f x j) a).choose
  refine ⟨H, ?_⟩
  ext j
  exact (oriented_complex_degenerate (fun x => f x j) a).choose_spec

theorem oriented_complex_vector_additivity :
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexVectorAdditivity := by
  intro n f a b c h
  have hLU : min a (min b c) ≤ max a (max b c) :=
    (min_le_left _ _).trans (le_max_left _ _)
  have H (j : Fin n) := oriented_complex_additivity (fun x => f x j) a b c
    (by simpa [O.complexIntegrableValue, min_eq_left hLU, max_eq_right hLU] using h j)
  refine ⟨fun j => (H j).choose, fun j => (H j).choose_spec.choose,
    fun j => (H j).choose_spec.choose_spec.choose, ?_⟩
  ext j
  exact (H j).choose_spec.choose_spec.choose_spec

theorem oriented_real_vector_norm_estimate :
    Specs.SingleVariableAnalysis.Ch08.Oriented.realVectorNormEstimate := by
  intro n f a b h
  let J : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2
    (fun j => realIntegral (fun x => f x j) (h j))
  have hn : RealIntegrable (fun x => ‖f x‖) (min a b) (max a b) :=
    euclidean_norm_integrable min_le_max (fun j => RealIntegrable.norm (h j))
  have hlim : FineTaggedLimit f (min a b) (max a b) J := by
    apply FineTaggedLimit.euclidean
    intro j
    exact (real_tagged_equivalence _ min_le_max (RealIntegrable.bounded (h j)) _).mp ⟨h j, rfl⟩
  have hnlim : FineTaggedLimit (fun x => ‖f x‖) (min a b) (max a b)
      (realIntegral _ hn) :=
    (real_tagged_equivalence _ min_le_max (RealIntegrable.bounded hn) _).mp ⟨hn, rfl⟩
  have hb := hlim.norm_le min_le_max hnlim
  refine ⟨hn, ?_⟩
  by_cases hab : a ≤ b
  · have he : O.realVectorIntegralValue n f h = J := by
      ext j
      simp [O.realVectorIntegralValue, O.realIntegralValue, hab, J]
    rw [he]
    exact hb
  · have he : O.realVectorIntegralValue n f h = -J := by
      ext j
      simp [O.realVectorIntegralValue, O.realIntegralValue, hab, J]
    rw [he, norm_neg]
    exact hb

theorem oriented_complex_vector_norm_estimate :
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexVectorNormEstimate := by
  intro n f a b h
  let J : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2
    (fun j => complexIntegral (fun x => f x j) (h j))
  have hn : RealIntegrable (fun x => ‖f x‖) (min a b) (max a b) :=
    euclidean_norm_integrable min_le_max (fun j => ComplexIntegrable.norm (h j))
  have hlim : FineTaggedLimit f (min a b) (max a b) J := by
    apply FineTaggedLimit.euclidean
    intro j
    exact (complex_tagged_equivalence _ min_le_max (ComplexIntegrable.norm_bound (h j)) _).mp ⟨h j, rfl⟩
  have hnlim : FineTaggedLimit (fun x => ‖f x‖) (min a b) (max a b)
      (realIntegral _ hn) :=
    (real_tagged_equivalence _ min_le_max (RealIntegrable.bounded hn) _).mp ⟨hn, rfl⟩
  have hb := hlim.norm_le min_le_max hnlim
  refine ⟨hn, ?_⟩
  by_cases hab : a ≤ b
  · have he : O.complexVectorIntegralValue n f h = J := by
      ext j
      simp [O.complexVectorIntegralValue, O.complexIntegralValue, hab, J]
    rw [he]
    exact hb
  · have he : O.complexVectorIntegralValue n f h = -J := by
      ext j
      simp [O.complexVectorIntegralValue, O.complexIntegralValue, hab, J]
    rw [he, norm_neg]
    exact hb

end SingleVariableAnalysis.Riemann
