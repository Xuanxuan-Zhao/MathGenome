import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.EuclideanSard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.SardNonzeroRankStep
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.SardVanishingLayerStep
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.SardFlatJetNull
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Set MeasureTheory

namespace SmoothManifolds.Ch04

/-- Maps to the zero-dimensional vector space have no critical points. -/
theorem criticalSet_target_zero {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin 0 → ℝ)) : criticalSet U f = ∅ := by
  ext x
  simp only [criticalSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro _ h
  apply h
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The Sard conclusion for target dimension zero uses counting measure correctly. -/
theorem euclideanSard_target_zero {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin 0 → ℝ)) :
    volume (f '' criticalSet U f) = 0 := by
  simp [criticalSet_target_zero]

/-- The empty domain has empty critical image, in all dimensions. -/
theorem euclideanSard_empty {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ)) :
    volume (f '' criticalSet ∅ f) = 0 := by
  simp [criticalSet]

/-- For an endomorphism, non-surjectivity is exactly determinant zero. -/
private theorem det_eq_zero_of_not_surjective {m : ℕ}
    (A : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))
    (hA : ¬ Function.Surjective A) : A.det = 0 := by
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot,
    ne_eq, LinearMap.ker_eq_bot, LinearMap.injective_iff_surjective]
  exact hA

/-- Equal-dimensional Sard follows already from differentiability on the open domain. -/
theorem euclideanSard_same_dimension {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) :
    volume (f '' criticalSet U f) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun x => fderiv ℝ f x)
  · intro x hx
    exact ((hf x hx.1).differentiableAt (hU.mem_nhds hx.1)).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact det_eq_zero_of_not_surjective _ hx.2

/-- A zero-dimensional source has at most one image point. -/
theorem euclideanSard_source_zero : EuclideanSardIn 0 := by
  intro n U f hU hf
  cases n with
  | zero => exact euclideanSard_target_zero U f
  | succ n => exact ((Set.to_countable (criticalSet U f)).image f).measure_zero volume

/-- A map from a smaller vector space cannot have a surjective derivative. -/
theorem criticalSet_of_dimension_lt {m n : ℕ} (hmn : m < n)
    (U : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → (Fin n → ℝ)) :
    criticalSet U f = U := by
  ext x
  simp only [criticalSet, mem_ofPred_eq, and_iff_left_iff_imp]
  intro _ hsurj
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv ℝ f x).toLinearMap) hsurj
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- A differentiable map from lower-dimensional Euclidean space has null image.
Lift it by a coordinate projection to an endomorphism and apply the Jacobian lemma. -/
theorem euclidean_image_null_of_dimension_lt {m n : ℕ} (hmn : m < n)
    (U : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) : volume (f '' U) = 0 := by
  let P : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castLE hmn.le i)
  have hP : Function.Surjective P := (Fin.castLE_injective hmn.le).surjective_comp_right
  have hnull : volume ((f ∘ P) '' (P ⁻¹' U)) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => (fderiv ℝ f (P x)).comp P)
    · intro x hx
      exact (((hf (P x) hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.comp x
        P.hasFDerivAt).hasFDerivWithinAt
    · intro x hx
      apply det_eq_zero_of_not_surjective
      intro hsurj
      have hsurj' : Function.Surjective (fderiv ℝ f (P x)) := by
        intro y
        obtain ⟨z, hz⟩ := hsurj y
        exact ⟨P z, hz⟩
      have hdim := LinearMap.finrank_le_finrank_of_surjective
        (f := (fderiv ℝ f (P x)).toLinearMap) hsurj'
      simp only [Module.finrank_pi, Fintype.card_fin] at hdim
      omega
  convert hnull using 2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hP x
    exact ⟨z, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨P x, hx, rfl⟩

/-- The source's set `B_j`, expressed using the actual higher Fréchet derivatives. -/
def vanishingJets {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (j : ℕ) : Set (Fin m → ℝ) :=
  {x | x ∈ U ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i f x = 0}

/-- At first order the vanishing-jet condition is exactly vanishing of the derivative. -/
theorem mem_vanishingJets_one_iff {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ) :
    x ∈ vanishingJets U f 1 ↔ x ∈ U ∧ fderiv ℝ f x = 0 := by
  have hone : iteratedFDeriv ℝ 1 f x = 0 ↔ fderiv ℝ f x = 0 := by
    rw [← norm_eq_zero, norm_iteratedFDeriv_one, norm_eq_zero]
  simp only [vanishingJets, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, hone.mp (h 1 le_rfl le_rfl)⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i hi hi' => ?_⟩
    obtain rfl : i = 1 := by omega
    exact hone.mpr h

/-- Null successive layers and a null terminal set imply nullity of `B_1`. -/
theorem vanishingJets_null_descend {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (k : ℕ) :
    volume (f '' vanishingJets U f (k + 1)) = 0 →
    (∀ j : ℕ, 1 ≤ j → j ≤ k →
      volume (f '' (vanishingJets U f j \ vanishingJets U f (j + 1))) = 0) →
    volume (f '' vanishingJets U f 1) = 0 := by
  induction k with
  | zero => intro htail _; exact htail
  | succ k ih =>
    intro htail hlayers
    apply ih
    · have hcover : vanishingJets U f (k + 1) ⊆
          (vanishingJets U f (k + 1) \ vanishingJets U f (k + 2)) ∪
            vanishingJets U f (k + 2) := by
        intro x hx
        by_cases h : x ∈ vanishingJets U f (k + 2)
        · exact Or.inr h
        · exact Or.inl ⟨hx, h⟩
      apply measure_mono_null (image_mono hcover)
      rw [image_union]
      exact measure_union_null (hlayers (k + 1) (by omega) le_rfl) htail
    · intro j hj hk
      exact hlayers j hj (by omega)

/-- Assemble the two parts of the critical set without any measurability assumption. -/
theorem critical_image_null_of_parts {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hoff : volume (f '' (criticalSet U f \ vanishingJets U f 1)) = 0)
    (hflat : volume (f '' vanishingJets U f 1) = 0) :
    volume (f '' criticalSet U f) = 0 := by
  have hcover : criticalSet U f ⊆
      (criticalSet U f \ vanishingJets U f 1) ∪ vanishingJets U f 1 := by
    intro x hx
    by_cases h : x ∈ vanishingJets U f 1
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  apply measure_mono_null (image_mono hcover)
  rw [image_union]
  exact measure_union_null hoff hflat

/-- The full Euclidean theorem, by induction on source dimension and decomposition
into the nonzero-derivative stratum, vanishing-jet layers, and a flat-jet tail. -/
theorem euclidean_sard : EuclideanSardSpecs.smoothSard := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro n U f hU hf
    by_cases hn : n = 0
    · subst n
      exact euclideanSard_target_zero U f
    by_cases hm : m = 0
    · subst m
      exact euclideanSard_source_zero n U f hU hf
    by_cases hmn : m ≤ n
    · rcases hmn.eq_or_lt with heq | hlt
      · subst n
        exact euclideanSard_same_dimension U f hU (hf.differentiableOn (by simp))
      · rw [criticalSet_of_dimension_lt hlt]
        exact euclidean_image_null_of_dimension_lt hlt U f hU
          (hf.differentiableOn (by simp))
    have hoff : volume (f '' (criticalSet U f \ vanishingJets U f 1)) = 0 := by
      have hstep := SardNonzeroRank.nonzeroRankStep m n (by omega) (by omega)
        U f hU hf (ih (m - 1) (by omega))
      apply measure_mono_null (image_mono ?_) hstep
      intro x hx
      refine ⟨hx.1.1, hx.1.2, ?_⟩
      intro hzero
      exact hx.2 ((mem_vanishingJets_one_iff U f x).mpr ⟨hx.1.1, hzero⟩)
    have hlayers : ∀ j : ℕ, 1 ≤ j → j ≤ m →
        volume (f '' (vanishingJets U f j \ vanishingJets U f (j + 1))) = 0 := by
      intro j hj _hjm
      exact SardVanishingLayer.vanishing_layer m n j (by omega) (by omega) hj
        U f hU hf (ih (m - 1) (by omega))
    have htail : volume (f '' vanishingJets U f (m + 1)) = 0 := by
      exact SardFlatJet.flat_jet_image_null m n (m + 1) (by omega)
        (by nlinarith [show 1 ≤ n by omega]) U f hU hf
    exact critical_image_null_of_parts U f hoff
      (vanishingJets_null_descend U f m htail hlayers)

end SmoothManifolds.Ch04
