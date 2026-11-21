import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormLowRanks
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalLowRank
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsOrthogonal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsSymplectic
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsTypeA
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.IntervalCases

/-! The real low-rank comparisons in LA-J07. The classical complex
isomorphisms and the negative index of the real Killing form identify the
matrix models in the smaller ranks. The nonsimple D₂ classification
descends the two simple factors of the complex matrix algebra. -/

noncomputable section

open scoped TensorProduct
open LieAlgebra Matrix
open Specs.LieAlgebrasAndRepresentations.RealFormLowRanks
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.RealFormsTypeA (Blocks SL quaternionicSL)

namespace LieAlgebrasAndRepresentations.RealFormLowRanks

open RealForms RealFormsOrthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

open private typeBEquiv typeDEquiv from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
open private reindexSo reindexSo_commutes from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsOrthogonal
open private killing_real_skew_neg from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
open private blockFixed_finrank compact_model_unique reindexSL_intertwines
  split_model_with_compact quaternionic_model_with_compact sp_finrank_twice
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsTypeA

private theorem coefficientCompact {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : 2 < Fintype.card ι) : IsCompact (coefficientConjugation ι) := by
  let e := Fintype.equivFin ι
  obtain ⟨f, _⟩ := restrict_complex_isomorphism _ _ (reindexSo e) (reindexSo_commutes e)
  obtain ⟨g, _⟩ := OrthogonalCompactGeometry.coefficient_fixed (Fintype.card ι)
  intro X hX
  let j := f.trans g.symm
  rw [← killingForm_of_equiv_apply j]
  apply killing_real_skew_neg (by simpa using h)
  intro hz
  apply hX
  apply j.injective
  rw [map_zero]
  exact hz

private def negativeIndex (A : Type*) [LieRing A] [LieAlgebra ℝ A] : ℕ :=
  sigNeg (killingQuadratic A)

private theorem negativeIndex_eq {A B : Type*} [LieRing A] [LieAlgebra ℝ A]
    [LieRing B] [LieAlgebra ℝ B] (e : A ≃ₗ⁅ℝ⁆ B) :
    negativeIndex A = negativeIndex B := by
  apply QuadraticMap.Equivalent.sigNeg_eq
  exact ⟨{ e.toLinearEquiv with
    map_app' x := killingForm_of_equiv_apply e x x }⟩

private theorem signatureIndex (p q : ℕ) (h : 2 < p + q) :
    negativeIndex (soSignature p q) = p * (p - 1) / 2 + q * (q - 1) / 2 := by
  obtain ⟨e⟩ := signature_model p q
  obtain ⟨f⟩ := signature_compact p q
  let D := signatureMatrix p q
  have hk := CartanDecompositionSignature.killing_indices
    (coefficientConjugation (Fin p ⊕ Fin q)) (orthogonalAction D (signature_orthogonal p q))
    (orthogonalAction_commutes (signature_orthogonal p q))
    (orthogonalAction_involutive (signature_orthogonal p q) (Or.inl (signature_square p q)))
    (coefficientCompact (by simpa using h))
  exact (negativeIndex_eq e).trans (hk.1.trans
    (f.toLinearEquiv.finrank_eq.trans (OrthogonalCompactGeometry.signed_dimensions p q).1))

private theorem starIndex (n : ℕ) (h : 2 < n + n) :
    negativeIndex (soStar n) = n ^ 2 := by
  obtain ⟨f⟩ := quaternionic_compact n
  let J := quaternionicMatrix n
  have hk := CartanDecompositionSignature.killing_indices
    (coefficientConjugation (Fin n ⊕ Fin n)) (orthogonalAction J (quaternionic_orthogonal n))
    (orthogonalAction_commutes (quaternionic_orthogonal n))
    (orthogonalAction_involutive (quaternionic_orthogonal n) (Or.inr (quaternionic_square n)))
    (coefficientCompact (by simpa using h))
  exact hk.1.trans (f.toLinearEquiv.finrank_eq.trans
    (OrthogonalCompactGeometry.general_linear_dimensions ℂ n).1)

private theorem signatureComplexification (p q N : ℕ) (h : p + q = N) :
    Nonempty ((ℂ ⊗[ℝ] soSignature p q) ≃ₗ⁅ℂ⁆ so (Fin N)) := by
  obtain ⟨e⟩ := signature_model p q
  obtain ⟨f, _⟩ := fixed_complexification (signatureConjugation p q)
  exact ⟨(complexifyEquiv e).trans (f.trans (reindexSo (finSumFinEquiv.trans (finCongr h))))⟩

private theorem starComplexification (n N : ℕ) (h : n + n = N) :
    Nonempty ((ℂ ⊗[ℝ] soStar n) ≃ₗ⁅ℂ⁆ so (Fin N)) := by
  obtain ⟨e, _⟩ := fixed_complexification (quaternionicConjugation n)
  exact ⟨e.trans (reindexSo (finSumFinEquiv.trans (finCongr h)))⟩

private theorem su_eq_compact (n : ℕ) :
    su n = (RealFormsTypeA.compactConjugation : Conjugation (SL (Fin n))).fixed := by
  ext X
  change X.valᴴ = -X.val ↔ _
  change X.valᴴ = -X.val ↔ RealFormsTypeA.compactConjugation.map X = X
  constructor
  · intro h
    exact Subtype.ext (by change -X.valᴴ = X.val; rw [h, neg_neg])
  · intro h
    have h' : -X.valᴴ = X.val := congrArg Subtype.val h
    simpa only [neg_neg] using congrArg Neg.neg h'

private theorem unitaryEndpoint {p q n : ℕ} (h : p + q = n) (hzero : p = 0 ∨ q = 0)
    (σ : Conjugation (SL (Blocks p q))) (hσ : HasUnitaryFormula σ) :
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ su n) := by
  let e : Blocks p q ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have h₁ : σ = RealFormsTypeA.compactConjugation :=
    compact_model_unique (Blocks p q) σ (fun X => (hσ X).trans
      (RealFormsTypeA.compact_endpoints p q hzero X.val))
  subst σ
  rw [su_eq_compact]
  obtain ⟨f, _⟩ := restrict_complex_isomorphism _ _ (RealFormsTypeA.reindexSL e)
    (reindexSL_intertwines e)
  exact ⟨f⟩

private theorem unitaryIndex {p q : ℕ} (h : 0 < p + q)
    (σ : Conjugation (SL (Blocks p q))) (hσ : HasUnitaryFormula σ) :
    negativeIndex σ.fixed + 1 = p * p + q * q := by
  obtain ⟨ω, a, ha, hai, hω, _, hform, _, hfixed⟩ := RealFormsTypeA.unitary_model p q
  have eqω := compact_model_unique _ _ hω
  subst ω
  have eqσ : σ = involutionConjugation RealFormsTypeA.compactConjugation a ha hai :=
    Conjugation.ext_map (LieHom.ext fun X => Subtype.ext ((hσ X).trans (hform X).symm))
  rw [eqσ]
  have hk := CartanDecompositionSignature.killing_indices RealFormsTypeA.compactConjugation
    a ha hai (RealFormsTypeA.compactConjugation_isCompact (Blocks p q))
  exact (congrArg (· + 1) hk.1).trans (blockFixed_finrank h a hfixed)

private theorem splitLinearIndex (n : ℕ) :
    negativeIndex (SpecialLinear.sl (Fin n) ℝ) = n * (n - 1) / 2 := by
  obtain ⟨a, ha, hai, ⟨e⟩, ⟨f⟩⟩ := split_model_with_compact n
  have hk := CartanDecompositionSignature.killing_indices RealFormsTypeA.compactConjugation
    a ha hai (RealFormsTypeA.compactConjugation_isCompact (Fin n))
  exact (negativeIndex_eq e).trans
    (hk.1.trans (f.toLinearEquiv.finrank_eq.trans
      (OrthogonalCompactGeometry.orthogonal_dimensions ℂ n).1))

private theorem quaternionicLinearIndex (m : ℕ) :
    negativeIndex (quaternionicSL (Fin m)) = m * (2 * m + 1) := by
  obtain ⟨a, ha, hai, ⟨e⟩, ⟨f⟩⟩ := quaternionic_model_with_compact m
  have hk := CartanDecompositionSignature.killing_indices RealFormsTypeA.compactConjugation
    a ha hai (RealFormsTypeA.compactConjugation_isCompact (Blocks m m))
  have hd := sp_finrank_twice m
  have eq : negativeIndex (quaternionicSL (Fin m)) =
      Module.finrank ℂ (Symplectic.sp (Fin m) ℂ) :=
    (negativeIndex_eq e).trans (hk.1.trans f.toLinearEquiv.finrank_eq)
  rw [eq]
  nlinarith

private theorem unitaryCompactIndex (n : ℕ) (h : 0 < n) :
    negativeIndex (su n) + 1 = n * n := by
  obtain ⟨ω, a, hc, hi, _, _, hform, _, _⟩ := RealFormsTypeA.unitary_model n 0
  let σ := involutionConjugation ω a hc hi
  obtain ⟨e⟩ := unitaryEndpoint (n := n) (by simp) (Or.inr rfl) σ hform
  have hind := unitaryIndex (show 0 < n + 0 by simpa using h) σ hform
  simpa [← negativeIndex_eq e] using hind

private theorem rankOneClassification {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    (h : Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ sl₂ℂ)) :
    Nonempty (A ≃ₗ⁅ℝ⁆ su 2) ∨ Nonempty (A ≃ₗ⁅ℝ⁆ sl₂ℝ) := by
  rcases RealFormsTypeA.abstract_classification 2 (by decide) A h with
    ⟨p, q, hn, σ, e, hσ⟩ | hs | ⟨m, hm, hn, _⟩
  · by_cases hz : p = 0 ∨ q = 0
    · obtain ⟨f⟩ := unitaryEndpoint hn hz σ hσ
      exact Or.inl ⟨e.trans f⟩
    · have hp : p = 1 := by omega
      have hq : q = 1 := by omega
      subst p q
      obtain ⟨f⟩ := RealFormsTypeA.split_rank_one σ hσ
      exact Or.inr ⟨e.trans f⟩
  · exact Or.inr hs
  · omega

private theorem b1Complexification (p q : ℕ) (h : p + q = 3) :
    Nonempty ((ℂ ⊗[ℝ] soSignature p q) ≃ₗ⁅ℂ⁆ sl₂ℂ) := by
  obtain ⟨e⟩ := signatureComplexification p q 3 h
  obtain ⟨b⟩ := ClassicalLowRank.b1_a1
  exact ⟨e.trans ((typeBEquiv (n := 1) (by decide)).trans b)⟩

theorem b1_compact : b1_compact_type := by
  obtain ⟨c⟩ := compact_signature 3
  rcases rankOneClassification (b1Complexification 3 0 rfl) with h | h <;> obtain ⟨e⟩ := h
  · exact ⟨c.symm.trans e⟩
  · have h := negativeIndex_eq e
    rw [signatureIndex 3 0 (by decide), splitLinearIndex 2] at h
    norm_num at h

theorem b1_split : b1_split_type := by
  rcases rankOneClassification (b1Complexification 2 1 rfl) with he | hs
  · obtain ⟨e⟩ := he
    have h := negativeIndex_eq e
    have hi := unitaryCompactIndex 2 (by decide)
    rw [← h, signatureIndex 2 1 (by decide)] at hi
    norm_num at hi
  · exact hs

theorem d2_complex : d2_complex_type := by
  obtain ⟨e⟩ := ClassicalLowRank.d2_a1_sum
  exact ⟨(typeDEquiv (n := 2) (by decide)).trans e⟩

theorem d2_models_real_forms : d2_models_real_forms_type := by
  intro i
  cases i
  · obtain ⟨e⟩ := compact_signature 4
    obtain ⟨S, hS, ⟨f⟩⟩ := model_existence.1 4 0
    exact ⟨S, hS, ⟨e.symm.trans f⟩⟩
  · exact model_existence.1 2 2
  · exact model_existence.1 3 1
  · exact model_existence.2 2

private def expectedIndex : OrthogonalFourKind → ℕ
  | .compact => 6
  | .split => 2
  | .lorentz => 3
  | .quaternionic => 4

private theorem orthogonalFourIndex (i : OrthogonalFourKind) :
    negativeIndex (OrthogonalFourModel i) = expectedIndex i := by
  cases i
  · obtain ⟨e⟩ := compact_signature 4
    change negativeIndex (Orthogonal.so (Fin 4) ℝ) = 6
    rw [← negativeIndex_eq e, signatureIndex 4 0 (by decide)]
  · exact signatureIndex 2 2 (by decide)
  · exact signatureIndex 3 1 (by decide)
  · exact starIndex 2 (by decide)

theorem d2_distinct : d2_distinct_type := by
  intro i j
  constructor
  · rintro ⟨e⟩
    have h := negativeIndex_eq e
    rw [orthogonalFourIndex, orthogonalFourIndex] at h
    have hinj : Function.Injective expectedIndex := by
      intro a b h
      cases a <;> cases b <;> simp_all [expectedIndex]
    exact hinj h
  · rintro rfl
    exact ⟨LieEquiv.refl⟩


open Specs.LieAlgebrasAndRepresentations.RealFormsSymplectic
  (quaternionicSkewLie_value compactConjugation_value signatureConjugation_value
    signatureInvolution_value coefficientConjugation_value splitInvolution_value)

private theorem splitSymplecticIndex (n : ℕ) (hn : 0 < n) :
    negativeIndex (Symplectic.sp (Fin n) ℝ) = n ^ 2 := by
  obtain ⟨e⟩ := RealFormsSymplectic.splitIdentification n
  obtain ⟨hInv, hComm, hσ⟩ := RealFormsSymplectic.splitInvolutionProperties n
  obtain ⟨f⟩ := RealFormsSymplectic.splitComplexFixed n
  have eqσ : coefficientConjugation_value n = involutionConjugation
      (compactConjugation_value n) (splitInvolution_value n) hComm hInv :=
    Conjugation.ext_map (LieHom.ext fun X => (hσ X).symm)
  have he := negativeIndex_eq e.symm
  rw [eqσ] at he
  exact he.trans ((CartanDecompositionSignature.killing_indices _ _ hComm hInv
    (RealFormsSymplectic.compactKilling n hn)).1.trans
    (f.toLinearEquiv.finrank_eq.trans (OrthogonalCompactGeometry.general_linear_dimensions ℂ n).1))


private theorem signatureSymplecticIndex (n p : ℕ) (hn : 0 < n) (hp : p ≤ n) :
    negativeIndex (quaternionicSkewLie_value n p) =
      p * (2 * p + 1) + (n - p) * (2 * (n - p) + 1) := by
  obtain ⟨e⟩ := RealFormsSymplectic.signatureQuaternionicIdentification n p hp
  obtain ⟨_, hInv, hComm, hσ⟩ := RealFormsSymplectic.signatureInvolutionProperties n p
  obtain ⟨f⟩ := RealFormsSymplectic.signatureComplexFixed n p hp
  have eqσ : signatureConjugation_value n p = involutionConjugation
      (compactConjugation_value n) (signatureInvolution_value n p) hComm hInv :=
    Conjugation.ext_map (LieHom.ext fun X => (hσ X).symm)
  have he := negativeIndex_eq e.symm
  rw [eqσ] at he
  have hk := he.trans ((CartanDecompositionSignature.killing_indices _ _ hComm hInv
    (RealFormsSymplectic.compactKilling n hn)).1.trans f.toLinearEquiv.finrank_eq)
  rw [Module.finrank_prod] at hk
  have hp' := sp_finrank_twice p
  have hq := sp_finrank_twice (n - p)
  nlinarith

private theorem b2Classification (p q : ℕ) (h : p + q = 5) :
    (negativeIndex (soSignature p q) = 10 ∧
      Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ quaternionicSkewLie_value 2 2)) ∨
    (negativeIndex (soSignature p q) = 6 ∧
      Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ quaternionicSkewLie_value 2 1)) ∨
    (negativeIndex (soSignature p q) = 4 ∧
      Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ Symplectic.sp (Fin 2) ℝ)) := by
  obtain ⟨e⟩ := signatureComplexification p q 5 h
  obtain ⟨b⟩ := ClassicalLowRank.b2_c2
  let f := e.trans ((typeBEquiv (n := 2) (by decide)).trans b)
  rcases (RealFormsSymplectic.abstractRealFormClassification 2 (by decide) _).mp ⟨f⟩ with
    he | ⟨k, hk, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr ⟨(negativeIndex_eq e).trans (splitSymplecticIndex 2 (by decide)), ⟨e⟩⟩)
  · interval_cases k
    · have hi := (negativeIndex_eq e).trans (signatureSymplecticIndex 2 0 (by decide) (by decide))
      obtain ⟨e₀⟩ := RealFormsSymplectic.signatureQuaternionicIdentification 2 0 (by decide)
      obtain ⟨e₂⟩ := RealFormsSymplectic.signatureQuaternionicIdentification 2 2 (by decide)
      have hσ := RealFormsSymplectic.compactEndpoint 2
      have heq : (signatureConjugation_value 2 0).fixed = (signatureConjugation_value 2 2).fixed :=
        congrArg Conjugation.fixed (hσ.2.trans hσ.1.symm)
      exact Or.inl ⟨hi, ⟨e.trans (e₀.symm.trans ((LieEquiv.ofEq _ _ (congrArg SetLike.coe heq)).trans e₂))⟩⟩
    · exact Or.inr (Or.inl ⟨(negativeIndex_eq e).trans
        (signatureSymplecticIndex 2 1 (by decide) (by decide)), ⟨e⟩⟩)
    · exact Or.inl ⟨(negativeIndex_eq e).trans
        (signatureSymplecticIndex 2 2 (by decide) (by decide)), ⟨e⟩⟩

theorem b2_compact : b2_compact_type := by
  obtain ⟨c⟩ := compact_signature 5
  have h := signatureIndex 5 0 (by decide)
  rcases b2Classification 5 0 rfl with ⟨_, ⟨e⟩⟩ | ⟨h', _⟩ | ⟨h', _⟩
  · exact ⟨c.symm.trans e⟩
  all_goals rw [h] at h'; norm_num at h'

theorem b2_quaternionic : b2_quaternionic_type := by
  have h := signatureIndex 4 1 (by decide)
  rcases b2Classification 4 1 rfl with ⟨h', _⟩ | ⟨_, ⟨e⟩⟩ | ⟨h', _⟩
  · rw [h] at h'; norm_num at h'
  · exact ⟨e⟩
  · rw [h] at h'; norm_num at h'

theorem b2_split : b2_split_type := by
  have h := signatureIndex 3 2 (by decide)
  rcases b2Classification 3 2 rfl with ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, ⟨e⟩⟩
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · exact ⟨e⟩

private theorem d3Classification {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    (h : Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ so (Fin 6))) :
    (negativeIndex A = 15 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ su 4)) ∨
    (negativeIndex A = 10 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ quaternionicSL (Fin 2))) ∨
    (negativeIndex A = 7 ∧ ∃ σ : Conjugation (SL (Blocks 2 2)), HasUnitaryFormula σ ∧
      Nonempty (A ≃ₗ⁅ℝ⁆ σ.fixed)) ∨
    (negativeIndex A = 6 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ SpecialLinear.sl (Fin 4) ℝ)) ∨
    (negativeIndex A = 9 ∧ ∃ σ : Conjugation (SL (Blocks 3 1)), HasUnitaryFormula σ ∧
      Nonempty (A ≃ₗ⁅ℝ⁆ σ.fixed)) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := ClassicalLowRank.d3_a3
  rcases RealFormsTypeA.abstract_classification 4 (by decide) A
      ⟨e.trans ((typeDEquiv (n := 3) (by decide)).trans f)⟩ with
    ⟨p, q, hn, σ, e, hσ⟩ | he | ⟨m, hm, hn, ⟨e⟩⟩
  · have hi := unitaryIndex (by omega : 0 < p + q) σ hσ
    rw [← negativeIndex_eq e] at hi
    by_cases hz : p = 0 ∨ q = 0
    · obtain ⟨g⟩ := unitaryEndpoint hn hz σ hσ
      refine Or.inl ⟨?_, ⟨e.trans g⟩⟩
      rcases hz with rfl | rfl
      · have : q = 4 := by omega
        subst q
        omega
      · have : p = 4 := by omega
        subst p
        omega
    · have hp : 1 ≤ p := by omega
      have hq : 1 ≤ q := by omega
      have hp' : p ≤ 3 := by omega
      interval_cases p
      · have : q = 3 := by omega
        subst q
        obtain ⟨ω, a, hc, hv, _, _, hτ, _, _⟩ := RealFormsTypeA.unitary_model 3 1
        let τ := involutionConjugation ω a hc hv
        obtain ⟨g⟩ := RealFormsTypeA.unitary_exchange 1 3 σ τ hσ hτ
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, τ, hτ, ⟨e.trans g⟩⟩)))
      · have : q = 2 := by omega
        subst q
        exact Or.inr (Or.inr (Or.inl ⟨by omega, σ, hσ, ⟨e⟩⟩))
      · have : q = 1 := by omega
        subst q
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, σ, hσ, ⟨e⟩⟩)))
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(negativeIndex_eq e).trans (splitLinearIndex 4), ⟨e⟩⟩)))
  · have : m = 2 := by omega
    subst m
    exact Or.inr (Or.inl
      ⟨(negativeIndex_eq e).trans (quaternionicLinearIndex 2), ⟨e⟩⟩)

theorem d3_compact : d3_compact_type := by
  obtain ⟨c⟩ := compact_signature 6
  have h := signatureIndex 6 0 (by decide)
  rcases d3Classification (signatureComplexification 6 0 6 rfl) with
    ⟨_, ⟨e⟩⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
  · exact ⟨c.symm.trans e⟩
  all_goals rw [h] at h'; norm_num at h'

theorem d3_quaternionic : d3_quaternionic_type := by
  have h := signatureIndex 5 1 (by decide)
  rcases d3Classification (signatureComplexification 5 1 6 rfl) with
    ⟨h', _⟩ | ⟨_, ⟨e⟩⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
  · rw [h] at h'; norm_num at h'
  · exact ⟨e⟩
  all_goals rw [h] at h'; norm_num at h'

theorem d3_unitary : d3_unitary_type := by
  have h := signatureIndex 4 2 (by decide)
  rcases d3Classification (signatureComplexification 4 2 6 rfl) with
    ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, e⟩ | ⟨h', _⟩ | ⟨h', _⟩
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · exact e
  all_goals rw [h] at h'; norm_num at h'

theorem d3_split : d3_split_type := by
  have h := signatureIndex 3 3 (by decide)
  rcases d3Classification (signatureComplexification 3 3 6 rfl) with
    ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, ⟨e⟩⟩ | ⟨h', _⟩
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · exact ⟨e⟩
  · rw [h] at h'; norm_num at h'

theorem d3_orthogonal_quaternionic : d3_orthogonal_quaternionic_type := by
  have h := starIndex 3 (by decide)
  rcases d3Classification (starComplexification 3 6 rfl) with
    ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, e⟩
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · exact e


section Triality

open scoped BigOperators
open private complexMatrix_signature complexMatrix_quaternionic
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsOrthogonal
open private elementarySkew skewBasis skewBasis_apply
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry

/- The Clifford matrices with off-diagonal blocks Cᵢ and Cᵢᵀ act on two
eight-dimensional spaces. Their even products act on each space separately.
The first block gives the half-spin realization of D₄ triality. -/

private abbrev Eight := Fin 8
private abbrev TrialityMatrix (K : Type*) := Matrix Eight Eight K

/-- The sign masks for the eight signed translations on the three-bit vector space. -/
private def spinMask : Eight → Eight := ![0, 1, 3, 6, 7, 4, 5, 2]

private def spinSign (i b : Eight) : ℤ :=
  let x := (spinMask i).val &&& b.val
  if (x.testBit 0 ^^ x.testBit 1) ^^ x.testBit 2 then -1 else 1

private def cliffordInt (i : Eight) : TrialityMatrix ℤ :=
  Matrix.of fun a b => if a = i ^^^ b then spinSign i b else 0

private def clifford (i : Eight) : TrialityMatrix ℂ :=
  (Int.castRingHom ℂ).mapMatrix (cliffordInt i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem clifford_left_int :
    ∀ i j : Eight, cliffordInt i * (cliffordInt j)ᵀ + cliffordInt j * (cliffordInt i)ᵀ =
      (if i = j then (1 + 1 : TrialityMatrix ℤ) else 0) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem clifford_right_int :
    ∀ i j : Eight, (cliffordInt i)ᵀ * cliffordInt j + (cliffordInt j)ᵀ * cliffordInt i =
      (if i = j then (1 + 1 : TrialityMatrix ℤ) else 0) := by
  decide +kernel


private def delta (i j : Eight) : ℂ := if i = j then 1 else 0

private theorem delta_symm (i j : Eight) : delta i j = delta j i := by
  simp [delta, eq_comm]

private theorem intMatrix_transpose (X : TrialityMatrix ℤ) :
    (Int.castRingHom ℂ).mapMatrix Xᵀ = ((Int.castRingHom ℂ).mapMatrix X)ᵀ := rfl

private theorem clifford_left (i j : Eight) :
    clifford i * (clifford j)ᵀ + clifford j * (clifford i)ᵀ =
      (2 : ℂ) • (delta i j • (1 : TrialityMatrix ℂ)) := by
  have h := congrArg (Int.castRingHom ℂ).mapMatrix (clifford_left_int i j)
  simp only [map_add, map_mul, intMatrix_transpose] at h
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, map_add, map_one, map_zero] at h <;>
    simpa [clifford, delta, hij, two_smul] using h

private theorem clifford_right (i j : Eight) :
    (clifford i)ᵀ * clifford j + (clifford j)ᵀ * clifford i =
      (2 : ℂ) • (delta i j • (1 : TrialityMatrix ℂ)) := by
  have h := congrArg (Int.castRingHom ℂ).mapMatrix (clifford_right_int i j)
  simp only [map_add, map_mul, intMatrix_transpose] at h
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, map_add, map_one, map_zero] at h <;>
    simpa [clifford, delta, hij, two_smul] using h

/-- Twice the half-spin action of the skew matrix unit Eᵢⱼ − Eⱼᵢ. -/
private def spinNumerator (i j : Eight) : TrialityMatrix ℂ :=
  clifford i * (clifford j)ᵀ - delta i j • 1

private theorem spinNumerator_flip (i j : Eight) :
    spinNumerator j i = -spinNumerator i j := by
  have h := clifford_left i j
  rw [two_smul] at h
  rw [spinNumerator, spinNumerator, ← delta_symm i j]
  rw [eq_neg_iff_add_eq_zero]
  rw [add_comm (clifford j * (clifford i)ᵀ - _)]
  rw [sub_add_sub_comm, h, sub_self]

private theorem spinNumerator_diag (i : Eight) : spinNumerator i i = 0 := by
  have h := spinNumerator_flip i i
  have hz : (2 : ℂ) • spinNumerator i i = 0 :=
    (two_smul ℂ _).trans ((congrArg (spinNumerator i i + ·) h).trans (add_neg_cancel _))
  exact (smul_eq_zero.mp hz).resolve_left two_ne_zero

private theorem spinNumerator_transpose (i j : Eight) :
    (spinNumerator i j)ᵀ = -spinNumerator i j := by
  rw [spinNumerator, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, Matrix.transpose_one, delta_symm i j, ← spinNumerator,
    spinNumerator_flip]
  rw [spinNumerator, delta_symm i j]

private theorem spinNumerator_bracket (i j k l : Eight) :
    spinNumerator i j * spinNumerator k l - spinNumerator k l * spinNumerator i j =
      (2 : ℂ) • (delta j k • spinNumerator i l - delta i k • spinNumerator j l -
        delta j l • spinNumerator i k + delta i l • spinNumerator j k) := by
  let C := clifford
  let D (i : Eight) := (C i)ᵀ
  let P (i j : Eight) := C i * D j
  have hP :
      P i j * P k l - P k l * P i j =
        (2 : ℂ) • (delta j k • P i l - delta i k • P j l +
          delta j l • P k i - delta i l • P k j) := by
    calc
      _ = C i * (D j * C k + D k * C j) * D l -
          (C i * D k + C k * D i) * C j * D l +
          C k * D i * (C j * D l + C l * D j) -
          C k * (D i * C l + D l * C i) * D j := by
            unfold P
            noncomm_ring
      _ = _ := by
        dsimp only [C, D]
        rw [clifford_right, clifford_left, clifford_left, clifford_right]
        simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, smul_add, smul_sub,
          P, C, D, mul_assoc]
  have hshift :
      delta j k • P i l - delta i k • P j l + delta j l • P k i - delta i l • P k j =
        delta j k • spinNumerator i l - delta i k • spinNumerator j l -
          delta j l • spinNumerator i k + delta i l • spinNumerator j k := by
    have ha : delta i l * delta k j = delta j k * delta i l := by
      rw [← delta_symm j k, mul_comm]
    have hb : delta j l * delta k i = delta i k * delta j l := by
      rw [← delta_symm i k, mul_comm]
    calc
      _ = delta j k • spinNumerator i l - delta i k • spinNumerator j l +
          delta j l • spinNumerator k i - delta i l • spinNumerator k j := by
            change _ = delta j k • (P i l - delta i l • 1) -
              delta i k • (P j l - delta j l • 1) + delta j l • (P k i - delta k i • 1) -
              delta i l • (P k j - delta k j • 1)
            simp only [smul_sub, smul_smul, ha, hb]
            abel
      _ = _ := by
        rw [spinNumerator_flip i k, spinNumerator_flip j k, smul_neg, smul_neg,
          ← sub_eq_add_neg, sub_neg_eq_add]
  rw [← hshift, ← hP]
  change (P i j - delta i j • 1) * (P k l - delta k l • 1) -
    (P k l - delta k l • 1) * (P i j - delta i j • 1) = _
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one, smul_smul]
  rw [mul_comm (delta k l) (delta i j)]
  abel

private def spinBasisVector (i j : Eight) : Orthogonal.so Eight ℂ :=
  (2 : ℂ)⁻¹ • ⟨spinNumerator i j, Orthogonal.mem_so _ _ _ |>.mpr (spinNumerator_transpose i j)⟩

private theorem spinBasisVector_bracket (i j k l : Eight) :
    ⁅spinBasisVector i j, spinBasisVector k l⁆ =
      delta j k • spinBasisVector i l - delta i k • spinBasisVector j l -
        delta j l • spinBasisVector i k + delta i l • spinBasisVector j k := by
  apply Subtype.ext
  change ((2 : ℂ)⁻¹ • spinNumerator i j) * ((2 : ℂ)⁻¹ • spinNumerator k l) -
    ((2 : ℂ)⁻¹ • spinNumerator k l) * ((2 : ℂ)⁻¹ • spinNumerator i j) =
      delta j k • ((2 : ℂ)⁻¹ • spinNumerator i l) -
        delta i k • ((2 : ℂ)⁻¹ • spinNumerator j l) -
        delta j l • ((2 : ℂ)⁻¹ • spinNumerator i k) +
        delta i l • ((2 : ℂ)⁻¹ • spinNumerator j k)
  have hs (a b : Eight) (X : TrialityMatrix ℂ) :
      delta a b • ((2 : ℂ)⁻¹ • X) = (2 : ℂ)⁻¹ • (delta a b • X) :=
    smul_comm _ _ _
  simp only [Matrix.smul_mul, Matrix.mul_smul, hs, ← smul_sub, ← smul_add]
  rw [spinNumerator_bracket, smul_smul, smul_smul]
  congr 1
  field_simp

private def skewMatrixUnit {R : Type*} [AddGroupWithOne R] (i j : Eight) : TrialityMatrix R :=
  single i j 1 - single j i 1

private theorem skewMatrixUnit_bracket (i j k l : Eight) :
    (skewMatrixUnit i j : TrialityMatrix ℂ) * skewMatrixUnit k l - skewMatrixUnit k l * skewMatrixUnit i j =
      delta j k • skewMatrixUnit i l - delta i k • skewMatrixUnit j l -
        delta j l • skewMatrixUnit i k + delta i l • skewMatrixUnit j k := by
  have hs (a b c d : Eight) : single a b (1 : ℂ) * single c d 1 =
      delta b c • single a d (1 : ℂ) := by
    by_cases h : b = c
    · subst c
      simp [delta, Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b c h 1]
      simp [delta, h]
  unfold skewMatrixUnit
  simp only [sub_mul, mul_sub, hs, smul_sub, ← delta_symm j k, ← delta_symm i k,
    ← delta_symm j l, ← delta_symm i l]
  abel

private def trialityInput : Fin 4 ⊕ Fin 4 ≃ Eight := finSumFinEquiv

/-- Put the two negative half-spin coordinates at indices 3 and 7. -/
private def trialityOutput : Fin 6 ⊕ Fin 2 ≃ Eight :=
  finSumFinEquiv.trans (Equiv.swap 3 6)

private def quarterTurn (R : Type*) [CommRing R] : TrialityMatrix R :=
  Matrix.reindex trialityInput trialityInput (-Matrix.J (Fin 4) R)

private def trialitySignature (R : Type*) [CommRing R] : TrialityMatrix R :=
  Matrix.reindex trialityOutput trialityOutput
    (Orthogonal.indefiniteDiagonal (Fin 6) (Fin 2) R)

private def quarterSign (i : Eight) : ℤ := if i < 4 then -1 else 1

private def spinDiagonalSign (i : Eight) : ℤ := if i = 3 ∨ i = 7 then -1 else 1

private theorem trialitySignature_int :
    trialitySignature ℤ = diagonal spinDiagonalSign := by decide +kernel

private def spinNumeratorInt (i j : Eight) : TrialityMatrix ℤ :=
  cliffordInt i * (cliffordInt j)ᵀ - if i = j then 1 else 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem spinNumerator_intertwines_entry :
    ∀ i j a b : Eight,
      spinDiagonalSign a * spinNumeratorInt i j a b * spinDiagonalSign b =
        (quarterSign i * quarterSign j) * spinNumeratorInt (i ^^^ 4) (j ^^^ 4) a b := by
  decide +kernel

private theorem spinNumerator_intertwines_int (i j : Eight) :
    trialitySignature ℤ * spinNumeratorInt i j * (trialitySignature ℤ)ᵀ =
      (quarterSign i * quarterSign j) • spinNumeratorInt (i ^^^ 4) (j ^^^ 4) := by
  rw [trialitySignature_int, Matrix.diagonal_transpose]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact spinNumerator_intertwines_entry i j a b

private theorem quarterTurn_matrix_int :
    quarterTurn ℤ = Matrix.of (fun a b => if a = b ^^^ 4 then quarterSign b else 0) := by
  decide +kernel

private theorem quarterTurn_entries (a b : Eight) :
    quarterTurn ℤ a b = if a = b ^^^ 4 then quarterSign b else 0 :=
  congrFun (congrFun quarterTurn_matrix_int a) b

private theorem conjugate_single_int (i j : Eight) :
    quarterTurn ℤ * single i j (1 : ℤ) * (quarterTurn ℤ)ᵀ =
      (quarterSign i * quarterSign j) • single (i ^^^ 4) (j ^^^ 4) (1 : ℤ) := by
  ext a b
  have h :
      (quarterTurn ℤ * single i j (1 : ℤ) * (quarterTurn ℤ)ᵀ) a b =
        quarterTurn ℤ a i * quarterTurn ℤ b j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.mul_single_apply_same, Matrix.transpose_apply, mul_one]
    · intro k _ hk
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]
    · simp
  rw [h, quarterTurn_entries, quarterTurn_entries]
  by_cases ha : a = i ^^^ 4 <;> by_cases hb : b = j ^^^ 4 <;>
    simp [Matrix.single, ha, hb, Ne.symm]

private theorem quarterTurn_skew_int (i j : Eight) :
    quarterTurn ℤ * skewMatrixUnit i j * (quarterTurn ℤ)ᵀ =
      (quarterSign i * quarterSign j) • skewMatrixUnit (i ^^^ 4) (j ^^^ 4) := by
  simp only [skewMatrixUnit, Matrix.mul_sub, Matrix.sub_mul, conjugate_single_int, smul_sub]
  rw [mul_comm (quarterSign j) (quarterSign i)]

private theorem quarterTurn_cast :
    (Int.castRingHom ℂ).mapMatrix (quarterTurn ℤ) = quarterTurn ℂ := by
  let f := Int.castRingHom ℂ
  change Matrix.reindex trialityInput trialityInput
    (f.mapMatrix (-Matrix.J (Fin 4) ℤ)) = _
  rw [map_neg]
  exact congrArg (fun X => Matrix.reindex trialityInput trialityInput (-X))
    (Matrix.map_J (Fin 4) f)

private theorem trialitySignature_cast :
    (Int.castRingHom ℂ).mapMatrix (trialitySignature ℤ) = trialitySignature ℂ := by
  ext i j
  change ((Orthogonal.indefiniteDiagonal (Fin 6) (Fin 2) ℤ
    (trialityOutput.symm i) (trialityOutput.symm j) : ℤ) : ℂ) = _
  change _ = Orthogonal.indefiniteDiagonal (Fin 6) (Fin 2) ℂ
    (trialityOutput.symm i) (trialityOutput.symm j)
  generalize trialityOutput.symm i = a
  generalize trialityOutput.symm j = b
  by_cases h : a = b
  · subst b
    cases a <;> simp [Orthogonal.indefiniteDiagonal]
  · simp [Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply_ne _ h]

private theorem spinNumerator_cast (i j : Eight) :
    (Int.castRingHom ℂ).mapMatrix (spinNumeratorInt i j) = spinNumerator i j := by
  rw [spinNumeratorInt, spinNumerator, map_sub, map_mul, intMatrix_transpose]
  by_cases h : i = j <;> simp [clifford, delta, h]

private theorem skewMatrixUnit_cast (i j : Eight) :
    (Int.castRingHom ℂ).mapMatrix (skewMatrixUnit i j) = skewMatrixUnit i j := by
  unfold skewMatrixUnit
  rw [map_sub]
  change (single i j (1 : ℤ)).map (Int.castRingHom ℂ) -
    (single j i (1 : ℤ)).map (Int.castRingHom ℂ) = _
  rw [Matrix.map_single, Matrix.map_single, map_one]

private theorem quarterTurn_skew (i j : Eight) :
    quarterTurn ℂ * skewMatrixUnit i j * (quarterTurn ℂ)ᵀ =
      ((quarterSign i * quarterSign j : ℤ) : ℂ) • skewMatrixUnit (i ^^^ 4) (j ^^^ 4) := by
  have h := congrArg (Int.castRingHom ℂ).mapMatrix (quarterTurn_skew_int i j)
  simpa only [map_mul, intMatrix_transpose, quarterTurn_cast, skewMatrixUnit_cast,
    map_zsmul, Int.cast_smul_eq_zsmul] using h

private theorem spinNumerator_intertwines (i j : Eight) :
    trialitySignature ℂ * spinNumerator i j * (trialitySignature ℂ)ᵀ =
      ((quarterSign i * quarterSign j : ℤ) : ℂ) • spinNumerator (i ^^^ 4) (j ^^^ 4) := by
  have h := congrArg (Int.castRingHom ℂ).mapMatrix (spinNumerator_intertwines_int i j)
  simpa only [map_mul, intMatrix_transpose, trialitySignature_cast, spinNumerator_cast,
    map_zsmul, Int.cast_smul_eq_zsmul] using h

private theorem xor_xor_eq : ∀ i j : Eight, i ^^^ (i ^^^ j) = j := by decide +kernel

private def spinEntry (i j a b : Eight) : ℤ :=
  if a = i ^^^ (j ^^^ b) then spinSign i (j ^^^ b) * spinSign j (j ^^^ b) else 0

private theorem spinNumeratorInt_apply_offdiag {i j : Eight} (hij : i ≠ j) (a b : Eight) :
    spinNumeratorInt i j a b = spinEntry i j a b := by
  unfold spinNumeratorInt
  rw [ite_eq_right hij, sub_zero, Matrix.mul_apply, Finset.sum_eq_single (j ^^^ b)]
  · by_cases h : a = i ^^^ (j ^^^ b) <;>
      simp [cliffordInt, spinEntry, h, xor_xor_eq]
  · intro k _ hk
    have hne : b ≠ j ^^^ k := by
      intro h
      apply hk
      rw [h, xor_xor_eq]
    simp [cliffordInt, hne]
  · simp

/- For increasing pairs the numerators are mutually orthogonal and each has
squared entry norm eight. The sum uses the supported row in each column. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem spinGram_int :
    ∀ i j k l : Eight, i < j → k < l →
      (∑ b : Eight, spinEntry i j (i ^^^ (j ^^^ b)) b *
        spinEntry k l (i ^^^ (j ^^^ b)) b) = if i = k ∧ j = l then 8 else 0 := by
  decide +kernel

private abbrev spinElementary := elementarySkew (ι := Eight) (K := ℂ)
private abbrev spinBasis := skewBasis (ι := Eight) (K := ℂ)

private def spinLinear : so Eight →ₗ[ℂ] so Eight :=
  spinBasis.constr ℂ (fun p => spinBasisVector p.val.1 p.val.2)

private theorem spinLinear_elementary (i j : Eight) :
    spinLinear (spinElementary i j) = spinBasisVector i j := by
  have hlt {i j : Eight} (h : i < j) : spinLinear (spinElementary i j) = spinBasisVector i j := by
    have he : spinBasis ⟨(i, j), h⟩ = spinElementary i j := skewBasis_apply ⟨(i, j), h⟩
    rw [← he]
    exact spinBasis.constr_basis _ _ _
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt h
  · have hE : spinElementary i i = (0 : so Eight) := Subtype.ext (sub_self _)
    rw [hE, map_zero]
    apply Subtype.ext
    change (0 : TrialityMatrix ℂ) = (2 : ℂ)⁻¹ • spinNumerator i i
    rw [spinNumerator_diag, smul_zero]
  · have hE : spinElementary i j = -(spinElementary j i : so Eight) :=
      Subtype.ext (neg_sub _ _).symm
    rw [hE, map_neg, hlt h]
    apply Subtype.ext
    change -((2 : ℂ)⁻¹ • spinNumerator j i) = (2 : ℂ)⁻¹ • spinNumerator i j
    rw [spinNumerator_flip i j, smul_neg, neg_neg]

private theorem elementarySkew_bracket (i j k l : Eight) :
    ⁅(spinElementary i j : so Eight), spinElementary k l⁆ =
      delta j k • spinElementary i l - delta i k • spinElementary j l -
        delta j l • spinElementary i k + delta i l • spinElementary j k :=
  Subtype.ext (skewMatrixUnit_bracket i j k l)

set_option maxHeartbeats 600000 in
private def spinHom : so Eight →ₗ⁅ℂ⁆ so Eight where
  toLinearMap := spinLinear
  map_lie' {x y} := by
    let a := (LieAlgebra.ad ℂ (so Eight)).toLinearMap
    let lhs := a.compr₂ spinLinear
    let rhs := (a.compl₂ spinLinear).comp spinLinear
    let b := spinBasis
    have hab : lhs = rhs := by
      apply LinearMap.ext_basis b b
      intro p q
      change spinLinear ⁅spinBasis p, spinBasis q⁆ = ⁅spinLinear (spinBasis p), spinLinear (spinBasis q)⁆
      simp only [skewBasis_apply, elementarySkew_bracket, map_add, map_sub, map_smul,
        spinLinear_elementary, spinBasisVector_bracket]
    exact congrArg (fun F => F x y) hab

private def spinPairing (i j : Eight) : so Eight →ₗ[ℂ] ℂ where
  toFun X := ∑ b : Eight, (spinEntry i j (i ^^^ (j ^^^ b)) b : ℂ) * X.val (i ^^^ (j ^^^ b)) b
  map_add' X Y := by
    change (∑ b : Eight, (spinEntry i j (i ^^^ (j ^^^ b)) b : ℂ) *
      (X.val (i ^^^ (j ^^^ b)) b + Y.val (i ^^^ (j ^^^ b)) b)) = _
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' r X := by
    change (∑ b : Eight, (spinEntry i j (i ^^^ (j ^^^ b)) b : ℂ) *
      (r * X.val (i ^^^ (j ^^^ b)) b)) = r * _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => mul_left_comm _ _ _)

private theorem spinPairing_basisVector {i j k l : Eight} (hi : i < j) (hk : k < l) :
    spinPairing i j (spinBasisVector k l) = if i = k ∧ j = l then 4 else 0 := by
  change (∑ b : Eight, (spinEntry i j (i ^^^ (j ^^^ b)) b : ℂ) *
    ((2 : ℂ)⁻¹ * spinNumerator k l (i ^^^ (j ^^^ b)) b)) = _
  rw [← spinNumerator_cast]
  change (∑ b : Eight, (spinEntry i j (i ^^^ (j ^^^ b)) b : ℂ) *
    ((2 : ℂ)⁻¹ * (spinNumeratorInt k l (i ^^^ (j ^^^ b)) b : ℂ))) = _
  simp_rw [spinNumeratorInt_apply_offdiag hk.ne, mul_left_comm _ ((2 : ℂ)⁻¹)]
  rw [← Finset.mul_sum]
  simp only [← Int.cast_mul, ← Int.cast_sum, spinGram_int i j k l hi hk]
  by_cases h : i = k ∧ j = l <;> norm_num [h]

private theorem spinPairing_coord (p : {p : Eight × Eight // p.1 < p.2}) :
    (spinPairing p.val.1 p.val.2).comp spinLinear = (4 : ℂ) • spinBasis.coord p := by
  apply spinBasis.ext
  intro q
  change spinPairing p.val.1 p.val.2 (spinLinear (spinBasis q)) =
    (4 : ℂ) * spinBasis.repr (spinBasis q) p
  rw [Module.Basis.repr_self, skewBasis_apply, spinLinear_elementary,
    spinPairing_basisVector p.property q.property]
  by_cases h : q = p
  · subst q
    simp
  · have hpq : ¬ (p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) :=
      fun hpq => h (Subtype.ext (Prod.ext hpq.1.symm hpq.2.symm))
    simp [Finsupp.single_eq_of_ne (Ne.symm h), hpq]

private theorem spinHom_injective : Function.Injective spinHom := by
  apply (injective_iff_map_eq_zero spinHom).2
  intro X hX
  apply spinBasis.repr.injective
  ext p
  have hp := congrArg (fun f : so Eight →ₗ[ℂ] ℂ => f X) (spinPairing_coord p)
  change spinPairing p.val.1 p.val.2 (spinHom X) = (4 : ℂ) * spinBasis.repr X p at hp
  rw [hX, map_zero] at hp
  have h := (mul_eq_zero.mp hp.symm).resolve_left (by norm_num)
  simpa using h

private def spinTriality : so Eight ≃ₗ⁅ℂ⁆ so Eight :=
  LieEquiv.ofBijective spinHom ⟨spinHom_injective,
    LinearMap.surjective_of_injective (f := spinLinear) spinHom_injective⟩

private def spinCoefficientConjugation :
    so Eight →ₛₗ[Complex.conjAe.toRingEquiv.toRingHom] so Eight where
  toFun := (coefficientConjugation Eight).map
  map_add' := map_add _
  map_smul' := (coefficientConjugation Eight).antilinear

private theorem spinCoefficient_elementary (i j : Eight) :
    (coefficientConjugation Eight).map (spinElementary i j) = spinElementary i j := by
  apply Subtype.ext
  change conjMatrix (skewMatrixUnit i j : TrialityMatrix ℂ) = skewMatrixUnit i j
  rw [← skewMatrixUnit_cast]
  ext a b
  change star ((skewMatrixUnit i j a b : ℤ) : ℂ) = _
  simp

private theorem spinCoefficient_atom (i j : Eight) :
    (coefficientConjugation Eight).map (spinBasisVector i j) = spinBasisVector i j := by
  apply Subtype.ext
  change conjMatrix ((2 : ℂ)⁻¹ • spinNumerator i j) = (2 : ℂ)⁻¹ • spinNumerator i j
  rw [← spinNumerator_cast]
  ext a b
  change star ((2 : ℂ)⁻¹ * ((spinNumeratorInt i j a b : ℤ) : ℂ)) = _
  simp

private theorem spinTriality_commutes :
    Intertwines (coefficientConjugation Eight) (coefficientConjugation Eight) spinTriality := by
  intro x
  have h : spinCoefficientConjugation.comp spinLinear =
      spinLinear.comp spinCoefficientConjugation := by
    apply spinBasis.ext
    intro p
    change (coefficientConjugation Eight).map (spinLinear (spinBasis p)) =
      spinLinear ((coefficientConjugation Eight).map (spinBasis p))
    rw [skewBasis_apply, spinLinear_elementary, spinCoefficient_atom, spinCoefficient_elementary,
      spinLinear_elementary]
  exact congrArg (fun F => F x) h

private def reindexOrthogonalAction {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Eight) {A : Matrix ι ι ℝ} (hA : IsOrthogonal A) : so Eight ≃ₗ⁅ℂ⁆ so Eight :=
  (reindexSo e).symm.trans ((orthogonalAction A hA).trans (reindexSo e))

private theorem reindexOrthogonalAction_val {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Eight) {A : Matrix ι ι ℝ} (hA : IsOrthogonal A) (X : so Eight) :
    (reindexOrthogonalAction e hA X).val =
      Matrix.reindex e e (complexMatrix A) * X.val * (Matrix.reindex e e (complexMatrix A))ᵀ := by
  let r := Matrix.reindexAlgEquiv ℂ ℂ e
  change r (complexMatrix A * ((reindexSo e).symm X).val * (complexMatrix A)ᵀ) =
    r (complexMatrix A) * X.val * (r (complexMatrix A))ᵀ
  have hx : r ((reindexSo e).symm X).val = X.val :=
    congrArg Subtype.val ((reindexSo e).apply_symm_apply X)
  rw [map_mul, map_mul, hx]
  exact congrArg ((r (complexMatrix A) * X.val) * ·)
    (Matrix.transpose_reindex e e (complexMatrix A)).symm

private theorem spinTriality_intertwines (X : so Eight) :
    reindexOrthogonalAction trialityOutput (signature_orthogonal 6 2) (spinTriality X) =
      spinTriality (reindexOrthogonalAction trialityInput (quaternionic_orthogonal 4) X) := by
  let a := reindexOrthogonalAction trialityInput (quaternionic_orthogonal 4)
  let b := reindexOrthogonalAction trialityOutput (signature_orthogonal 6 2)
  have ha (i j : Eight) : a (spinElementary i j) =
      ((quarterSign i * quarterSign j : ℤ) : ℂ) • spinElementary (i ^^^ 4) (j ^^^ 4) := by
    apply Subtype.ext
    dsimp only [a]
    rw [reindexOrthogonalAction_val, complexMatrix_quaternionic]
    exact quarterTurn_skew _ _
  have hb (i j : Eight) : b (spinBasisVector i j) =
      ((quarterSign i * quarterSign j : ℤ) : ℂ) • spinBasisVector (i ^^^ 4) (j ^^^ 4) := by
    apply Subtype.ext
    dsimp only [b]
    rw [reindexOrthogonalAction_val, complexMatrix_signature]
    change trialitySignature ℂ * ((2 : ℂ)⁻¹ • spinNumerator i j) * (trialitySignature ℂ)ᵀ =
      ((quarterSign i * quarterSign j : ℤ) : ℂ) • ((2 : ℂ)⁻¹ • spinNumerator _ _)
    rw [Matrix.mul_smul, Matrix.smul_mul, spinNumerator_intertwines, smul_comm]
  have he : b.toLinearEquiv.toLinearMap.comp spinLinear =
      spinLinear.comp a.toLinearEquiv.toLinearMap := by
    apply spinBasis.ext
    intro p
    change b (spinLinear (spinBasis p)) = spinLinear (a (spinBasis p))
    rw [skewBasis_apply, spinLinear_elementary, hb, ha, map_smul, spinLinear_elementary]
  exact congrArg (fun F => F X) he

set_option maxHeartbeats 700000 in
theorem d4_triality : d4_triality_type := by
  let u := reindexSo trialityInput
  let v := reindexSo trialityOutput
  let e := u.trans (spinTriality.trans v.symm)
  let a := orthogonalAction (quaternionicMatrix 4) (quaternionic_orthogonal 4)
  let b := orthogonalAction (signatureMatrix 6 2) (signature_orthogonal 6 2)
  have hlinear (X : so (Fin 4 ⊕ Fin 4)) : b (e X) = e (a X) := by
    apply v.injective
    change v (b (v.symm (spinTriality (u X)))) = v (v.symm (spinTriality (u (a X))))
    rw [v.apply_symm_apply]
    have h := spinTriality_intertwines (u X)
    change v (b (v.symm (spinTriality (u X)))) =
      spinTriality (u (a (u.symm (u X)))) at h
    rwa [u.symm_apply_apply] at h
  let ω₁ := RealFormsOrthogonal.coefficientConjugation (Fin 4 ⊕ Fin 4)
  let ω₂ := RealFormsOrthogonal.coefficientConjugation (Fin 6 ⊕ Fin 2)
  let ω := RealFormsOrthogonal.coefficientConjugation Eight
  have hcoeff (X : so (Fin 4 ⊕ Fin 4)) : ω₂.map (e X) = e (ω₁.map X) := by
    apply v.injective
    change v (ω₂.map (e X)) = v (e (ω₁.map X))
    have hv : ω.map (v (e X)) = v (ω₂.map (e X)) := reindexSo_commutes trialityOutput (e X)
    rw [← hv]
    change ω.map (v (v.symm (spinTriality (u X)))) = v (v.symm (spinTriality (u (ω₁.map X))))
    simp only [v.apply_symm_apply]
    have hu : ω.map (u X) = u (ω₁.map X) := reindexSo_commutes trialityInput X
    exact (spinTriality_commutes (u X)).trans (congrArg spinTriality hu)
  have he : Intertwines (quaternionicConjugation 4) (signatureConjugation 6 2) e := by
    intro X
    change b (ω₂.map (e X)) = e (a (ω₁.map X))
    exact (congrArg b (hcoeff X)).trans (hlinear _)
  obtain ⟨f, _⟩ := restrict_complex_isomorphism _ _ e he
  obtain ⟨g⟩ := signature_model 6 2
  exact ⟨f.trans g.symm⟩

end Triality

section Products

variable {R : Type*} [CommRing R]
variable {A B C D : Type*} [LieRing A] [LieRing B] [LieRing C] [LieRing D]
  [LieAlgebra R A] [LieAlgebra R B] [LieAlgebra R C] [LieAlgebra R D]

private def productEquiv (e : A ≃ₗ⁅R⁆ B) (f : C ≃ₗ⁅R⁆ D) :
    (A × C) ≃ₗ⁅R⁆ (B × D) where
  __ := e.toLinearEquiv.prodCongr f.toLinearEquiv
  map_lie' {x y} := Prod.ext (e.map_lie _ _) (f.map_lie _ _)

end Products

section ProductConjugations

variable {L H : Type*} [LieRing L] [LieRing H] [LieAlgebra ℂ L] [LieAlgebra ℂ H]

private def productConjugation (σ : Conjugation L) (τ : Conjugation H) :
    Conjugation (L × H) where
  map := σ.map.prodMap τ.map
  antilinear c x := Prod.ext (σ.antilinear c x.1) (τ.antilinear c x.2)
  involutive x := Prod.ext (σ.involutive x.1) (τ.involutive x.2)

private def fixedProductEquiv (σ : Conjugation L) (τ : Conjugation H) :
    (productConjugation σ τ).fixed ≃ₗ⁅ℝ⁆ (σ.fixed × τ.fixed) where
  toFun x := (⟨x.val.1, congrArg Prod.fst x.property⟩, ⟨x.val.2, congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := rfl
  map_lie' := rfl

private def complexFixedProductEquiv (a : L ≃ₗ⁅ℂ⁆ L) (b : H ≃ₗ⁅ℂ⁆ H) :
    complexFixed (productEquiv a b) ≃ₗ⁅ℂ⁆ (complexFixed a × complexFixed b) where
  toFun x := (⟨x.val.1, congrArg Prod.fst x.property⟩, ⟨x.val.2, congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := rfl
  map_lie' := rfl

private theorem productIsCompact [FiniteDimensional ℂ L] [FiniteDimensional ℂ H]
    {σ : Conjugation L} {τ : Conjugation H}
    (hσ : IsCompact σ) (hτ : IsCompact τ) : IsCompact (productConjugation σ τ) := by
  intro x hx
  let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let : FiniteDimensional ℝ H := FiniteDimensional.trans ℝ ℂ H
  let : FiniteDimensional ℝ σ.fixed :=
    FiniteDimensional.of_injective σ.fixed.toSubmodule.subtype Subtype.val_injective
  let : FiniteDimensional ℝ τ.fixed :=
    FiniteDimensional.of_injective τ.fixed.toSubmodule.subtype Subtype.val_injective
  let e := fixedProductEquiv σ τ
  let y := e x
  have he : y ≠ 0 := by
    intro h
    apply hx
    apply e.injective
    rw [map_zero]
    exact h
  have hk :
      _root_.killingForm ℝ (σ.fixed × τ.fixed) y y =
        _root_.killingForm ℝ σ.fixed y.1 y.1 + _root_.killingForm ℝ τ.fixed y.2 y.2 := by
    simp only [killingForm_apply_apply]
    exact LinearMap.trace_prodMap'
      ((ad ℝ σ.fixed y.1).comp (ad ℝ σ.fixed y.1))
      ((ad ℝ τ.fixed y.2).comp (ad ℝ τ.fixed y.2))
  rw [← killingForm_of_equiv_apply e]
  change _root_.killingForm ℝ (σ.fixed × τ.fixed) y y < 0
  rw [hk]
  by_cases h₁ : y.1 = 0
  · have h₂ : y.2 ≠ 0 := fun h => he (Prod.ext h₁ h)
    simpa [h₁] using hτ y.2 h₂
  · by_cases h₂ : y.2 = 0
    · simpa [h₂] using hσ y.1 h₁
    · exact add_neg (hσ y.1 h₁) (hτ y.2 h₂)

private theorem productIndex [FiniteDimensional ℂ L] [FiniteDimensional ℂ H]
    {ω : Conjugation L} {υ : Conjugation H} (hω : IsCompact ω) (hυ : IsCompact υ)
    {a : L ≃ₗ⁅ℂ⁆ L} {b : H ≃ₗ⁅ℂ⁆ H}
    (ha : Intertwines ω ω a) (hb : Intertwines υ υ b)
    (hai : Function.Involutive a) (hbi : Function.Involutive b) :
    negativeIndex ((involutionConjugation ω a ha hai).fixed ×
      (involutionConjugation υ b hb hbi).fixed) =
    Module.finrank ℂ (complexFixed a) + Module.finrank ℂ (complexFixed b) := by
  let θ := productEquiv a b
  let Ω := productConjugation ω υ
  have hc : Intertwines Ω Ω θ := fun x => Prod.ext (ha x.1) (hb x.2)
  have hi : Function.Involutive θ := fun x => Prod.ext (hai x.1) (hbi x.2)
  let σ := involutionConjugation ω a ha hai
  let τ := involutionConjugation υ b hb hbi
  have hEq : productConjugation σ τ = involutionConjugation Ω θ hc hi :=
    Conjugation.ext_map (LieHom.ext fun _ => rfl)
  have hind := (negativeIndex_eq (fixedProductEquiv σ τ)).symm
  rw [hEq] at hind
  exact hind.trans ((CartanDecompositionSignature.killing_indices Ω θ hc hi
    (productIsCompact hω hυ)).1.trans
    ((complexFixedProductEquiv a b).toLinearEquiv.finrank_eq.trans Module.finrank_prod))

end ProductConjugations

section RankOneProduct

private theorem rankOneComponent_surjective (f : sl₂ℂ →ₗ⁅ℝ⁆ sl₂ℂ)
    (ha : ∀ (z : ℂ) x, f (z • x) = star z • f x) (hf : f ≠ 0) :
    Function.Surjective f := by
  let K : LieIdeal ℂ sl₂ℂ :=
    { carrier := {x | f x = 0}
      add_mem' := by intro x y hx hy; change f (x + y) = 0; rw [map_add, hx, hy, add_zero]
      zero_mem' := map_zero f
      smul_mem' := by intro c x hx; change f (c • x) = 0; rw [ha, hx, smul_zero]
      lie_mem := by intro x y hy; change f ⁅x, y⁆ = 0; rw [f.map_lie, hy, lie_zero] }
  letI : FiniteDimensional ℝ sl₂ℂ := FiniteDimensional.trans ℝ ℂ sl₂ℂ
  apply LinearMap.surjective_of_injective (f := f.toLinearMap)
  rcases (sl2_simple ℂ).eq_bot_or_eq_top K with hK | hK
  · apply (injective_iff_map_eq_zero f).2
    intro x hx
    have hx' : x ∈ K := hx
    rw [hK] at hx'
    exact (LieSubmodule.mem_bot x).mp hx'
  · exfalso
    apply hf
    apply LieHom.ext
    intro x
    have hx : x ∈ K := hK ▸ LieSubmodule.mem_top x
    exact hx

private theorem rankOneComponents_zero (f g : sl₂ℂ →ₗ⁅ℝ⁆ sl₂ℂ)
    (hf : ∀ (z : ℂ) x, f (z • x) = star z • f x)
    (hc : ∀ x y, ⁅f x, g y⁆ = 0) : f = 0 ∨ g = 0 := by
  by_cases hz : f = 0
  · exact Or.inl hz
  · refine Or.inr (LieHom.ext fun y => ?_)
    letI : LieAlgebra.IsSimple ℂ sl₂ℂ := sl2_simple ℂ
    have hy : g y ∈ LieAlgebra.center ℂ sl₂ℂ := by
      apply (LieModule.mem_maxTrivSubmodule ℂ sl₂ℂ sl₂ℂ (g y)).2
      intro x
      obtain ⟨z, rfl⟩ := rankOneComponent_surjective f hf hz x
      exact hc z y
    rw [LieAlgebra.center_eq_bot] at hy
    exact (LieSubmodule.mem_bot _).mp hy

private theorem rankOneFactorAction (σ : Conjugation (sl₂ℂ × sl₂ℂ)) :
    (∀ x : sl₂ℂ × sl₂ℂ, σ.map x = ((σ.map (x.1, 0)).1, (σ.map (0, x.2)).2)) ∨
    (∀ x : sl₂ℂ × sl₂ℂ, σ.map x = ((σ.map (0, x.2)).1, (σ.map (x.1, 0)).2)) := by
  let L := sl₂ℂ
  let a := (LieHom.fst ℝ L L).comp (σ.map.comp (LieHom.inl ℝ L L))
  let b := (LieHom.fst ℝ L L).comp (σ.map.comp (LieHom.inr ℝ L L))
  let c := (LieHom.snd ℝ L L).comp (σ.map.comp (LieHom.inl ℝ L L))
  let d := (LieHom.snd ℝ L L).comp (σ.map.comp (LieHom.inr ℝ L L))
  have ha (z : ℂ) (x : L) : a (z • x) = star z • a x := by
    simpa [a] using congrArg Prod.fst (σ.antilinear z (x, 0))
  have hc (z : ℂ) (x : L) : c (z • x) = star z • c x := by
    simpa [c] using congrArg Prod.snd (σ.antilinear z (x, 0))
  have hcomm (x y : L) : ⁅σ.map (x, 0), σ.map (0, y)⁆ = 0 := by
    rw [← σ.map.map_lie, show ⁅((x, 0) : L × L), ((0, y) : L × L)⁆ = 0 by simp, map_zero]
  have hab : a = 0 ∨ b = 0 :=
    rankOneComponents_zero a b ha (fun x y => congrArg Prod.fst (hcomm x y))
  have hcd : c = 0 ∨ d = 0 :=
    rankOneComponents_zero c d hc (fun x y => congrArg Prod.snd (hcomm x y))
  have he (x : L × L) : σ.map x = (a x.1 + b x.2, c x.1 + d x.2) := by
    calc
      σ.map x = σ.map ((x.1, 0) + (0, x.2)) := by simp
      _ = σ.map (x.1, 0) + σ.map (0, x.2) := map_add _ _ _
      _ = _ := rfl
  rcases hab with hab | hab <;> rcases hcd with hcd | hcd
  · have hz (x : L) : σ.map (x, 0) = σ.map 0 := by simp [he, hab, hcd]
    exact (sl2_simple ℂ).non_abelian (⟨fun x y =>
      by rw [show x = 0 from congrArg Prod.fst (σ.involutive.injective (hz x)), zero_lie]⟩) |>.elim
  · exact Or.inr fun x => by
      change σ.map x = (b x.2, c x.1)
      simpa [hab, hcd] using he x
  · exact Or.inl fun x => by
      change σ.map x = (a x.1, d x.2)
      simpa [hab, hcd] using he x
  · have hz (x : L) : σ.map (0, x) = σ.map 0 := by simp [he, hab, hcd]
    exact (sl2_simple ℂ).non_abelian (⟨fun x y =>
      by rw [show x = 0 from congrArg Prod.snd (σ.involutive.injective (hz x)), zero_lie]⟩) |>.elim


private theorem rankOnePreserved (σ : Conjugation (sl₂ℂ × sl₂ℂ))
    (h : ∀ x : sl₂ℂ × sl₂ℂ, σ.map x = ((σ.map (x.1, 0)).1, (σ.map (0, x.2)).2)) :
    ∃ α β : Conjugation sl₂ℂ, σ = productConjugation α β := by
  let L := sl₂ℂ
  let a := (LieHom.fst ℝ L L).comp (σ.map.comp (LieHom.inl ℝ L L))
  let b := (LieHom.snd ℝ L L).comp (σ.map.comp (LieHom.inr ℝ L L))
  have hzero : σ.map ((0, 0) : L × L) = (0, 0) := map_zero σ.map
  have h₁ (x : L) : σ.map (x, 0) = (a x, 0) := by simpa [a, hzero] using h (x, 0)
  have h₂ (x : L) : σ.map (0, x) = (0, b x) := by simpa [b, hzero] using h (0, x)
  let α : Conjugation L :=
    { map := a
      antilinear := fun c x => by simpa [a] using congrArg Prod.fst (σ.antilinear c (x, 0))
      involutive := fun x => by
        have hx := σ.involutive (x, (0 : L))
        rw [h₁, h₁] at hx
        exact congrArg Prod.fst hx }
  let β : Conjugation L :=
    { map := b
      antilinear := fun c x => by simpa [b] using congrArg Prod.snd (σ.antilinear c (0, x))
      involutive := fun x => by
        have hx := σ.involutive ((0 : L), x)
        rw [h₂, h₂] at hx
        exact congrArg Prod.snd hx }
  exact ⟨α, β, Conjugation.ext_map (LieHom.ext h)⟩

private def rankOneGraphEquiv (σ : Conjugation (sl₂ℂ × sl₂ℂ))
    (h : ∀ x : sl₂ℂ × sl₂ℂ, σ.map x = ((σ.map (0, x.2)).1, (σ.map (x.1, 0)).2)) :
    σ.fixed ≃ₗ⁅ℝ⁆ sl₂ℂ := by
  let L := sl₂ℂ
  let b := (LieHom.fst ℝ L L).comp (σ.map.comp (LieHom.inr ℝ L L))
  let c := (LieHom.snd ℝ L L).comp (σ.map.comp (LieHom.inl ℝ L L))
  have hzero : σ.map ((0, 0) : L × L) = (0, 0) := map_zero σ.map
  have h₁ (x : L) : σ.map (x, 0) = (0, c x) := by simpa [c, hzero] using h (x, 0)
  have h₂ (x : L) : σ.map (0, x) = (b x, 0) := by simpa [b, hzero] using h (0, x)
  have hi (x : L) : b (c x) = x := by
    have hx := σ.involutive (x, (0 : L))
    rw [h₁, h₂] at hx
    exact congrArg Prod.fst hx
  exact
    { toFun := fun x => x.val.1
      invFun := fun x => ⟨(x, c x), (h (x, c x)).trans (Prod.ext (hi x) rfl)⟩
      left_inv := fun x => by
        have hx : σ.map x.val = x.val := x.property
        have h' := congrArg (fun v : L × L => v.2) ((h x.val).symm.trans hx)
        apply Subtype.ext
        exact Prod.ext rfl h'
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := rfl }

private theorem rankOneProductClassify (σ : Conjugation (sl₂ℂ × sl₂ℂ)) :
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ (su 2 × su 2)) ∨
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ (sl₂ℝ × sl₂ℝ)) ∨
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ sl₂ℂ) ∨
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ (su 2 × sl₂ℝ)) := by
  rcases rankOneFactorAction σ with h | h
  · obtain ⟨α, β, rfl⟩ := rankOnePreserved σ h
    obtain ⟨a, _⟩ := fixed_complexification α
    obtain ⟨b, _⟩ := fixed_complexification β
    let e := fixedProductEquiv α β
    rcases rankOneClassification ⟨a⟩ with hf | hf <;>
      rcases rankOneClassification ⟨b⟩ with hg | hg <;>
      obtain ⟨f⟩ := hf <;> obtain ⟨g⟩ := hg
    · exact Or.inl ⟨e.trans (productEquiv f g)⟩
    · exact Or.inr (Or.inr (Or.inr ⟨e.trans (productEquiv f g)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e.trans
        ((productEquiv f g).trans (LieEquiv.prodComm ℝ _ _))⟩))
    · exact Or.inr (Or.inl ⟨e.trans (productEquiv f g)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rankOneGraphEquiv σ h⟩))

private theorem rankOneProductIndices :
    negativeIndex (su 2 × su 2) = 6 ∧
    negativeIndex (sl₂ℝ × sl₂ℝ) = 2 ∧
    negativeIndex (su 2 × sl₂ℝ) = 4 := by
  obtain ⟨ω, a, ha, hai, hω, _, hform, _, hfixed⟩ := RealFormsTypeA.unitary_model 2 0
  have eqω := compact_model_unique _ _ hω
  subst ω
  obtain ⟨e⟩ := unitaryEndpoint (n := 2) (by decide) (Or.inr rfl)
    (involutionConjugation RealFormsTypeA.compactConjugation a ha hai) hform
  obtain ⟨b, hb, hbi, ⟨f⟩, ⟨g⟩⟩ := split_model_with_compact 2
  have hC := RealFormsTypeA.compactConjugation_isCompact (Blocks 2 0)
  have hS := RealFormsTypeA.compactConjugation_isCompact (Fin 2)
  have hka : Module.finrank ℂ (complexFixed a) = 3 := by
    have h := blockFixed_finrank (show 0 < 2 + 0 by decide) a hfixed
    omega
  have hkb : Module.finrank ℂ (complexFixed b) = 1 :=
    g.toLinearEquiv.finrank_eq.trans (OrthogonalCompactGeometry.orthogonal_dimensions ℂ 2).1
  refine ⟨?_, ?_, ?_⟩
  · rw [← negativeIndex_eq (productEquiv e e), productIndex hC hC ha ha hai hai, hka]
  · rw [negativeIndex_eq (productEquiv f f), productIndex hS hS hb hb hbi hbi, hkb]
  · rw [negativeIndex_eq (productEquiv e.symm f), productIndex hC hS ha hb hai hbi, hka, hkb]

private theorem complexRankOneRealIndex : negativeIndex sl₂ℂ = 3 := by
  let L := sl₂ℂ
  let ω : Conjugation L := RealFormsTypeA.compactConjugation
  let Ω := productConjugation ω ω
  let θ := LieEquiv.prodComm ℂ L L
  have hc : Intertwines Ω Ω θ := fun _ => rfl
  have hi : Function.Involutive θ := fun _ => rfl
  let σ := involutionConjugation Ω θ hc hi
  have hGraph (x : L × L) : σ.map x = ((σ.map (0, x.2)).1, (σ.map (x.1, 0)).2) := rfl
  let e := rankOneGraphEquiv σ hGraph
  let f : complexFixed θ ≃ₗ⁅ℂ⁆ L :=
    { toFun := fun x => x.val.1
      invFun := fun x => ⟨(x, x), rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl (congrArg Prod.fst x.property).symm)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := rfl }
  have hω := RealFormsTypeA.compactConjugation_isCompact (Fin 2)
  obtain ⟨basis, _⟩ := sl2_basis ℂ
  exact (negativeIndex_eq e).symm.trans
    ((CartanDecompositionSignature.killing_indices Ω θ hc hi (productIsCompact hω hω)).1.trans
      (f.toLinearEquiv.finrank_eq.trans (Module.finrank_eq_card_basis basis)))

end RankOneProduct

section OrthogonalFour

private theorem d2ProductModels {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    (h : Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ so (Fin 4))) :
    (negativeIndex A = 6 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ (su 2 × su 2))) ∨
    (negativeIndex A = 2 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ (sl₂ℝ × sl₂ℝ))) ∨
    (negativeIndex A = 3 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ sl₂ℂ)) ∨
    (negativeIndex A = 4 ∧ Nonempty (A ≃ₗ⁅ℝ⁆ (su 2 × sl₂ℝ))) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := d2_complex
  let g := e.trans f
  let ρ := RealForms.coefficientConjugation A
  let σ := ρ.transport g
  have hg : Intertwines ρ σ g := by
    intro x
    change g (ρ.map (g.symm (g x))) = g (ρ.map x)
    rw [g.symm_apply_apply]
  obtain ⟨u, _⟩ := coefficient_fixed_equiv A
  obtain ⟨v, _⟩ := restrict_complex_isomorphism ρ σ g hg
  let w := u.trans v
  obtain ⟨hcc, hss, hcs⟩ := rankOneProductIndices
  rcases rankOneProductClassify σ with h | h | h | h <;> obtain ⟨j⟩ := h
  · exact Or.inl ⟨(negativeIndex_eq (w.trans j)).trans hcc, ⟨w.trans j⟩⟩
  · exact Or.inr (Or.inl ⟨(negativeIndex_eq (w.trans j)).trans hss, ⟨w.trans j⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(negativeIndex_eq (w.trans j)).trans complexRankOneRealIndex,
      ⟨w.trans j⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(negativeIndex_eq (w.trans j)).trans hcs, ⟨w.trans j⟩⟩))

theorem d2_compact : d2_compact_type := by
  obtain ⟨c⟩ := compact_signature 4
  have h := signatureIndex 4 0 (by decide)
  rcases d2ProductModels (signatureComplexification 4 0 4 rfl) with
    ⟨_, ⟨e⟩⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
  · exact ⟨c.symm.trans e⟩
  all_goals rw [h] at h'; norm_num at h'

theorem d2_split : d2_split_type := by
  have h := signatureIndex 2 2 (by decide)
  rcases d2ProductModels (signatureComplexification 2 2 4 rfl) with
    ⟨h', _⟩ | ⟨_, e⟩ | ⟨h', _⟩ | ⟨h', _⟩
  · rw [h] at h'; norm_num at h'
  · exact e
  all_goals rw [h] at h'; norm_num at h'

theorem d2_lorentz : d2_lorentz_type := by
  have h := signatureIndex 3 1 (by decide)
  rcases d2ProductModels (signatureComplexification 3 1 4 rfl) with
    ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, e⟩ | ⟨h', _⟩
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · exact e
  · rw [h] at h'; norm_num at h'

theorem d2_quaternionic : d2_quaternionic_type := by
  have h := starIndex 2 (by decide)
  rcases d2ProductModels (starComplexification 2 4 rfl) with
    ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, e⟩
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · exact e

theorem d2_abstract_classification : d2_abstract_classification_type := by
  intro A _ _
  constructor
  · intro h
    rcases d2ProductModels h with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
    · obtain ⟨f⟩ := d2_compact
      exact ⟨.compact, ⟨e.trans f.symm⟩⟩
    · obtain ⟨f⟩ := d2_split
      exact ⟨.split, ⟨e.trans f.symm⟩⟩
    · obtain ⟨f⟩ := d2_lorentz
      exact ⟨.lorentz, ⟨e.trans f.symm⟩⟩
    · obtain ⟨f⟩ := d2_quaternionic
      exact ⟨.quaternionic, ⟨e.trans f.symm⟩⟩
  · rintro ⟨i, ⟨e⟩⟩
    obtain ⟨S, hS, ⟨f⟩⟩ := d2_models_real_forms i
    exact ⟨(complexifyEquiv (e.trans f)).trans (LieEquiv.ofBijective (complexifyMap S) hS)⟩

theorem d2_classification : d2_classification_type := by
  intro S hS
  exact (d2_abstract_classification S).1 ⟨LieEquiv.ofBijective (complexifyMap S) hS⟩

end OrthogonalFour


section CompactUnitary

open OrthogonalCompactGeometry (unitaryAlgebra)
open private cartan_maximal_compact compactSubalgebraEquiv complexMatrix_quaternionic
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsOrthogonal

private def scalarPart (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (z / 2) • 1

private theorem scalarPart_trace (z : ℂ) : (scalarPart z).trace = z := by
  simp [scalarPart, Matrix.trace_smul, smul_eq_mul]

private theorem scalarPart_skew {z : ℂ} (hz : star z = -z) :
    (scalarPart z)ᴴ = -scalarPart z := by
  rw [scalarPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  rw [show star (z / 2) = -(z / 2) by simp [hz, neg_div], neg_smul]

private def rankTwoUnitarySumHom : (su 2 × unitaryAlgebra 1) →ₗ⁅ℝ⁆ unitaryAlgebra 2 where
  toFun x := ⟨x.1.val.val + scalarPart (x.2.val 0 0), by
    have hx : x.1.val.valᴴ = -x.1.val.val := x.1.property
    have ht : x.2.valᴴ = -x.2.val := x.2.property
    have hz : star (x.2.val 0 0) = -(x.2.val 0 0) := congrFun (congrFun ht 0) 0
    change (x.1.val.val + scalarPart (x.2.val 0 0))ᴴ = _
    rw [Matrix.conjTranspose_add, hx, scalarPart_skew hz, neg_add]⟩
  map_add' x y := by
    apply Subtype.ext
    change x.1.val.val + y.1.val.val + scalarPart (x.2.val 0 0 + y.2.val 0 0) =
      (x.1.val.val + scalarPart (x.2.val 0 0)) + (y.1.val.val + scalarPart (y.2.val 0 0))
    unfold scalarPart
    rw [add_div, add_smul]
    abel
  map_smul' r x := by
    apply Subtype.ext
    change r • x.1.val.val + scalarPart ((r : ℂ) * x.2.val 0 0) =
      r • (x.1.val.val + scalarPart (x.2.val 0 0))
    rw [smul_add]
    congr 1
    rw [scalarPart, scalarPart, ← Complex.real_smul, ← smul_assoc, smul_div_assoc]
  map_lie' {x y} := by
    have hz : (⁅x.2, y.2⁆ : unitaryAlgebra 1).val 0 0 = 0 := by
      change (x.2.val * y.2.val - y.2.val * x.2.val) 0 0 = 0
      simp [Matrix.mul_apply, mul_comm]
    apply Subtype.ext
    change x.1.val.val * y.1.val.val - y.1.val.val * x.1.val.val +
      scalarPart ((⁅x.2, y.2⁆ : unitaryAlgebra 1).val 0 0) =
      (x.1.val.val + scalarPart (x.2.val 0 0)) * (y.1.val.val + scalarPart (y.2.val 0 0)) -
      (y.1.val.val + scalarPart (y.2.val 0 0)) * (x.1.val.val + scalarPart (x.2.val 0 0))
    rw [hz]
    simp [scalarPart, mul_add, add_mul, smul_smul, mul_comm]
    abel

private theorem rankTwoUnitarySum_bijective : Function.Bijective rankTwoUnitarySumHom := by
  constructor
  · apply (injective_iff_map_eq_zero rankTwoUnitarySumHom).2
    intro x hx
    have hv : x.1.val.val + scalarPart (x.2.val 0 0) = 0 := congrArg Subtype.val hx
    have ht := congrArg Matrix.trace hv
    have hx₁ : x.1.val.val.trace = 0 := x.1.val.property
    rw [Matrix.trace_add, hx₁, zero_add, scalarPart_trace, Matrix.trace_zero] at ht
    have hu : x.2 = 0 := by
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      exact ht
    have hs : x.1 = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [ht, scalarPart] using hv
    exact Prod.ext hs hu
  · intro X
    let z := X.val.trace
    have hX : X.valᴴ = -X.val := X.property
    have hz : star z = -z := by
      change star X.val.trace = -X.val.trace
      rw [← Matrix.trace_conjTranspose, hX, Matrix.trace_neg]
    let X₀ := X.val - scalarPart z
    have ht : X₀.trace = 0 := by simp [X₀, scalarPart_trace, z]
    have hs : X₀ᴴ = -X₀ := by
      change (X.val - scalarPart z)ᴴ = -(X.val - scalarPart z)
      rw [Matrix.conjTranspose_sub, hX, scalarPart_skew hz, neg_sub]
      abel
    let Y : unitaryAlgebra 1 := ⟨fun _ _ => z, by
      ext i j
      exact hz⟩
    refine ⟨(⟨⟨X₀, ht⟩, hs⟩, Y), Subtype.ext ?_⟩
    change X₀ + scalarPart z = X.val
    exact sub_add_cancel _ _

theorem d2_quaternionic_compact : d2_quaternionic_compact_type := by
  let ω := coefficientConjugation (Fin 2 ⊕ Fin 2)
  let h := quaternionic_orthogonal 2
  let hs : quaternionicMatrix 2 * quaternionicMatrix 2 = 1 ∨
      quaternionicMatrix 2 * quaternionicMatrix 2 = -1 := Or.inr (quaternionic_square 2)
  let a := orthogonalAction (quaternionicMatrix 2) h
  have hc : IsCompact ω := coefficientCompact (by decide)
  let e := compactSubalgebraEquiv ω a (orthogonalAction_commutes h) (orthogonalAction_involutive h hs)
  obtain ⟨f⟩ := OrthogonalCompactGeometry.quaternionic_real_fixed 2 a (orthogonalAction_commutes h)
    (fun X => by rw [orthogonalAction_val, complexMatrix_quaternionic])
  exact ⟨cartan_maximal_compact ω hc a (orthogonalAction_commutes h) (orthogonalAction_involutive h hs),
    ⟨e.trans (f.trans (LieEquiv.ofBijective rankTwoUnitarySumHom rankTwoUnitarySum_bijective).symm)⟩⟩

end CompactUnitary

end LieAlgebrasAndRepresentations.RealFormLowRanks
