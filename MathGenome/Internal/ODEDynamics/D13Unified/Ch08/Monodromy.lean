import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Monodromy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.EvolutionMatrix
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
open Set
open scoped Matrix Matrix.Norms.Elementwise

namespace D13Unified.Ch08.Monodromy
open D13Unified.Ch07.EvolutionMatrix
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

def principalMatrix (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (t : ℝ) :=
  U wholeTime A t 0

def monodromy (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (T : ℝ) := principalMatrix A T

def monodromyAt (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (T s : ℝ) :=
  U wholeTime A (s + T) s

def complexify (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  M.map Complex.ofRealHom

def floquetMultipliers (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ) : Multiset ℂ :=
  (monodromy A T).charpoly.roots

def realFloquetMultipliers (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ) : Multiset ℂ :=
  (complexify (monodromy A T)).charpoly.roots

lemma wholeTime_mem (t : ℝ) : t ∈ wholeTime.carrier := mem_univ t

lemma continuous_U (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (hA : Continuous A) (s : ℝ) :
    Continuous (fun t => U wholeTime A t s) :=
  continuousOn_univ.mp (continuousOn_U wholeTime A s (wholeTime_mem s) hA.continuousOn)

lemma hasDerivAt_U (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (hA : Continuous A) (s t : ℝ) :
    HasDerivAt (fun r => U wholeTime A r s) (A t * U wholeTime A t s) t :=
  (hasDerivWithinAt_U wholeTime A s (wholeTime_mem s) hA.continuousOn t
    (wholeTime_mem t)).hasDerivAt (by simp [wholeTime])

theorem principal_properties : Specs.D13Unified.Ch08.Monodromy.PrincipalProperties := by
  intro 𝕂 _ n A hA
  exact ⟨U_self wholeTime A 0 (wholeTime_mem 0) hA.continuousOn,
    fun s => (inverse 𝕂 n wholeTime A hA.continuousOn 0 (wholeTime_mem 0) s
      (wholeTime_mem s)).1⟩

/-- A simultaneous period shift preserves the normalized IVP, hence the actual
chosen evolution matrices agree by uniqueness, for every pair of real times. -/
lemma evolution_periodic (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (hA : Continuous A)
    (T : ℝ) (hper : Function.Periodic A T) (t s : ℝ) :
    U wholeTime A (t + T) (s + T) = U wholeTime A t s := by
  have heq := solution_unique wholeTime A
    (fun r => U wholeTime A (r + T) (s + T)) (fun r => U wholeTime A r s)
    s (wholeTime_mem s) hA.continuousOn
    ((continuous_U A hA (s + T)).comp (continuous_id.add continuous_const)).continuousOn
    (continuous_U A hA s).continuousOn
    (by rw [U_self wholeTime A (s + T) (wholeTime_mem _) hA.continuousOn,
      U_self wholeTime A s (wholeTime_mem _) hA.continuousOn])
    (by
      intro r _
      have hd := (hasDerivAt_U A hA (s + T) (r + T)).scomp r
        ((hasDerivAt_id r).add_const T)
      convert! hd.hasDerivWithinAt using 1
      simp only [hper r, one_smul])
    (fun r _ => (hasDerivAt_U A hA s r).hasDerivWithinAt)
  exact heq (wholeTime_mem t)

/-- This one-period identity is used internally to prove the base-time formula. -/
lemma principal_period (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (hA : Continuous A)
    (T : ℝ) (hper : Function.Periodic A T) (s : ℝ) :
    principalMatrix A (s + T) = principalMatrix A s * monodromy A T := by
  change U wholeTime A (s + T) 0 = U wholeTime A s 0 * U wholeTime A T 0
  rw [← composition 𝕂 n wholeTime A hA.continuousOn T (wholeTime_mem T)
    0 (wholeTime_mem 0) (s + T) (wholeTime_mem _)]
  have hp : U wholeTime A (s + T) T = U wholeTime A s 0 := by
    simpa only [zero_add] using evolution_periodic A hA T hper s 0
  rw [hp]

theorem conjugacy : Specs.D13Unified.Ch08.Monodromy.Conjugacy := by
  intro 𝕂 _ n A T hA _ hper s
  change monodromyAt A T s = principalMatrix A s * monodromy A T *
    (principalMatrix A s)⁻¹
  rw [← principal_period A hA T hper s]
  change U wholeTime A (s + T) s = U wholeTime A (s + T) 0 * (U wholeTime A s 0)⁻¹
  rw [(inverse 𝕂 n wholeTime A hA.continuousOn 0 (wholeTime_mem 0) s
    (wholeTime_mem s)).2]
  exact (composition 𝕂 n wholeTime A hA.continuousOn 0 (wholeTime_mem 0)
    s (wholeTime_mem s) (s + T) (wholeTime_mem _)).symm

theorem similarity : Specs.D13Unified.Ch08.Monodromy.Similarity := by
  intro 𝕂 _ n A T hA hT hper s
  obtain ⟨P, hP⟩ := (principal_properties 𝕂 n A hA).2 s
  change (P : Matrix (Fin n) (Fin n) 𝕂) = principalMatrix A s at hP
  refine ⟨P, ?_⟩
  have hc : monodromyAt A T s = principalMatrix A s * monodromy A T *
      (principalMatrix A s)⁻¹ := conjugacy 𝕂 n A T hA hT hper s
  rw [← hP] at hc
  change monodromyAt A T s = (P : Matrix (Fin n) (Fin n) 𝕂) *
    monodromy A T * ((P⁻¹) : Matrix (Fin n) (Fin n) 𝕂)
  simpa using hc

/-- The real inclusion is a continuous real-linear map on the actual matrix
spaces, which lets uniqueness identify the real and complex IVPs. -/
private def complexifyCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := complexify
      map_add' := by intro M N; ext i j; simp [complexify]
      map_smul' := by intro c M; ext i j; simp [complexify] }

lemma continuous_complexify : Continuous (complexify (n := n)) :=
  complexifyCLM.continuous

lemma complexify_one : complexify (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  exact Complex.ofRealHom.mapMatrix.map_one

lemma complexify_mul (M N : Matrix (Fin n) (Fin n) ℝ) :
    complexify (M * N) = complexify M * complexify N := by
  exact Complex.ofRealHom.mapMatrix.map_mul M N

lemma hasDerivAt_complexify {Y : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Y' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hd : HasDerivAt Y Y' t) :
    HasDerivAt (fun r => complexify (Y r)) (complexify Y') t :=
  complexifyCLM.hasFDerivAt.comp_hasDerivAt t hd

theorem complexification_bridge :
    Specs.D13Unified.Ch08.Monodromy.ComplexificationBridge := by
  intro n A hA t s
  let B : ℝ → Matrix (Fin n) (Fin n) ℂ := fun r => complexify (A r)
  have hB : Continuous B := continuous_complexify.comp hA
  have heq := solution_unique wholeTime B
    (fun r => U wholeTime B r s) (fun r => complexify (U wholeTime A r s))
    s (wholeTime_mem s) hB.continuousOn
    (continuous_U B hB s).continuousOn
    (continuous_complexify.comp (continuous_U A hA s)).continuousOn
    (by rw [U_self wholeTime B s (wholeTime_mem s) hB.continuousOn,
      U_self wholeTime A s (wholeTime_mem s) hA.continuousOn, complexify_one])
    (fun r _ => (hasDerivAt_U B hB s r).hasDerivWithinAt)
    (by
      intro r _
      have hd := hasDerivAt_complexify (hasDerivAt_U A hA s r)
      rw [complexify_mul] at hd
      exact hd.hasDerivWithinAt)
  exact heq (wholeTime_mem t)

theorem real_monodromy_bridge : Specs.D13Unified.Ch08.Monodromy.RealMonodromyBridge := by
  intro n A hA T
  have hb := complexification_bridge n A hA T 0
  refine ⟨hb, ?_⟩
  change (U wholeTime (fun r => complexify (A r)) T 0).charpoly.roots =
    (complexify (U wholeTime A T 0)).charpoly.roots
  exact congrArg (fun M => M.charpoly.roots) hb

lemma monodromy_charpoly (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (hA : Continuous A)
    (T : ℝ) (hT : 0 < T) (hper : Function.Periodic A T) (s : ℝ) :
    (monodromyAt A T s).charpoly = (monodromy A T).charpoly := by
  obtain ⟨P, hP⟩ := similarity 𝕂 n A T hA hT hper s
  change monodromyAt A T s = (P : Matrix (Fin n) (Fin n) 𝕂) *
    monodromy A T * ((P⁻¹) : Matrix (Fin n) (Fin n) 𝕂) at hP
  rw [hP]
  simp

theorem multiplier_independence : Specs.D13Unified.Ch08.Monodromy.MultiplierIndependence := by
  constructor
  · intro n A T hA hT hper s
    change (monodromyAt A T s).charpoly.roots = (monodromy A T).charpoly.roots
    rw [monodromy_charpoly A hA T hT hper s]
  · intro n A T hA hT hper s
    change ((monodromyAt A T s).map Complex.ofRealHom).charpoly.roots =
      ((monodromy A T).map Complex.ofRealHom).charpoly.roots
    rw [Matrix.charpoly_map, Matrix.charpoly_map, monodromy_charpoly A hA T hT hper s]

theorem multiplier_counts : Specs.D13Unified.Ch08.Monodromy.MultiplierCounts := by
  constructor <;> intro n A T μ <;> exact Polynomial.count_roots _

/-- This bridge makes explicit why a characteristic-polynomial root is an
eigenvalue, rather than relying on terminology for the multiset definition. -/
lemma mem_charpoly_roots_iff (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    μ ∈ M.charpoly.roots ↔ ∃ v : Fin n → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [Polynomial.mem_roots M.charpoly_monic.ne_zero,
    ← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, hv.apply_eq_smul⟩
  · rintro ⟨v, hv, heq⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr heq, hv⟩

theorem multiplier_eigenvalues : Specs.D13Unified.Ch08.Monodromy.MultiplierEigenvalues := by
  constructor <;> intro n A T μ <;> exact mem_charpoly_roots_iff _ μ

lemma card_charpoly_roots (M : Matrix (Fin n) (Fin n) ℂ) : M.charpoly.roots.card = n := by
  rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem multiplier_cardinality : Specs.D13Unified.Ch08.Monodromy.MultiplierCardinality := by
  constructor <;> intro n A T <;> exact card_charpoly_roots _

end D13Unified.Ch08.Monodromy
