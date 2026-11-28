import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.Basic
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.DeformationTransport
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import Mathlib.Tactic.Abel

/-! Change of basis of Heisenberg deformations over the truncated and formal bases. -/

noncomputable section

open scoped TensorProduct Matrix
open LieModule.Cohomology

namespace LieNotes.Heisenberg.DeformationTransport

open Specs.LieNotes.Heisenberg (ModelValue basisValue coordinatesValue)
open Specs.LieNotes.Heisenberg.DeformationTransport hiding tensorCoordinates

open _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations
  (shear pullback_spec shearEquiv bracket_normal_form coefficient bracketFormula
    quotientDualNumberEquiv quotientDualNumberEquiv_root)

universe u
variable {k A : Type u} [Field k] [CommRing A]

/-- The coordinate chart of the scalar extension, in the Heisenberg basis. -/
def tensorCoordinates : tensorCoordinatesType.{u} :=
  tensorCoordinatesValue

private theorem coordinateMatrix_action (f : Module.End k (ModelValue k))
    (p : ModelValue k) (i : Fin 3) :
    ∑ j, coefficientMatrix f i j * p.coords j = (f p).coords i := by
  change (coefficientMatrix f *ᵥ coordinatesValue k p) i = (coordinatesValue k (f p)) i
  simp [coefficientMatrix, LinearEquiv.conj_apply_apply]

theorem scalarExtension : scalarExtensionType.{u} := by
  intro k A _ _ _ f a p
  have hcoord (r : ModelValue k) :
      Specs.LieNotes.Heisenberg.DeformationTransport.tensorCoordinates (a ⊗ₜ[k] r) =
        a • constantVector (algebraMap k A) r := by
    funext i
    have hi : (basisValue k).repr r i = r.coords i := basis_repr k r i
    simp [Specs.LieNotes.Heisenberg.DeformationTransport.tensorCoordinates, constantVector,
      Module.Basis.equivFun_apply, hi, Algebra.smul_def, mul_comm]
  refine ⟨hcoord p, ?_⟩
  rw [hcoord, hcoord, map_smul]
  congr 1
  funext i
  simp only [extendedEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    constantVector, ← map_mul, ← map_sum, coordinateMatrix_action]

theorem firstOrderTransport : firstOrderTransportType.{u} := by
  intro k _ _ c c' f h
  subst c'
  exact pullback_spec (k := k) (g := Model k) c f

private theorem truncatedReduction_parameter :
    truncatedReduction k (truncatedParameter k) = DualNumber.eps :=
  AdjoinRoot.liftAlgHom_root ..

private theorem formalReduction_constant (a : k) :
    formalReduction k (PowerSeries.C a) = TrivSqZeroExt.inl a := by
  apply TrivSqZeroExt.ext
  · change PowerSeries.coeff 0 (PowerSeries.C a) = a
    simp
  · change PowerSeries.coeff 1 (PowerSeries.C a) = 0
    simp

private theorem formalReduction_parameter :
    formalReduction k PowerSeries.X = DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · change PowerSeries.coeff 0 (PowerSeries.X : PowerSeries k) = 0
    simp
  · change PowerSeries.coeff 1 (PowerSeries.X : PowerSeries k) = 1
    simp [PowerSeries.coeff_X]

private theorem dualReduction_surjective (ι : k →+* A) (ρ : A →+* DualNumber k) (t : A)
    (hι : ∀ a, ρ (ι a) = TrivSqZeroExt.inl a) (ht : ρ t = DualNumber.eps) :
    Function.Surjective ρ := by
  intro d
  refine ⟨ι d.fst + t * ι d.snd, ?_⟩
  rw [map_add, map_mul, hι, hι, ht]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul]
  · simp [TrivSqZeroExt.snd_add]

theorem modTwoReductions : modTwoReductionsType.{u} := by
  intro k _
  refine ⟨dualReduction_surjective (algebraMap k _) (truncatedReduction k).toRingHom _
      (truncatedReduction k).commutes truncatedReduction_parameter, ?_,
    dualReduction_surjective PowerSeries.C (formalReduction k) PowerSeries.X
      formalReduction_constant formalReduction_parameter, ?_⟩
  · intro a
    let X : Polynomial k := Polynomial.X
    have hle : Ideal.span {X ^ 3} ≤ Ideal.span {X ^ 2} :=
      Ideal.span_singleton_le_span_singleton.mpr ⟨X, pow_succ X 2⟩
    let π : Truncated k →ₐ[k] AdjoinRoot (X ^ 2) := Ideal.Quotient.factorₐ k hle
    have hπ : (quotientDualNumberEquiv k).toAlgHom.comp π = truncatedReduction k := by
      apply AdjoinRoot.algHom_ext
      change quotientDualNumberEquiv k (AdjoinRoot.root (X ^ 2)) =
        truncatedReduction k (truncatedParameter k)
      rw [quotientDualNumberEquiv_root, truncatedReduction_parameter]
    constructor
    · intro ha
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      have hp : AdjoinRoot.mk (X ^ 2) p = 0 := by
        apply (quotientDualNumberEquiv k).injective
        rw [map_zero]
        change ((quotientDualNumberEquiv k).toAlgHom.comp π) (AdjoinRoot.mk (X ^ 3) p) = 0
        rw [hπ]
        exact ha
      obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_zero.mp hp
      refine ⟨AdjoinRoot.mk (X ^ 3) q, ?_⟩
      change AdjoinRoot.mk (X ^ 3) p =
        (AdjoinRoot.mk (X ^ 3) X) ^ 2 * AdjoinRoot.mk (X ^ 3) q
      rw [hq, map_mul, map_pow]
    · rintro ⟨q, rfl⟩
      rw [map_mul, map_pow, truncatedReduction_parameter, DualNumber.eps_pow_two, zero_mul]
  · intro a
    rw [PowerSeries.X_pow_dvd_iff]
    constructor
    · intro h n hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · exact congrArg TrivSqZeroExt.fst h
      · exact congrArg TrivSqZeroExt.snd h
    · intro h
      exact TrivSqZeroExt.ext (h 0 (by decide)) (h 1 (by decide))

private theorem reduce_shear (ι : k →+* A) (ρ : A →+* DualNumber k) (t : A)
    (hι : ∀ a, ρ (ι a) = TrivSqZeroExt.inl a) (ht : ρ t = DualNumber.eps)
    (f : Module.End k (ModelValue k)) (p : Carrier A) :
    reduce ρ ((1 + t • extendedEnd ι f) p) = shear f (reduce ρ p) := by
  have h (i : Fin 3) :
      ρ (((1 + t • extendedEnd ι f) p) i) =
        ρ (p i) + DualNumber.eps *
          ∑ j, TrivSqZeroExt.inl (coefficientMatrix f i j) * ρ (p j) := by
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, extendedEnd, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.map_apply, map_add, map_mul, map_sum, hι, ht]
  apply Prod.ext <;> apply ModelValue.ext <;> funext i
  · change (ρ (((1 + t • extendedEnd ι f) p) i)).fst = (ρ (p i)).fst
    rw [h]
    simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul]
  · change (ρ (((1 + t • extendedEnd ι f) p) i)).snd =
      (ρ (p i)).snd + (f (reduce ρ p).1).coords i
    rw [h]
    simp only [TrivSqZeroExt.snd_add, DualNumber.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, zero_mul, one_mul, zero_add, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
    rw [← coordinateMatrix_action f (reduce ρ p).1 i]
    rfl

theorem truncatedTransport : truncatedTransportType.{u} := by
  intro k _ _ f
  let t := truncatedParameter k
  let F := extendedEnd (algebraMap k (Truncated k)) f
  let U := t • F
  have ht : t ^ 3 = 0 := by
    change AdjoinRoot.mk ((Polynomial.X : Polynomial k) ^ 3) Polynomial.X ^ 3 = 0
    rw [← map_pow]
    exact AdjoinRoot.mk_eq_zero.mpr dvd_rfl
  have hU : U ^ 3 = 0 := by simp [U, smul_pow, ht]
  have left : (1 + U) * (1 - U + U ^ 2) = 1 := by
    calc
      _ = 1 + U ^ 3 := by
        simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, pow_succ, pow_zero,
          mul_assoc]
        abel
      _ = 1 := by rw [hU, add_zero]
  have right : (1 - U + U ^ 2) * (1 + U) = 1 := by
    calc
      _ = 1 + U ^ 3 := by
        simp only [add_mul, mul_add, sub_mul, one_mul, mul_one, pow_succ, pow_zero,
          mul_assoc]
        abel
      _ = 1 := by rw [hU, add_zero]
  let T : Carrier (Truncated k) ≃ₗ[Truncated k] Carrier (Truncated k) :=
    LinearEquiv.ofLinearMap (1 + U) (1 - U + U ^ 2) left right
  refine ⟨T, rfl, ?_, ?_⟩
  · change 1 - U + U ^ 2 = 1 - t • F + t ^ 2 • F ^ 2
    rw [show U ^ 2 = t ^ 2 • F ^ 2 from smul_pow _ _ _]
  · intro p
    change reduce (truncatedReduction k).toRingHom ((1 + t • F) p) = _
    exact reduce_shear _ _ t (truncatedReduction k).commutes
      truncatedReduction_parameter f p

private abbrev Mat (R : Type u) := Matrix (Fin 3) (Fin 3) R

/-- The matrix series of the geometric inverse. -/
private def inverseSeries (M : Mat k) : Mat (PowerSeries k) :=
  Matrix.of fun i j => PowerSeries.mk fun n => ((-M) ^ n) i j

private theorem coeff_left (M : Mat k) (n : ℕ) (i j : Fin 3) :
    PowerSeries.coeff n ((M.map PowerSeries.C * inverseSeries M) i j) =
      (M * (-M) ^ n) i j := by
  simp [Matrix.mul_apply, PowerSeries.coeff_C_mul, inverseSeries]

private theorem coeff_right (M : Mat k) (n : ℕ) (i j : Fin 3) :
    PowerSeries.coeff n ((inverseSeries M * M.map PowerSeries.C) i j) =
      ((-M) ^ n * M) i j := by
  simp [Matrix.mul_apply, PowerSeries.coeff_mul_C, inverseSeries]

private theorem coeff_X_mul_succ (n : ℕ) (p : PowerSeries k) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * p) = PowerSeries.coeff n p := by
  simpa only [pow_one] using PowerSeries.coeff_X_pow_mul p 1 n

private theorem formal_left (M : Mat k) :
    (1 + (PowerSeries.X : PowerSeries k) • M.map PowerSeries.C) * inverseSeries M = 1 := by
  rw [add_mul, one_mul, smul_mul_assoc]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [inverseSeries, Matrix.one_apply, apply_ite]
  | succ n =>
    have h₁ : PowerSeries.coeff (n + 1) ((1 : Mat (PowerSeries k)) i j) = 0 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [Matrix.add_apply, map_add, Matrix.smul_apply, smul_eq_mul, coeff_X_mul_succ,
      coeff_left, h₁]
    simp only [inverseSeries, Matrix.of_apply, PowerSeries.coeff_mk]
    have h : (-M) ^ (n + 1) + M * (-M) ^ n = 0 := by
      rw [pow_succ', neg_mul, neg_add_cancel]
    simpa only [Matrix.add_apply, Matrix.zero_apply] using congrArg (fun P : Mat k => P i j) h

private theorem formal_right (M : Mat k) :
    inverseSeries M * (1 + (PowerSeries.X : PowerSeries k) • M.map PowerSeries.C) = 1 := by
  rw [mul_add, mul_one, Matrix.mul_smul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [inverseSeries, Matrix.one_apply, apply_ite]
  | succ n =>
    have h₁ : PowerSeries.coeff (n + 1) ((1 : Mat (PowerSeries k)) i j) = 0 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [Matrix.add_apply, map_add, Matrix.smul_apply, smul_eq_mul, coeff_X_mul_succ,
      coeff_right, h₁]
    simp only [inverseSeries, Matrix.of_apply, PowerSeries.coeff_mk]
    have h : (-M) ^ (n + 1) + (-M) ^ n * M = 0 := by
      rw [pow_succ, mul_neg, neg_add_cancel]
    simpa only [Matrix.add_apply, Matrix.zero_apply] using congrArg (fun P : Mat k => P i j) h

private theorem series_on_constants (f : Module.End k (ModelValue k))
    (n : ℕ) (p : ModelValue k) (i : Fin 3) :
    PowerSeries.coeff n
        ((inverseSeries (coefficientMatrix f)).toLin' (constantVector PowerSeries.C p) i) =
      (((-f) ^ n) p).coords i := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, constantVector,
    map_sum, PowerSeries.coeff_mul_C, inverseSeries, Matrix.of_apply, PowerSeries.coeff_mk]
  change Matrix.toLin' ((-coefficientMatrix f) ^ n) (coordinatesValue k p) i = _
  rw [Matrix.toLin'_pow, map_neg, coefficientMatrix, Matrix.toLin'_toMatrix']
  let e := coordinatesValue k
  change ((-(e.conjRingEquiv f)) ^ n) (e p) i = _
  rw [← map_neg e.conjRingEquiv, ← map_pow e.conjRingEquiv]
  change e (((-f) ^ n) (e.symm (e p))) i = _
  rw [e.symm_apply_apply]
  rfl

private def matrixEquiv (P Q : Mat A) (left : P * Q = 1) (right : Q * P = 1) :
    Carrier A ≃ₗ[A] Carrier A :=
  LinearEquiv.ofLinearMap P.toLin' Q.toLin'
    (by rw [← Matrix.toLin'_mul, left, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, right, Matrix.toLin'_one])

private def formalEquiv (f : Module.End k (ModelValue k)) :
    Carrier (PowerSeries k) ≃ₗ[PowerSeries k] Carrier (PowerSeries k) :=
  let M := coefficientMatrix f
  matrixEquiv _ _ (formal_left M) (formal_right M)

private theorem formalEquiv_forward (f : Module.End k (ModelValue k)) :
    (formalEquiv f).toLinearMap =
      1 + (PowerSeries.X : PowerSeries k) • extendedEnd PowerSeries.C f := by
  change Matrix.toLin' (1 + (PowerSeries.X : PowerSeries k) •
    (coefficientMatrix f).map PowerSeries.C) = _
  simp [extendedEnd, Module.End.one_eq_id]

private theorem formalEquiv_inverse (f : Module.End k (ModelValue k)) :
    (formalEquiv f).symm.toLinearMap = (inverseSeries (coefficientMatrix f)).toLin' := rfl

private theorem formalEquiv_coeff (f : Module.End k (ModelValue k))
    (n : ℕ) (p : ModelValue k) (i : Fin 3) :
    PowerSeries.coeff n ((formalEquiv f).symm (constantVector PowerSeries.C p) i) =
      (((-f) ^ n) p).coords i := by
  change PowerSeries.coeff n
    ((formalEquiv f).symm.toLinearMap (constantVector PowerSeries.C p) i) = _
  rw [formalEquiv_inverse]
  exact series_on_constants f n p i

private theorem formalEquiv_reduce (f : Module.End k (ModelValue k)) (p : Carrier (PowerSeries k)) :
    reduce (formalReduction k) (formalEquiv f p) = shear f (reduce (formalReduction k) p) := by
  change reduce (formalReduction k) ((formalEquiv f).toLinearMap p) = _
  rw [formalEquiv_forward]
  apply reduce_shear
  · exact formalReduction_constant
  · exact formalReduction_parameter

theorem formalTransport : formalTransportType.{u} := by
  intro k _ _ f
  exact ⟨formalEquiv f, formalEquiv_forward f, formalEquiv_coeff f, formalEquiv_reduce f⟩

/-- Pull back the bracket through a linear equivalence of the fixed carrier. -/
def pullback : pullbackType.{u} := pullbackValue

private theorem pullback_apply (T : Carrier A ≃ₗ[A] Carrier A) (B : LieBracket A)
    (p q : Carrier A) :
    (pullback A T B).bracket p q = T.symm (B.bracket (T p) (T q)) := rfl

private theorem pullback_symm (T : Carrier A ≃ₗ[A] Carrier A) (B : LieBracket A) :
    pullback A T (pullback A T.symm B) = B := by
  apply LieBracket.ext
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro q
  simp [pullback_apply]

theorem pullbackReduction : pullbackReductionType.{u} := by
  intro k A _ _ _ ρ B T f c c' hT hc
  have h (p q : Carrier A) :
      reduce ρ (B.bracket (T p) (T q)) =
        shear f (reduce ρ ((pullbackValue A T B).bracket p q)) := by
    rw [← hT]
    change reduce ρ (B.bracket (T p) (T q)) =
      reduce ρ (T (T.symm (B.bracket (T p) (T q))))
    rw [T.apply_symm_apply]
  have hs (p q : Carrier A) :=
    firstOrderTransport k c c' f hc (reduce ρ p) (reduce ρ q)
  constructor
  · intro hB p q
    rw [← T.apply_symm_apply p, ← T.apply_symm_apply q]
    rw [h, hB, hs, ← hT, ← hT]
  · intro hB p q
    apply (shearEquiv f).injective
    change shear f _ = shear f _
    rw [← h, hs, hB, hT, hT]

private theorem exists_congr [CharZero k] (ρ : A →+* DualNumber k)
    (c c' : twoCochain k (Model k) (Model k)) (f : Module.End k (Model k))
    (T : Carrier A ≃ₗ[A] Carrier A)
    (hT : ∀ p, reduce ρ (T p) = shear f (reduce ρ p))
    (hc : c' = c + d₁₂ k (Model k) (Model k) f) :
    (∃ B, ReducesTo ρ B c) ↔ ∃ B, ReducesTo ρ B c' := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨pullback A T B, (pullbackReduction k A ρ B T f c c' hT hc).2 hB⟩
  · rintro ⟨B, hB⟩
    refine ⟨pullback A T.symm B, (pullbackReduction k A ρ _ T f c c' hT hc).1 ?_⟩
    change ReducesTo ρ (pullback A T (pullback A T.symm B)) c'
    rwa [pullback_symm]

theorem extensionsEquivalent : extensionsEquivalentType.{u} := by
  intro k _ _ c c' f hc
  obtain ⟨T, _, _, hT⟩ := truncatedTransport k f
  obtain ⟨U, _, _, hU⟩ := formalTransport k f
  exact ⟨exists_congr _ c c' f T hT hc, exists_congr _ c c' f U hU hc⟩

theorem actualExtensionsEquivalent : actualExtensionsEquivalentType.{u} := by
  intro k _ _ D D' f hf
  let c := coefficient D
  let c' := c + d₁₂ k (Model k) (Model k) f
  have hD := bracket_normal_form D
  have hD' (p q : Model k × Model k) : D'.bracket p q = bracketFormula c' p q := by
    apply (shearEquiv f).injective
    change shear f (D'.bracket p q) = shear f (bracketFormula c' p q)
    rw [hf, hD, firstOrderTransport k c c' f rfl]
  simpa only [Extends, ReducesTo, hD, hD'] using extensionsEquivalent k c c' f rfl

end LieNotes.Heisenberg.DeformationTransport
