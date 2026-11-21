import MathGenome.Internal.Specs.D05.M10.Rational.Presentation
import MathGenome.Internal.D05.M04.Coordinates
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M03.FirstIso

/-! The polynomial presentation of a finite-dimensional operator.
All polynomial-module objects are the canonical definitions in the independent
Specs. The proof follows the source's finite telescoping reduction; in
particular, no structure theorem for modules or cyclic decomposition is used. -/

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace D05.M10.Rational.Presentation
open Specs.D05.M10.Rational.Presentation

theorem matrix_powers : Specs.D05.M10.Rational.Presentation.matrix_powers := by
  intro K V _ _ _ n b T j v
  change (LinearMap.toMatrix b b T ^ j) *ᵥ b.repr v = b.repr ((T ^ j) v)
  rw [LinearMap.toMatrix_pow]
  exact (T ^ j).toMatrix_mulVec_repr b b v

theorem polynomial_action : Specs.D05.M10.Rational.Presentation.polynomial_action := by
  intro K V _ _ _ T p v
  rfl

theorem variable_action : Specs.D05.M10.Rational.Presentation.variable_action := by
  intro K V _ _ _ T v
  exact Module.AEval'.X_smul_of T v

theorem phi_linear : Specs.D05.M10.Rational.Presentation.phi_linear := by
  intro K V _ _ _ n b T p f g
  exact ⟨(phi b T).map_add f g, (phi b T).map_smul p f⟩

theorem phi_constant {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V) (v : V) :
    phi b T (constant b v) = Module.AEval'.of T v := by
  change (∑ i, C (b.repr v i) • Module.AEval'.of T (b i)) = _
  simp only [Module.AEval.C_smul, ← map_smul, ← map_sum]
  rw [b.sum_repr]

theorem phi_expansion : Specs.D05.M10.Rational.Presentation.phi_expansion := by
  intro K V _ _ _ n b T s v
  simp only [map_sum, map_smul, phi_constant, Module.AEval'.X_pow_smul_of,
    Module.End.smul_def]

theorem phi_surjective : Specs.D05.M10.Rational.Presentation.phi_surjective := by
  intro K V _ _ _ n b T w
  exact ⟨constant b ((Module.AEval'.of T).symm w), by rw [phi_constant]; simp⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ}

lemma constant_coordinates (b : Module.Basis (Fin n) K V) (x : Fin n → K) :
    constant b (b.equivFun.symm x) = fun i => C (x i) := by
  funext i
  change C (b.equivFun (b.equivFun.symm x) i) = _
  rw [b.equivFun.apply_symm_apply]

theorem finite_expansion : Specs.D05.M10.Rational.Presentation.finite_expansion := by
  intro K V _ _ _ n b f
  classical
  let d := Finset.univ.sup (fun i => (f i).natDegree)
  refine ⟨Finset.range (d + 1), fun j => b.equivFun.symm (fun i => (f i).coeff j), ?_⟩
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, constant_coordinates, smul_eq_mul]
  calc
    f i = ∑ j ∈ Finset.range (d + 1), C ((f i).coeff j) * X ^ j :=
      Polynomial.as_sum_range_C_mul_X_pow' _
        (Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (f i).natDegree) (Finset.mem_univ i)))
    _ = _ := Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Multiplying a constant column by the literal matrix X I - A. -/
lemma relation_constant (b : Module.Basis (Fin n) K V) (T : Module.End K V) (v : V) :
    relationMap b T (constant b v) =
      (X : K[X]) • constant b v - constant b (T v) := by
  funext i
  change ((Matrix.diagonal (fun _ => X) - (operatorMatrix b T).map C) *ᵥ
    (fun j => C (b.repr v j))) i = X * C (b.repr v i) - C (b.repr (T v) i)
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  congr 1
  exact (RingHom.map_mulVec C (operatorMatrix b T) (fun j => b.repr v j) i).symm.trans
    (congrArg C (congrFun (T.toMatrix_mulVec_repr b b v) i))

lemma telescopingSum_succ (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (j : ℕ) (v : V) :
    telescopingSum b T (j + 1) v =
      (X : K[X]) • telescopingSum b T j v + constant b ((T ^ j) v) := by
  classical
  unfold telescopingSum
  rw [Finset.sum_range_succ, Finset.smul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l < j := Finset.mem_range.mp hl
  rw [smul_smul, ← pow_succ']
  congr 2
  omega

theorem telescoping_identity (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (j : ℕ) (v : V) :
    relationMap b T (telescopingSum b T j v) =
      ((X : K[X]) ^ j) • constant b v - constant b ((T ^ j) v) := by
  induction j with
  | zero => simp [telescopingSum]
  | succ j ih =>
    rw [telescopingSum_succ, map_add, map_smul, ih, relation_constant]
    rw [smul_sub, smul_smul, ← pow_succ']
    have hp : T ((T ^ j) v) = (T ^ (j + 1)) v := by rw [pow_succ']; rfl
    rw [hp]
    abel

/-- Relations evaluate to zero: first on constants, then on every finite expansion. -/
lemma phi_relation (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (f : Fin n → K[X]) : phi b T (relationMap b T f) = 0 := by
  obtain ⟨s, v, rfl⟩ := finite_expansion b f
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  have hc : phi b T (relationMap b T (constant b (v j))) = 0 := by
    rw [relation_constant, map_sub, map_smul, phi_constant, phi_constant,
      Module.AEval'.X_smul_of, sub_self]
  rw [hc, smul_zero]

/-- Subtracting the evaluated constant leaves an explicit relation. -/
lemma polynomial_reduction (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (f : Fin n → K[X]) :
    ∃ g, relationMap b T g = f - constant b ((Module.AEval'.of T).symm (phi b T f)) := by
  obtain ⟨s, v, hf⟩ := finite_expansion b f
  refine ⟨∑ j ∈ s, telescopingSum b T j (v j), ?_⟩
  simp only [map_sum, telescoping_identity, Finset.sum_sub_distrib]
  rw [← hf, ← map_sum]
  congr 2
  rw [hf, phi_expansion, LinearEquiv.symm_apply_apply]

theorem phi_kernel : Specs.D05.M10.Rational.Presentation.phi_kernel := by
  intro K V _ _ _ n b T
  ext f
  constructor
  · intro hf
    have hz : phi b T f = 0 := hf
    obtain ⟨g, hg⟩ := polynomial_reduction b T f
    exact ⟨g, by simpa [hz] using hg⟩
  · rintro ⟨g, rfl⟩
    exact phi_relation b T g

theorem presentation_iso : Specs.D05.M10.Rational.Presentation.presentation_iso := by
  intro K V _ _ _ n b T
  let e := (Submodule.quotEquivOfEq _ _ (phi_kernel b T).symm).trans
    ((phi b T).quotKerEquivOfSurjective (phi_surjective b T))
  refine ⟨e, ?_⟩
  intro f
  simp [e, Submodule.quotEquivOfEq_mk]

theorem matrix_presentation : Specs.D05.M10.Rational.Presentation.matrix_presentation := by
  intro K V _ _ _ n b T A hA
  subst A
  exact presentation_iso b T

end D05.M10.Rational.Presentation
