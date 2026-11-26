import Specs.LinearAlgebraicGroups.Albert.HermitianCoordinates
import LinearAlgebraicGroups.Composition.Adjoints
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.FinCases

/-! The weighted Hermitian matrix model before the cubic operations are introduced. -/

namespace LinearAlgebraicGroups.Albert

open LinearAlgebraicGroups.Composition
open scoped TensorProduct Matrix

abbrev Mat := HermitianSpecification.Mat
abbrev Coordinates := HermitianSpecification.Coordinates
abbrev cyclicNext := HermitianSpecification.cyclicNext
abbrev cyclicPrev := HermitianSpecification.cyclicPrev
abbrev diagonalIdempotent := @HermitianSpecification.diagonalIdempotent
abbrev block := @HermitianSpecification.block
abbrev hermitian := @HermitianSpecification.hermitian
abbrev assemble := @HermitianSpecification.assemble
noncomputable abbrev matrixBaseChange := @HermitianSpecification.matrixBaseChange
noncomputable abbrev coordinatesBaseChange := @HermitianSpecification.coordinatesBaseChange
abbrev baseChangedWeights := @HermitianSpecification.baseChangedWeights

open HermitianSpecification (weight)

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
variable {n : QuadraticForm R A} {γ : Fin 3 → Rˣ}

private theorem units_smul_mul (a b : Rˣ) (x : A) :
    (a : R) • ((b : R) • x) = ((a * b : Rˣ) : R) • x :=
  (mul_smul (a : R) (b : R) x).symm

@[simp] private theorem weight_same (γ : Fin 3 → Rˣ) (i : Fin 3) : weight γ i i = 1 := by
  simp [weight]

@[simp] private theorem weight_smul (γ : Fin 3 → Rˣ) (i j : Fin 3) (x : A) :
    weight γ i j • ((γ j : R) • x) = (γ i : R) • x := by
  rw [weight, units_smul_mul]
  simp [mul_assoc]

@[simp] private theorem unscale (a : Rˣ) (x : A) : ((a⁻¹ : Rˣ) : R) • ((a : R) • x) = x := by
  rw [units_smul_mul]
  simp

@[simp] private theorem rescale (a : Rˣ) (x : A) : (a : R) • (((a⁻¹ : Rˣ) : R) • x) = x := by
  rw [units_smul_mul]
  simp

private theorem weight_chain (γ : Fin 3 → Rˣ) (i j k : Fin 3) :
    weight γ i k * weight γ k j = weight γ i j := by
  change (((γ i * (γ k)⁻¹) * (γ k * (γ j)⁻¹) : Rˣ) : R) = _
  congr 1
  simp [mul_assoc]

private theorem conjugate_scalar (h : NormLaws n) (r : R) :
    conjugate n (r • (1 : A)) = r • (1 : A) := by
  rw [map_smul, conjugate_one h]

theorem mem_hermitian_iff [IsScalarTower R A A] [SMulCommClass R A A] (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (x : Mat A) :
    x ∈ hermitian n γ ↔
      (x.map (conjugate n))ᵀ =
        (Matrix.diagonal fun i => (γ i : R) • (1 : A)) * x *
          (Matrix.diagonal fun i => (((γ i)⁻¹ : Rˣ) : R) • (1 : A)) ∧
      ∀ i, ∃ r : R, r • (1 : A) = x i i := by
  change ((∀ i j, conjugate n (x j i) = weight γ i j • x i j) ∧ _) ↔ _
  simp only [← Matrix.ext_iff, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, ← mul_smul, weight,
    Units.val_mul, mul_comm]

theorem diagonalIdempotent_mul_self (i : Fin 3) :
    diagonalIdempotent (A := A) i * diagonalIdempotent i = diagonalIdempotent i := by
  simp [HermitianSpecification.diagonalIdempotent, Matrix.single_mul_single_same]

theorem assemble_diagonal (p : Coordinates R A) (i : Fin 3) :
    assemble n γ p i i = p.1 i • (1 : A) := by
  fin_cases i <;> rfl

theorem assemble_forward (p : Coordinates R A) (i : Fin 3) :
    assemble n γ p (cyclicNext i) (cyclicPrev i) = (γ (cyclicPrev i) : R) • p.2 i := by
  fin_cases i <;> rfl

theorem assemble_backward (p : Coordinates R A) (i : Fin 3) :
    assemble n γ p (cyclicPrev i) (cyclicNext i) =
      (γ (cyclicNext i) : R) • conjugate n (p.2 i) := by
  fin_cases i <;> rfl

private theorem entry_cases (i j : Fin 3) :
    i = j ∨ (∃ k, i = cyclicNext k ∧ j = cyclicPrev k) ∨
      (∃ k, i = cyclicPrev k ∧ j = cyclicNext k) := by
  revert i j
  decide

theorem assemble_mem (h : NormLaws n) (γ : Fin 3 → Rˣ) (p : Coordinates R A) :
    assemble n γ p ∈ hermitian n γ := by
  refine ⟨fun i j => ?_, fun i => ⟨p.1 i, (assemble_diagonal p i).symm⟩⟩
  rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · simp [assemble_diagonal, conjugate_scalar h]
  · have hc (z : A) : AdjointSpecification.conjugate n (conjugate n z) = z :=
      conjugate_involutive h z
    simp [assemble_forward, assemble_backward, hc]
  · simp [assemble_forward, assemble_backward]

theorem assemble_eq_sum (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (p : Coordinates R A) :
    assemble n γ p = ∑ i, (p.1 i • diagonalIdempotent i + block n γ i (p.2 i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianSpecification.assemble, HermitianSpecification.diagonalIdempotent,
      HermitianSpecification.block, HermitianSpecification.cyclicNext,
      HermitianSpecification.cyclicPrev, Fin.sum_univ_three,
      Matrix.add_apply, Fin.isValue]

section Blocks

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem diagonalIdempotent_mem (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) (i : Fin 3) :
    diagonalIdempotent (A := A) i ∈ hermitian n γ := by
  have hp := assemble_mem h.toNormLaws γ (Pi.single i 1, 0)
  rw [assemble_eq_sum, Finset.sum_eq_single i] at hp
  · simpa [HermitianSpecification.block] using hp
  · intro j _ hji
    simp [hji, HermitianSpecification.block]
  · simp

theorem block_mem (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) (i : Fin 3) (c : A) :
    block n γ i c ∈ hermitian n γ := by
  have hp := assemble_mem h.toNormLaws γ (0, Pi.single i c)
  rw [assemble_eq_sum, Finset.sum_eq_single i] at hp
  · simpa using hp
  · intro j _ hji
    simp [hji, HermitianSpecification.block]
  · simp

end Blocks

/-- The unit line splits even when the trace of the unit is zero. -/
private theorem exists_scalar_reader [Module.Projective R A] (h : NormLaws n) :
    ∃ f : A →ₗ[R] R, f 1 = 1 := by
  let d := Finsupp.linearCombination R (id : A → A)
  obtain ⟨s, hs⟩ := (Module.projective_def (R := R) (P := A)).mp inferInstance
  let b := Module.Free.chooseBasis R (A →₀ R)
  let : LinearOrder (Module.Free.ChooseBasisIndex R (A →₀ R)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let B := (n.comp d).toBilin b
  have hd : d (s (1 : A)) = 1 := hs 1
  refine ⟨(B.flip (s 1)).comp s, ?_⟩
  change B (s 1) (s 1) = 1
  rw [← LinearMap.BilinMap.toQuadraticMap_apply, QuadraticMap.toQuadraticMap_toBilin]
  change n (d (s 1)) = 1
  rw [hd, h.map_one]

private theorem scalar_injective [Module.Projective R A] (h : NormLaws n) :
    Function.Injective (fun r : R => r • (1 : A)) := by
  obtain ⟨f, hf⟩ := exists_scalar_reader h
  intro a b hab
  simpa [map_smul, hf] using congrArg f hab

/-- The coordinate map, with codomain the submodule defined by the matrix conditions. -/
def coordinateMap (h : NormLaws n) (γ : Fin 3 → Rˣ) :
    Coordinates R A →ₗ[R] hermitian n γ where
  toFun p := ⟨assemble n γ p, assemble_mem h γ p⟩
  map_add' p q := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;>
      simp [Matrix.add_apply, assemble_diagonal, assemble_forward,
        assemble_backward, add_smul, smul_add]
  map_smul' r p := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;>
      simp [Matrix.smul_apply, assemble_diagonal, assemble_forward,
        assemble_backward, mul_smul, smul_comm r]

@[simp] theorem coordinateMap_apply (h : NormLaws n) (γ : Fin 3 → Rˣ) (p : Coordinates R A) :
    (coordinateMap h γ p : Mat A) = assemble n γ p := rfl

private theorem coordinateMap_bijective [Module.Projective R A] (h : NormLaws n)
    (γ : Fin 3 → Rˣ) : Function.Bijective (coordinateMap h γ) := by
  constructor
  · intro p q hpq
    have hm : assemble n γ p = assemble n γ q := congrArg Subtype.val hpq
    apply Prod.ext
    · funext i
      apply scalar_injective h
      simpa only [assemble_diagonal] using congrArg (fun x : Mat A => x i i) hm
    · funext i
      have hi := congrArg (fun x : Mat A => x (cyclicNext i) (cyclicPrev i)) hm
      rw [assemble_forward, assemble_forward] at hi
      simpa only [unscale] using congrArg (fun x : A => ((γ (cyclicPrev i))⁻¹ : Rˣ).val • x) hi
  · intro x
    have hx := x.property.1
    have hd := x.property.2
    choose a ha using hd
    let c i := ((γ (cyclicPrev i))⁻¹ : Rˣ).val • (x : Mat A) (cyclicNext i) (cyclicPrev i)
    refine ⟨(a, c), ?_⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change assemble n γ (a, c) i j = (x : Mat A) i j
    rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · rw [assemble_diagonal]
      exact ha i
    · rw [assemble_forward]
      exact rescale _ _
    · rw [assemble_backward]
      change (γ (cyclicNext k) : R) • conjugate n (c k) = (x : Mat A) (cyclicPrev k) (cyclicNext k)
      have hw := hx (cyclicNext k) (cyclicPrev k)
      apply (conjugate_involutive h).injective
      rw [map_smul, conjugate_involutive h, hw]
      change (γ (cyclicNext k) : R) •
          (((γ (cyclicPrev k))⁻¹ : Rˣ).val • (x : Mat A) (cyclicNext k) (cyclicPrev k)) = _
      rw [units_smul_mul]
      rfl

/-- Unique scalar diagonal and cyclic octonion coordinates. -/
noncomputable def coordinateEquiv [Module.Projective R A] (h : NormLaws n)
    (γ : Fin 3 → Rˣ) : Coordinates R A ≃ₗ[R] hermitian n γ :=
  LinearEquiv.ofBijective (coordinateMap h γ) (coordinateMap_bijective h γ)

@[simp] theorem coordinateEquiv_apply [Module.Projective R A] (h : NormLaws n)
    (γ : Fin 3 → Rˣ) (p : Coordinates R A) :
    (coordinateEquiv h γ p : Mat A) = assemble n γ p := rfl

private theorem coordinates_projective [Module.Projective R A] :
    Module.Projective R (Coordinates R A) := by
  obtain ⟨s, hs⟩ := (Module.projective_def (R := R) (P := A)).mp inferInstance
  let d := Finsupp.linearCombination R (id : A → A)
  exact Module.Projective.of_split
    (LinearMap.id.prodMap (s.compLeft (Fin 3)))
    (LinearMap.id.prodMap (d.compLeft (Fin 3)))
    (LinearMap.ext fun p => Prod.ext rfl (funext fun i => hs (p.2 i)))

section Rank

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem coordinates_decomposition (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) :
    ∃ e : Coordinates R A ≃ₗ[R] hermitian n γ, ∀ p, (e p : Mat A) = assemble n γ p := by
  let := h.projective
  exact ⟨coordinateEquiv h.toNormLaws γ, coordinateEquiv_apply h.toNormLaws γ⟩


theorem hermitian_rank (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) :
    Module.Finite R (hermitian n γ) ∧ Module.Projective R (hermitian n γ) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (hermitian n γ) p = 27 := by
  let := h.finite
  let := h.projective
  let e := coordinateEquiv h.toNormLaws γ
  let : Module.Projective R (Coordinates R A) := coordinates_projective
  refine ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    Module.Projective.of_equiv' e, fun p => ?_⟩
  have : Nontrivial R := p.nontrivial
  let : Module.Projective R (Fin 3 → A) := Module.Projective.of_split
    (LinearMap.inr R (Fin 3 → R) (Fin 3 → A))
    (LinearMap.snd R (Fin 3 → R) (Fin 3 → A)) (LinearMap.ext fun _ => rfl)
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  change Module.rankAtStalk (Fin 3 → R) p + Module.rankAtStalk (Fin 3 → A) p = 27
  rw [Module.rankAtStalk_pi (fun _ : Fin 3 => R), Module.rankAtStalk_pi (fun _ : Fin 3 => A)]
  simp [h.rank_eight, finsum_eq_sum_of_fintype]

end Rank

theorem hermitian_dimension {k : Type u} [Field k] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    {n : QuadraticForm k A} (h : IsOctonionNorm n) (γ : Fin 3 → kˣ) :
    Module.finrank k (hermitian n γ) = 27 := by
  let := h.finite
  let := h.projective
  rw [← (coordinateEquiv h.toNormLaws γ).finrank_eq]
  change Module.finrank k ((Fin 3 → k) × (Fin 3 → A)) = 27
  have hA : Module.finrank k A = 8 := by
    let p : PrimeSpectrum k := Classical.choice inferInstance
    simpa using h.rank_eight p
  simp [Module.finrank_prod, Module.finrank_pi_fintype, hA]

private theorem transpose_entry (h : NormLaws n) (x : hermitian n γ) (i j : Fin 3) :
    (x : Mat A) j i = weight γ i j • conjugate n ((x : Mat A) i j) := by
  have hx := congrArg (conjugate n) (x.property.1 i j)
  change conjugate n (conjugate n ((x : Mat A) j i)) =
    conjugate n (weight γ i j • (x : Mat A) i j) at hx
  rw [show conjugate n (conjugate n ((x : Mat A) j i)) = (x : Mat A) j i
    from conjugate_involutive h _, map_smul] at hx
  exact hx

section SymmetrizedProduct

variable [IsScalarTower R A A] [SMulCommClass R A A]

private theorem conjugate_product_entry (h : NormLaws n) (x y : hermitian n γ) (i j : Fin 3) :
    conjugate n (((x : Mat A) * (y : Mat A)) j i) =
      weight γ i j • ((y : Mat A) * (x : Mat A)) i j := by
  rw [Matrix.mul_apply, map_sum, Matrix.mul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [conjugate_mul h, y.property.1 i k, x.property.1 k j,
    smul_mul_assoc, mul_smul_comm, smul_smul, weight_chain]

theorem symmetrized_mul_mem (h : NormLaws n) (x y : hermitian n γ) :
    (x : Mat A) * (y : Mat A) + (y : Mat A) * (x : Mat A) ∈ hermitian n γ := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, map_add, conjugate_product_entry h, conjugate_product_entry h,
      Matrix.add_apply, smul_add, add_comm]
  · refine ⟨∑ j, weight γ i j * n.polarBilin ((x : Mat A) i j) ((y : Mat A) i j), ?_⟩
    rw [Finset.sum_smul, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [transpose_entry h y i j, transpose_entry h x i j, mul_smul_comm, mul_smul_comm,
      ← smul_add, polar_mul_conjugate h, mul_smul]

theorem jordan_product_mem (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) (two : Rˣ)
    (_ : (two : R) = 2) (x y : hermitian n γ) :
    (((two⁻¹ : Rˣ) : R) • ((x : Mat A) * (y : Mat A) + (y : Mat A) * (x : Mat A)))
      ∈ hermitian n γ :=
  (hermitian n γ).smul_mem _ (symmetrized_mul_mem h.toNormLaws x y)

/-- The symmetrized matrix product when two is invertible. -/
def jordanProduct (h : IsOctonionNorm n) (two : Rˣ) (htwo : (two : R) = 2)
    (x y : hermitian n γ) : hermitian n γ :=
  ⟨_, jordan_product_mem h γ two htwo x y⟩


end SymmetrizedProduct

section BaseChange

variable (S : Type w) [CommRing S] [Algebra R S]

@[simp] theorem matrixBaseChange_tmul (s : S) (x : Mat A) (i j : Fin 3) :
    matrixBaseChange S (s ⊗ₜ[R] x) i j = s ⊗ₜ[R] x i j := rfl

theorem coordinatesBaseChange_tmul (s : S) (p : Coordinates R A) :
    coordinatesBaseChange S (s ⊗ₜ[R] p) =
      (fun i => s * algebraMap R S (p.1 i), fun i => s ⊗ₜ[R] p.2 i) := by
  apply Prod.ext
  · funext i
    simp [HermitianSpecification.coordinatesBaseChange, TensorProduct.piScalarRight_apply,
      Algebra.smul_def, mul_comm]
  · rfl

private theorem algebraMap_smul_tmul (r : R) (s : S) (a : A) :
    algebraMap R S r • (s ⊗ₜ[R] a) = s ⊗ₜ[R] (r • a) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem assemble_baseChange_tmul [Module.Projective R A] (n : QuadraticForm R A)
    (γ : Fin 3 → Rˣ) (s : S) (p : Coordinates R A) :
    assemble (normBaseChange S n) (baseChangedWeights S γ)
        (coordinatesBaseChange S (s ⊗ₜ[R] p)) =
      matrixBaseChange S (s ⊗ₜ[R] assemble n γ p) := by
  apply Matrix.ext
  intro i j
  rw [matrixBaseChange_tmul, coordinatesBaseChange_tmul]
  rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · rw [assemble_diagonal, assemble_diagonal]
    change (s * algebraMap R S (p.1 i)) • (1 ⊗ₜ[R] (1 : A)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm s, ← Algebra.smul_def,
      TensorProduct.smul_tmul]
  · rw [assemble_forward, assemble_forward]
    exact algebraMap_smul_tmul S _ _ _
  · rw [assemble_backward, assemble_backward]
    change algebraMap R S (γ (cyclicNext k) : R) •
        conjugate (normBaseChange S n) (s ⊗ₜ[R] p.2 k) = _
    rw [conjugate_baseChange, LinearMap.baseChange_tmul, algebraMap_smul_tmul]

/-- Scalar extension of the Hermitian module, transported via its coordinates. -/
noncomputable def hermitianBaseChange (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) :
    letI := h.projective
    S ⊗[R] hermitian n γ ≃ₗ[S]
      hermitian (normBaseChange S n) (baseChangedWeights S γ) :=
  letI := h.projective
  let hS : IsOctonionNorm (normBaseChange S n) := octonion_norm_baseChange h S
  letI := hS.projective
  (coordinateEquiv h.toNormLaws γ).symm.baseChange R S _ _ ≪≫ₗ
    coordinatesBaseChange S ≪≫ₗ coordinateEquiv hS.toNormLaws (baseChangedWeights S γ)

theorem hermitianBaseChange_tmul (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ)
    (s : S) (x : hermitian n γ) (p : Coordinates R A) :
    letI := h.projective
    (x : Mat A) = assemble n γ p →
      (hermitianBaseChange S h γ (s ⊗ₜ[R] x) : Mat (S ⊗[R] A)) =
        assemble (normBaseChange S n) (baseChangedWeights S γ)
          (coordinatesBaseChange S (s ⊗ₜ[R] p)) := by
  let := h.projective
  intro hx
  have hp : (coordinateEquiv h.toNormLaws γ).symm x = p := by
    apply (coordinateEquiv h.toNormLaws γ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext hx
  simp [hermitianBaseChange, hp]

theorem hermitianBaseChange_inclusion (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) :
    letI := h.projective
    ∀ z, (hermitianBaseChange S h γ z : Mat (S ⊗[R] A)) =
      matrixBaseChange S ((hermitian n γ).subtype.baseChange S z) := by
  let := h.projective
  let M := hermitian (normBaseChange S n) (baseChangedWeights S γ)
  suffices eq : M.subtype.comp (hermitianBaseChange S h γ).toLinearMap =
      (matrixBaseChange S).toLinearMap.comp ((hermitian n γ).subtype.baseChange S) from
    fun z => LinearMap.congr_fun eq z
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  change (hermitianBaseChange S h γ (s ⊗ₜ[R] x) : Mat (S ⊗[R] A)) =
    matrixBaseChange S ((hermitian n γ).subtype.baseChange S (s ⊗ₜ[R] x))
  let p := (coordinateEquiv h.toNormLaws γ).symm x
  have hx : (x : Mat A) = assemble n γ p :=
    (congrArg Subtype.val ((coordinateEquiv h.toNormLaws γ).apply_symm_apply x)).symm
  rw [hermitianBaseChange_tmul S h γ s x p hx, assemble_baseChange_tmul,
    LinearMap.baseChange_tmul]
  exact congrArg (fun m : Mat A => matrixBaseChange S (s ⊗ₜ[R] m)) hx.symm

theorem hermitianBaseChange_coordinates (h : IsOctonionNorm n) (γ : Fin 3 → Rˣ) :
    letI := h.projective
    let hS : IsOctonionNorm (normBaseChange S n) := octonion_norm_baseChange h S
    letI := hS.projective
    ((coordinateEquiv h.toNormLaws γ).baseChange R S _ _).trans (hermitianBaseChange S h γ) =
      (coordinatesBaseChange S).trans (coordinateEquiv hS.toNormLaws (baseChangedWeights S γ)) := by
  let := h.projective
  let hS : IsOctonionNorm (normBaseChange S n) := octonion_norm_baseChange h S
  let := hS.projective
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s p
  simp [hermitianBaseChange]

end BaseChange

theorem hermitian_baseChange : HermitianSpecification.hermitianBaseChange := by
  intro R A _ _ _ S _ _ _ _ n h γ
  change IsOctonionNorm n at h
  let := h.projective
  let hS : IsOctonionNorm (normBaseChange S n) := octonion_norm_baseChange h S
  let := hS.projective
  exact ⟨hermitianBaseChange S h γ, coordinateEquiv h.toNormLaws γ,
    coordinateEquiv hS.toNormLaws (baseChangedWeights S γ),
    coordinateEquiv_apply h.toNormLaws γ, coordinateEquiv_apply hS.toNormLaws (baseChangedWeights S γ),
    hermitianBaseChange_inclusion S h γ, hermitianBaseChange_coordinates S h γ⟩


end LinearAlgebraicGroups.Albert
