import MathGenome.Internal.Specs.D05.M10.Rational
import MathGenome.Internal.D05.M10.Rational.Presentation
import MathGenome.Internal.D05.M10.InvariantFactorComputation
import MathGenome.Internal.D05.M10.Companion
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Transvection

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace D05.M10.Rational
open Specs.D05.M10.Rational
open D05.M10.Smith
variable {K : Type*} [Field K] {n : ℕ}

/-- The elementary change matrix is obtained by operating on the identity. -/
def operationMatrix (op : Operation K n n) : Matrix (Fin n) (Fin n) K[X] := op.apply 1

def isRow : Operation K n n → Bool
  | .swapRows .. | .addRow .. | .scaleRow .. => true
  | _ => false

lemma operation_factorization (op : Operation K n n) (M : Matrix (Fin n) (Fin n) K[X]) :
    op.apply M = if isRow op then operationMatrix op * M else M * operationMatrix op := by
  classical
  cases op with
  | swapRows i j =>
    change _ = operationMatrix _ * M
    simp only [operationMatrix, Operation.apply]
    apply Matrix.ext; intro a b
    change M (Equiv.swap i j a) b = ∑ k, (if Equiv.swap i j a = k then 1 else 0) * M k b
    simp
  | swapCols i j =>
    change _ = M * operationMatrix _
    simp only [operationMatrix, Operation.apply]
    apply Matrix.ext; intro a b
    change M a (Equiv.swap i j b) = ∑ k, M a k * (if k = Equiv.swap i j b then 1 else 0)
    simp
  | addRow i j h q =>
    have heq : operationMatrix (Operation.addRow i j h q) = Matrix.transvection i j q := by
      apply Matrix.ext; intro a b
      by_cases ha : a = i
      · subst a; simp [operationMatrix, Operation.apply, Matrix.transvection, Matrix.single, Matrix.one_apply]
      · simp [operationMatrix, Operation.apply, Matrix.transvection, Matrix.single, Matrix.one_apply, ha, Ne.symm ha]
    change _ = operationMatrix _ * M
    rw [heq]
    apply Matrix.ext; intro a b
    by_cases ha : a = i
    · subst a; simp [Operation.apply]
    · simp [Operation.apply, ha]
  | addCol i j h q =>
    have heq : operationMatrix (Operation.addCol i j h q) = Matrix.transvection j i q := by
      apply Matrix.ext; intro a b
      by_cases hb : b = i
      · subst b; simp [operationMatrix, Operation.apply, Matrix.transvection, Matrix.single, Matrix.one_apply, eq_comm]
      · simp [operationMatrix, Operation.apply, Matrix.transvection, Matrix.single, Matrix.one_apply, hb, Ne.symm hb]
    change _ = M * operationMatrix _
    rw [heq]
    apply Matrix.ext; intro a b
    by_cases hb : b = i
    · subst b; simp [Operation.apply]
    · simp [Operation.apply, hb]
  | scaleRow i c =>
    have heq : operationMatrix (Operation.scaleRow i c) =
        Matrix.diagonal (fun a => if a = i then C (c : K) else 1) := by
      apply Matrix.ext; intro a b
      by_cases ha : a = i <;> by_cases hb : a = b <;>
        simp_all [operationMatrix, Operation.apply, Matrix.one_apply]
    change _ = operationMatrix _ * M
    rw [heq]
    apply Matrix.ext; intro a b
    by_cases ha : a = i <;> simp [Operation.apply, Matrix.diagonal_mul, ha]
  | scaleCol j c =>
    have heq : operationMatrix (Operation.scaleCol j c) =
        Matrix.diagonal (fun b => if b = j then C (c : K) else 1) := by
      apply Matrix.ext; intro a b
      by_cases ha : b = j <;> by_cases hb : a = b <;>
        simp_all [operationMatrix, Operation.apply, Matrix.one_apply]
    change _ = M * operationMatrix _
    rw [heq]
    apply Matrix.ext; intro a b
    by_cases hb : b = j <;> simp [Operation.apply, Matrix.mul_diagonal, hb, mul_comm]

lemma isRow_inverse (op : Operation K n n) : isRow op.inverse = isRow op := by cases op <;> rfl

lemma operationMatrix_inverse (op : Operation K n n) :
    operationMatrix op.inverse * operationMatrix op = 1 ∧
      operationMatrix op * operationMatrix op.inverse = 1 := by
  have h₁ := (InvariantFactorComputation.operation_inverse K n n op (1 : Matrix (Fin n) (Fin n) K[X])).1
  have h₂ := (InvariantFactorComputation.operation_inverse K n n op (1 : Matrix (Fin n) (Fin n) K[X])).2
  change op.inverse.apply (operationMatrix op) = 1 at h₁
  change op.apply (operationMatrix op.inverse) = 1 at h₂
  rw [operation_factorization, isRow_inverse] at h₁
  rw [operation_factorization] at h₂
  cases h : isRow op <;> simp [h] at h₁ h₂
  · exact ⟨h₂, h₁⟩
  · exact ⟨h₁, h₂⟩

/-- An explicit invertible linear change, over K[x], for each operation. -/
def operationEquiv (op : Operation K n n) : (Fin n → K[X]) ≃ₗ[K[X]] (Fin n → K[X]) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (operationMatrix op))
    (Matrix.toLin' (operationMatrix op.inverse))
    (by rw [← Matrix.toLin'_mul, (operationMatrix_inverse op).2, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, (operationMatrix_inverse op).1, Matrix.toLin'_one])

lemma cokernel_operation (op : Operation K n n) (M : Matrix (Fin n) (Fin n) K[X]) :
    Nonempty (Cokernel M ≃ₗ[K[X]] Cokernel (op.apply M)) := by
  rw [operation_factorization]
  by_cases h : isRow op = true
  · rw [ite_eq_left h]
    refine ⟨Submodule.Quotient.equiv _ _ (operationEquiv op) ?_⟩
    change (LinearMap.range (Matrix.toLin' M)).map (Matrix.toLin' (operationMatrix op)) = _
    rw [Matrix.toLin'_mul, LinearMap.range_comp]
  · rw [ite_eq_right h]
    have hr : LinearMap.range (Matrix.toLin' (operationMatrix op)) = ⊤ :=
      LinearMap.range_eq_top.mpr (operationEquiv op).surjective
    have he : LinearMap.range (Matrix.toLin' (M * operationMatrix op)) =
        LinearMap.range (Matrix.toLin' M) := by
      rw [Matrix.toLin'_mul, LinearMap.range_comp_of_range_eq_top _ hr]
    exact ⟨Submodule.quotEquivOfEq _ _ he.symm⟩

theorem smith_cokernel : Specs.D05.M10.Rational.smith_cokernel := by
  intro K _ n M ops
  induction ops generalizing M with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons op ops ih =>
    obtain ⟨e⟩ := cokernel_operation op M
    obtain ⟨f⟩ := ih (op.apply M)
    exact ⟨e.trans f⟩

/-- The range of a diagonal presentation consists of coordinatewise multiples. -/
lemma diagonal_range (d : Fin n → K[X]) :
    LinearMap.range (Matrix.toLin' (Matrix.diagonal d)) =
      Submodule.pi Set.univ (fun i => (Ideal.span {d i} : Submodule K[X] K[X])) := by
  classical
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    intro i hi
    apply Ideal.mem_span_singleton.mpr
    exact ⟨g i, by simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]⟩
  · intro hf
    have hd : ∀ i, d i ∣ f i := fun i => Ideal.mem_span_singleton.mp (hf i (Set.mem_univ i))
    choose g hg using hd
    refine ⟨g, ?_⟩
    funext i
    simpa [Matrix.toLin'_apply, Matrix.mulVec_diagonal] using (hg i).symm

def diagonalCokernelEquiv (d : Fin n → K[X]) :
    Cokernel (Matrix.diagonal d) ≃ₗ[K[X]] (∀ i, Residue (d i)) :=
  (Submodule.quotEquivOfEq _ _ (diagonal_range d)).trans
    (Submodule.quotientPi (fun i => (Ideal.span {d i} : Submodule K[X] K[X])))

lemma residue_one_subsingleton : Subsingleton (Residue (1 : K[X])) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact Ideal.span_singleton_one

/-- Removing a unit diagonal entry removes a zero module, without changing
any of the other coordinates. -/
def discardUnits (d : Fin n → K[X]) (s : Finset (Fin n))
    (hs : ∀ i, i ∈ s ↔ d i ≠ 1) :
    (∀ i, Residue (d i)) ≃ₗ[K[X]] (∀ i : s, Residue (d i.val)) := by
  classical
  let f : (∀ i, Residue (d i)) →ₗ[K[X]] (∀ i : s, Residue (d i.val)) :=
    { toFun := fun z i => z i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro z w h
    funext i
    by_cases hi : i ∈ s
    · exact congrFun h ⟨i, hi⟩
    · have hd : d i = 1 := not_ne_iff.mp (mt (hs i).mpr hi)
      have : Subsingleton (Residue (d i)) := hd ▸ residue_one_subsingleton
      exact Subsingleton.elim _ _
  · intro z
    refine ⟨fun i => if hi : i ∈ s then z ⟨i, hi⟩ else 0, ?_⟩
    funext i
    exact dite_eq_left i.property

/-- Smith reduction of X I - [T], followed by deletion of the zero quotients. -/
lemma cyclic_quotient_decomposition {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ (r : ℕ) (d : Fin r → K[X]),
      (∀ i, (d i).Monic) ∧ (∀ i, 0 < (d i).natDegree) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧
      Nonempty (Module.AEval' T ≃ₗ[K[X]] (∀ i, Residue (d i))) := by
  classical
  let n := Module.finrank K V
  let b := Module.finBasis K V
  let A := LinearMap.toMatrix b b T
  obtain ⟨_, _, _, ops, d, hred, hg, htop, hprod, hunit⟩ :=
    InvariantFactorComputation.characteristic_smith K n A
  obtain ⟨ep, _⟩ := Presentation.presentation_iso b T
  have ep' : Nonempty (Module.AEval' T ≃ₗ[K[X]] Cokernel A.charmatrix) := by
    exact ⟨ep.symm⟩
  obtain ⟨ec⟩ := smith_cokernel A.charmatrix ops
  have hdiag : Smith.run ops A.charmatrix = Matrix.diagonal (fun i : Fin n => d i.val) := by
    rw [hred.2.2.2]
    apply Matrix.ext; intro i j
    simp [InvariantFactorComputation.rectDiagonal, Matrix.diagonal_apply, Fin.ext_iff]
  rw [hdiag] at ec
  let s : Finset (Fin n) := Finset.univ.filter (fun i => d i.val ≠ 1)
  have hs (i : Fin n) : i ∈ s ↔ d i.val ≠ 1 := by simp [s]
  let q := s.orderIsoOfFin rfl
  let D : Fin s.card → K[X] := fun i => d (q i).val.val
  obtain ⟨ep'⟩ := ep'
  let E := ep'.trans (ec.trans ((diagonalCokernelEquiv (fun i : Fin n => d i.val)).trans
    ((discardUnits (fun i : Fin n => d i.val) s hs).trans
      (LinearEquiv.piCongrLeft K[X] (fun i : s => Residue (d i.val.val)) q.toEquiv).symm)))
  refine ⟨s.card, D, ?_, ?_, ?_, ⟨E⟩⟩
  · intro i
    exact hred.2.2.1.1 _ (q i).val.isLt
  · intro i
    have hm : (D i).Monic := hred.2.2.1.1 _ (q i).val.isLt
    exact hm.natDegree_pos.mpr ((hs _).mp (q i).property)
  · intro i j hij
    exact hred.2.2.1.2.2 _ _ (show (q i).val.val ≤ (q j).val.val from q.monotone hij)

/-- The K-space quotient and the usual quotient algebra have the same
representatives and scalar operations. -/
def residueEquiv (d : K[X]) : Residue d ≃ₗ[K] AdjoinRoot d where
  toFun := fun z => z
  invFun := fun z => z
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def residueBasis (d : K[X]) (hd : d.Monic) :
    Module.Basis (Fin d.natDegree) K (Residue d) :=
  (Companion.quotientBasis K d hd).map (residueEquiv d).symm

/-- Multiplication by X on the quotient, viewed as a K-linear operator. -/
def residueX (d : K[X]) : Module.End K (Residue d) where
  toFun := fun z => (X : K[X]) • z
  map_add' := smul_add (X : K[X])
  map_smul' := fun a z => smul_comm _ _ _

lemma residueX_matrix (d : K[X]) (hd : d.Monic) (hpos : 0 < d.natDegree) :
    LinearMap.toMatrix (residueBasis d hd) (residueBasis d hd) (residueX d) =
      Companion.companionMatrix K d := by
  have h := Companion.matrix_representation d hd hpos
  change LinearMap.toMatrix (Companion.quotientBasis K d hd)
    (Companion.quotientBasis K d hd) (Companion.multiplication K d) = _ at h
  unfold residueBasis
  rw [LinearMap.toMatrix_map_right, LinearMap.toMatrix_map_left]
  have ht : (((residueEquiv d).symm.symm.toLinearMap).comp (residueX d)).comp
      (residueEquiv d).symm.toLinearMap = Companion.multiplication K d := by
    ext z
    rfl
  rw [ht]
  exact h

/-- The componentwise X-action on the finite external direct sum. -/
def productX {r : ℕ} (d : Fin r → K[X]) : Module.End K (∀ i, Residue (d i)) where
  toFun z i := residueX (d i) (z i)
  map_add' := fun z w => by funext i; exact (residueX (d i)).map_add _ _
  map_smul' := fun a z => by funext i; exact (residueX (d i)).map_smul a _

lemma productX_matrix {r : ℕ} (d : Fin r → K[X]) (hm : ∀ i, (d i).Monic)
    (hp : ∀ i, 0 < (d i).natDegree) :
    LinearMap.toMatrix (Pi.basis (fun i => residueBasis (d i) (hm i)))
      (Pi.basis (fun i => residueBasis (d i) (hm i))) (productX d) =
        Matrix.blockDiagonal' (fun i => Companion.companionMatrix K (d i)) := by
  classical
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  simp only [LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply]
  by_cases h : i = j
  · subst j
    conv_rhs => rw [Matrix.blockDiagonal'_apply_eq]
    simp only [productX, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Pi.single_eq_same]
    simpa only [LinearMap.toMatrix_apply] using congrArg (fun M : Matrix (Fin (d i).natDegree) (Fin (d i).natDegree) K => M a b)
      (residueX_matrix (d i) (hm i) (hp i))
  · conv_rhs => rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp only [productX, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Pi.single_eq_of_ne h, map_zero, map_zero, Finsupp.zero_apply]

/-- Transport the residue bases across the polynomial-module isomorphism. -/
lemma companion_basis_of_equiv {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V)
    {r : ℕ} (d : Fin r → K[X]) (hm : ∀ i, (d i).Monic)
    (hp : ∀ i, 0 < (d i).natDegree)
    (e : Module.AEval' T ≃ₗ[K[X]] (∀ i, Residue (d i))) :
    ∃ b : Module.Basis (Σ i, Fin (d i).natDegree) K V,
      LinearMap.toMatrix b b T = Matrix.blockDiagonal' (fun i => Companion.companionMatrix K (d i)) ∧
      (∑ i, (d i).natDegree) = Module.finrank K V := by
  classical
  let E : (∀ i, Residue (d i)) ≃ₗ[K] V :=
    (e.symm.restrictScalars K).trans (Module.AEval'.of T).symm
  let B := Pi.basis (fun i => residueBasis (d i) (hm i))
  let b := B.map E
  have hT (z : ∀ i, Residue (d i)) : T (E z) = E ((X : K[X]) • z) := by
    apply (Module.AEval'.of T).injective
    change (Module.AEval'.of T) (T ((Module.AEval'.of T).symm (e.symm z))) =
      (Module.AEval'.of T) ((Module.AEval'.of T).symm (e.symm ((X : K[X]) • z)))
    rw [← Module.AEval'.X_smul_of, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, map_smul]
  have ht : (E.symm.toLinearMap.comp T).comp E.toLinearMap = productX d := by
    apply LinearMap.ext; intro z
    change E.symm (T (E z)) = _
    rw [hT, E.symm_apply_apply]
    rfl
  refine ⟨b, ?_, ?_⟩
  · change LinearMap.toMatrix (B.map E) (B.map E) T = _
    rw [LinearMap.toMatrix_map_right, LinearMap.toMatrix_map_left, ht]
    exact productX_matrix d hm hp
  · simpa using (Module.finrank_eq_card_basis b).symm

theorem rational_form : Specs.D05.M10.Rational.rational_form := by
  intro K V _ _ _ _ T
  obtain ⟨r, d, hm, hp, hd, ⟨e⟩⟩ := cyclic_quotient_decomposition T
  exact ⟨r, d, hm, hp, hd, ⟨e⟩, companion_basis_of_equiv T d hm hp e⟩

theorem zero_blocks : Specs.D05.M10.Rational.zero_blocks := by
  intro K V _ _ _ _ hV T
  let b : Module.Basis (Σ _ : Fin 0, Fin (0 : K[X]).natDegree) K V := basisOfFinrankZero hV
  refine ⟨b, ?_⟩
  apply Matrix.ext
  rintro ⟨i, _⟩ j
  exact Fin.elim0 i

end D05.M10.Rational
