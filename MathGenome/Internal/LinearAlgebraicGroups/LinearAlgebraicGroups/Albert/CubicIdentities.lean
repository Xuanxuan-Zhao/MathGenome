import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.CubicIdentities
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.HermitianCoordinates
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! Cubic identities in weighted Hermitian coordinates over a commutative ring. -/

namespace LinearAlgebraicGroups.Albert

open _root_.LinearAlgebraicGroups.Composition
open scoped BigOperators TensorProduct

universe u v w z

abbrev blockWeight := @CubicSpecification.blockWeight
abbrev weightProduct := @CubicSpecification.weightProduct
abbrev cubicUnit := @CubicSpecification.cubicUnit
abbrev cubicNorm := @CubicSpecification.cubicNorm
abbrev cubicAdjoint := @CubicSpecification.cubicAdjoint
abbrev tracePairing := @CubicSpecification.tracePairing
abbrev linearTrace := @CubicSpecification.linearTrace
abbrev quadraticTrace := @CubicSpecification.quadraticTrace
abbrev adjointCross := @CubicSpecification.adjointCross
abbrev diagonalCoordinates := @CubicSpecification.diagonalCoordinates
abbrev singleBlockCoordinates := @CubicSpecification.singleBlockCoordinates

noncomputable abbrev extendCoordinates := @CubicSpecification.extendCoordinates
noncomputable abbrev cubicLinePolynomial := @CubicSpecification.cubicLinePolynomial
noncomputable abbrev normDerivative := @CubicSpecification.normDerivative
noncomputable abbrev normMixedCoefficient := @CubicSpecification.normMixedCoefficient

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
variable {n : QuadraticForm R A} (γ : Fin 3 → Rˣ)

theorem tracePairing_apply (x y : Coordinates R A) :
    tracePairing n γ x y =
      ∑ i, (x.1 i * y.1 i + blockWeight γ i * n.polarBilin (x.2 i) (y.2 i)) := rfl

theorem tracePairing_comm (x y : Coordinates R A) :
    tracePairing n γ x y = tracePairing n γ y x := by
  simp only [tracePairing_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (x.1 i), QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

theorem linearTrace_apply (x : Coordinates R A) : linearTrace n γ x = ∑ i, x.1 i := by
  change tracePairing n γ x cubicUnit = _
  simp [tracePairing_apply, CubicSpecification.cubicUnit]

omit [CommRing R] [NonAssocRing A] [Module R A] in
private theorem coordinate_ext {x y : Coordinates R A}
    (ha : ∀ i, x.1 i = y.1 i) (hc : ∀ i, x.2 i = y.2 i) : x = y :=
  Prod.ext (funext ha) (funext hc)

private theorem next_zero : HermitianSpecification.cyclicNext 0 = 1 := rfl
private theorem next_one : HermitianSpecification.cyclicNext 1 = 2 := rfl
private theorem next_two : HermitianSpecification.cyclicNext 2 = 0 := rfl
private theorem prev_zero : HermitianSpecification.cyclicPrev 0 = 2 := rfl
private theorem prev_one : HermitianSpecification.cyclicPrev 1 = 0 := rfl
private theorem prev_two : HermitianSpecification.cyclicPrev 2 = 1 := rfl

private theorem norm_add (x y : A) :
    n (x + y) = n x + n y + n.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

theorem cubic_unit_identities : CubicSpecification.unitIdentities n γ := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simp [CubicSpecification.cubicNorm, CubicSpecification.cubicUnit]
  · apply coordinate_ext <;>
      simp [CubicSpecification.cubicAdjoint, CubicSpecification.cubicUnit]
  · change adjointCross n γ cubicUnit x = linearTrace n γ x • cubicUnit - x
    rw [linearTrace_apply]
    apply coordinate_ext
    · intro i
      fin_cases i <;>
        (simp [CubicSpecification.adjointCross, CubicSpecification.cubicAdjoint,
          CubicSpecification.cubicUnit, Fin.sum_univ_three,
          HermitianSpecification.cyclicNext, HermitianSpecification.cyclicPrev]; ring)
    · intro i
      simp [CubicSpecification.adjointCross, CubicSpecification.cubicAdjoint,
        CubicSpecification.cubicUnit]
      module

theorem quadraticTrace_polar : CubicSpecification.quadraticTracePolar n γ := by
  intro x y
  change linearTrace n γ (cubicAdjoint n γ (x + y)) -
    linearTrace n γ (cubicAdjoint n γ x) - linearTrace n γ (cubicAdjoint n γ y) =
      linearTrace n γ x * linearTrace n γ y - tracePairing n γ x y
  simp only [linearTrace_apply, tracePairing_apply, CubicSpecification.cubicAdjoint,
    Fin.sum_univ_three, Prod.fst_add, Prod.snd_add, Pi.add_apply, norm_add]
  simp only [next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  ring

theorem cubic_diagonal_formulas : CubicSpecification.diagonalFormulas n γ := by
  intro a
  constructor
  · simp [CubicSpecification.cubicNorm, CubicSpecification.diagonalCoordinates]
  · apply coordinate_ext <;>
      simp [CubicSpecification.cubicAdjoint, CubicSpecification.diagonalCoordinates]

theorem cubic_single_block_formulas : CubicSpecification.singleBlockFormulas n γ := by
  intro i c
  have adj : cubicAdjoint n γ (singleBlockCoordinates (R := R) i c) =
      diagonalCoordinates (Pi.single i (-(blockWeight γ i * n c))) := by
    apply coordinate_ext
    · intro j
      by_cases h : j = i
      · subst j
        simp [CubicSpecification.cubicAdjoint, CubicSpecification.singleBlockCoordinates,
          CubicSpecification.diagonalCoordinates]
      · simp [CubicSpecification.cubicAdjoint, CubicSpecification.singleBlockCoordinates,
          CubicSpecification.diagonalCoordinates, Pi.single_eq_of_ne h]
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [CubicSpecification.cubicAdjoint, CubicSpecification.singleBlockCoordinates,
          CubicSpecification.diagonalCoordinates,
          HermitianSpecification.cyclicNext, HermitianSpecification.cyclicPrev, Pi.single_apply]
  refine ⟨?_, adj, ?_⟩
  · fin_cases i <;>
      simp [CubicSpecification.cubicNorm, CubicSpecification.singleBlockCoordinates, Pi.single_apply]
  · change cubicAdjoint n γ (cubicAdjoint n γ (singleBlockCoordinates i c)) = 0
    rw [adj]
    let a : Fin 3 → R := Pi.single i (-(blockWeight γ i * n c))
    change cubicAdjoint n γ (diagonalCoordinates a) = 0
    have diag : cubicAdjoint n γ (diagonalCoordinates a) =
        diagonalCoordinates (fun j => a (cyclicNext j) * a (cyclicPrev j)) :=
      (cubic_diagonal_formulas (n := n) γ a).2
    rw [diag]
    apply coordinate_ext
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [CubicSpecification.diagonalCoordinates, cyclicNext, cyclicPrev,
          HermitianSpecification.cyclicNext, HermitianSpecification.cyclicPrev, Pi.single_apply, a]
    · simp [CubicSpecification.diagonalCoordinates]

theorem cubic_matrix_coordinates : CubicSpecification.coordinateMatrixFormulas n γ := by
  have diag (a : Fin 3 → R) :
      assemble n γ (diagonalCoordinates a) = Matrix.diagonal (fun i => a i • (1 : A)) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianSpecification.assemble, CubicSpecification.diagonalCoordinates]
  refine ⟨?_, diag, fun i c => ?_⟩
  · change assemble n γ (diagonalCoordinates (fun _ => 1)) = (1 : Mat A)
    rw [diag]
    simpa only [one_smul] using (Matrix.diagonal_one (n := Fin 3) (α := A))
  · change assemble n γ (singleBlockCoordinates i c) = block n γ i c
    rw [assemble_eq_sum]
    simp only [CubicSpecification.singleBlockCoordinates, Pi.zero_apply, zero_smul, zero_add]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, HermitianSpecification.block]
    · simp

private theorem tracePairing_diagonal_single (x : Coordinates R A) (i : Fin 3) (r : R) :
    tracePairing n γ x (diagonalCoordinates (Pi.single i r)) = x.1 i * r := by
  simp only [tracePairing_apply, CubicSpecification.diagonalCoordinates, Pi.zero_apply,
    map_zero, mul_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · simp

private theorem tracePairing_block_single (x : Coordinates R A) (i : Fin 3) (c : A) :
    tracePairing n γ x (singleBlockCoordinates i c) = blockWeight γ i * n.polarBilin (x.2 i) c := by
  simp only [tracePairing_apply, CubicSpecification.singleBlockCoordinates, Pi.zero_apply,
    mul_zero, zero_add]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]
  · simp

private theorem blockWeight_unit (i : Fin 3) : IsUnit (blockWeight γ i) :=
  ⟨γ (cyclicNext i) * γ (cyclicPrev i), rfl⟩

theorem tracePairing_perfect (h : n.polarBilin.IsPerfPair) : (tracePairing n γ).IsPerfPair := by
  suffices bij : Function.Bijective (tracePairing n γ) by
    have flip_eq : (tracePairing n γ).flip = tracePairing n γ :=
      LinearMap.ext fun x => LinearMap.ext fun y => tracePairing_comm γ y x
    refine ⟨bij, ?_⟩
    change Function.Bijective (⇑((tracePairing n γ).flip))
    rwa [flip_eq]
  constructor
  · intro x y eq
    apply coordinate_ext
    · intro i
      have H := LinearMap.congr_fun eq (diagonalCoordinates (Pi.single i 1))
      simpa only [tracePairing_diagonal_single, mul_one] using H
    · intro i
      apply h.bijective_left.injective
      apply LinearMap.ext
      intro c
      have H := LinearMap.congr_fun eq (singleBlockCoordinates i c)
      rw [tracePairing_block_single, tracePairing_block_single] at H
      exact (blockWeight_unit γ i).mul_left_cancel H
  · intro f
    let l (i : Fin 3) : A →ₗ[R] R :=
      f.comp ((LinearMap.inr R (Fin 3 → R) (Fin 3 → A)).comp (LinearMap.single R (fun _ : Fin 3 => A) i))
    obtain ⟨c, hc⟩ := Classical.axiomOfChoice (fun i : Fin 3 =>
      h.bijective_left.surjective (((γ (cyclicNext i) * γ (cyclicPrev i))⁻¹ : Rˣ) • l i))
    let x : Coordinates R A := (fun i => f (diagonalCoordinates (Pi.single i 1)), c)
    refine ⟨x, LinearMap.ext fun y => ?_⟩
    let parts (i : Fin 3) : Coordinates R A :=
      diagonalCoordinates (Pi.single i (y.1 i)) + singleBlockCoordinates i (y.2 i)
    have decompose : (∑ i, parts i) = y := by
      apply Prod.ext
      · change (LinearMap.fst R (Fin 3 → R) (Fin 3 → A)) (∑ i, parts i) = y.1
        rw [map_sum]
        simpa only [parts, LinearMap.fst_apply, Prod.fst_add, CubicSpecification.diagonalCoordinates,
          CubicSpecification.singleBlockCoordinates, add_zero] using Finset.univ_sum_single y.1
      · change (LinearMap.snd R (Fin 3 → R) (Fin 3 → A)) (∑ i, parts i) = y.2
        rw [map_sum]
        simpa only [parts, LinearMap.snd_apply, Prod.snd_add, CubicSpecification.diagonalCoordinates,
          CubicSpecification.singleBlockCoordinates, zero_add] using Finset.univ_sum_single y.2
    conv_rhs => rw [← decompose, map_sum]
    rw [tracePairing_apply]
    apply Finset.sum_congr rfl
    intro i _
    change _ + _ = f (diagonalCoordinates (Pi.single i (y.1 i)) + singleBlockCoordinates i (y.2 i))
    rw [map_add]
    congr 1
    · have eq : diagonalCoordinates (A := A) (Pi.single i (y.1 i)) =
          y.1 i • diagonalCoordinates (Pi.single i 1) := by
        apply coordinate_ext
        · intro j
          by_cases hij : j = i
          · subst j; simp [CubicSpecification.diagonalCoordinates]
          · simp [CubicSpecification.diagonalCoordinates, Pi.single_eq_of_ne hij]
        · simp [CubicSpecification.diagonalCoordinates]
      rw [eq, map_smul]
      exact mul_comm _ _
    · have H := LinearMap.congr_fun (hc i) (y.2 i)
      change n.polarBilin (c i) (y.2 i) =
        ((↑((γ (cyclicNext i) * γ (cyclicPrev i))⁻¹) : R) * l i (y.2 i)) at H
      change blockWeight γ i * n.polarBilin (c i) (y.2 i) = l i (y.2 i)
      rw [H, ← mul_assoc]
      change (↑(γ (cyclicNext i) * γ (cyclicPrev i)) : R) *
        ↑((γ (cyclicNext i) * γ (cyclicPrev i))⁻¹) * _ = _
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

variable [IsScalarTower R A A] [SMulCommClass R A A]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem adjointCross_diagonal (x y : Coordinates R A) (i : Fin 3) :
    (adjointCross n γ x y).1 i =
      x.1 (cyclicNext i) * y.1 (cyclicPrev i) +
      y.1 (cyclicNext i) * x.1 (cyclicPrev i) - blockWeight γ i * n.polarBilin (x.2 i) (y.2 i) := by
  simp only [CubicSpecification.adjointCross, CubicSpecification.cubicAdjoint, Prod.fst_add,
    Prod.snd_add, Prod.fst_sub, Pi.add_apply, Pi.sub_apply, norm_add]
  ring

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem adjointCross_block (x y : Coordinates R A) (i : Fin 3) :
    (adjointCross n γ x y).2 i =
      -(x.1 i) • y.2 i - y.1 i • x.2 i +
      (γ i : R) • conjugate n (x.2 (cyclicNext i) * y.2 (cyclicPrev i) +
        y.2 (cyclicNext i) * x.2 (cyclicPrev i)) := by
  simp only [CubicSpecification.adjointCross, CubicSpecification.cubicAdjoint, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply, add_mul, mul_add, map_add]
  module

theorem cubicAdjoint_add_smul : CubicSpecification.adjointLine n γ := by
  intro x y s
  change cubicAdjoint n γ (x + s • y) =
    cubicAdjoint n γ x + s • adjointCross n γ x y + (s * s) • cubicAdjoint n γ y
  apply coordinate_ext
  · intro i
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      adjointCross_diagonal, CubicSpecification.cubicAdjoint, Prod.snd_add, Prod.smul_snd,
      norm_add, n.map_smul, map_smul]
    ring
  · intro i
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
      adjointCross_block, CubicSpecification.cubicAdjoint, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul]
    module

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem adjointCross_comm (x y : Coordinates R A) :
    adjointCross n γ x y = adjointCross n γ y x := by
  unfold adjointCross CubicSpecification.adjointCross
  rw [add_comm x y]
  abel

private def adjointCrossRight (x : Coordinates R A) : Coordinates R A →ₗ[R] Coordinates R A where
  toFun := adjointCross n γ x
  map_add' y z := by
    apply coordinate_ext
    · intro i
      simp only [adjointCross_diagonal, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
      ring
    · intro i
      simp only [adjointCross_block, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul, map_add]
      module
  map_smul' r y := by
    apply coordinate_ext
    · intro i
      simp only [adjointCross_diagonal, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
        RingHom.id_apply, smul_eq_mul, map_smul]
      ring
    · intro i
      simp only [adjointCross_block, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply,
        smul_eq_mul, smul_mul_assoc, mul_smul_comm, map_smul, ← smul_add]
      module

theorem cubicAdjoint_isQuadratic : CubicSpecification.adjointQuadratic n γ := by
  let P : LinearMap.BilinMap R (Coordinates R A) (Coordinates R A) :=
    { toFun := adjointCrossRight γ
      map_add' x y := by
        apply LinearMap.ext
        intro z
        change adjointCross n γ (x + y) z = adjointCross n γ x z + adjointCross n γ y z
        rw [adjointCross_comm γ (x + y), adjointCross_comm γ x, adjointCross_comm γ y]
        exact (adjointCrossRight γ z).map_add x y
      map_smul' r x := by
        apply LinearMap.ext
        intro y
        change adjointCross n γ (r • x) y = r • adjointCross n γ x y
        rw [adjointCross_comm γ (r • x), adjointCross_comm γ x]
        exact (adjointCrossRight γ y).map_smul r x }
  let q : QuadraticMap R (Coordinates R A) (Coordinates R A) :=
    { toFun := cubicAdjoint n γ
      toFun_smul := fun r x => by
        have h : cubicAdjoint n γ ((0 : Coordinates R A) + r • x) =
            cubicAdjoint n γ 0 + r • adjointCross n γ 0 x + (r * r) • cubicAdjoint n γ x :=
          cubicAdjoint_add_smul γ 0 x r
        have h0 : cubicAdjoint n γ (0 : Coordinates R A) = 0 := by
          apply coordinate_ext <;> simp [CubicSpecification.cubicAdjoint]
        simpa [h0, CubicSpecification.adjointCross] using h
      exists_companion' := ⟨P, fun x y => by
        change cubicAdjoint n γ (x + y) =
          cubicAdjoint n γ x + cubicAdjoint n γ y + adjointCross n γ x y
        unfold adjointCross CubicSpecification.adjointCross
        abel⟩ }
  exact ⟨q, fun _ => rfl, fun _ _ => rfl⟩

private theorem trace_triple_polar (h : NormLaws n) (a b c : A) :
    n.polarBilin (conjugate n (b * c)) a = compositionTrace n ((a * b) * c) := by
  rw [compositionTrace_mul_assoc h, compositionTrace_mul_as_polar h]
  exact QuadraticMap.polar_comm n _ _

theorem cubicNorm_add_smul : CubicSpecification.normLine n γ := by
  intro h x y s
  change cubicNorm n γ (x + s • y) = cubicNorm n γ x +
      s * tracePairing n γ (cubicAdjoint n γ x) y +
      s ^ 2 * tracePairing n γ (cubicAdjoint n γ y) x + s ^ 3 * cubicNorm n γ y
  have pairing (a b : Coordinates R A) :
      tracePairing n γ (cubicAdjoint n γ a) b =
        ∑ i, ((a.1 (cyclicNext i) * a.1 (cyclicPrev i) - blockWeight γ i * n (a.2 i)) * b.1 i +
          blockWeight γ i * (-(a.1 i) * n.polarBilin (a.2 i) (b.2 i) +
            (γ i : R) * compositionTrace n ((b.2 i * a.2 (cyclicNext i)) * a.2 (cyclicPrev i)))) := by
    rw [tracePairing_apply]
    apply Finset.sum_congr rfl
    intro i _
    change _ * _ + blockWeight γ i * n.polarBilin
      (-(a.1 i) • a.2 i + (γ i : R) • conjugate n (a.2 (cyclicNext i) * a.2 (cyclicPrev i)))
      (b.2 i) = _
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂]
    change _ * _ + blockWeight γ i *
      (-(a.1 i) * n.polarBilin (a.2 i) (b.2 i) +
        (γ i : R) * n.polarBilin (conjugate n (a.2 (cyclicNext i) * a.2 (cyclicPrev i))) (b.2 i)) = _
    rw [trace_triple_polar h]
    rfl
  rw [pairing, pairing]
  simp only [CubicSpecification.cubicNorm, Fin.sum_univ_three,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, norm_add, n.map_smul, map_smul,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add]
  simp only [cyclicNext, cyclicPrev, next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  simp only [← compositionTrace_mul_cyclic h (x.2 0) (y.2 1) (x.2 2),
    compositionTrace_mul_cyclic h (y.2 2) (x.2 0) (x.2 1),
    ← compositionTrace_mul_cyclic h (y.2 0) (x.2 1) (y.2 2),
    compositionTrace_mul_cyclic h (x.2 2) (y.2 0) (y.2 1)]
  simp only [CubicSpecification.blockWeight, CubicSpecification.weightProduct,
    next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  have sym (i : Fin 3) : n.polarBilin (y.2 i) (x.2 i) = n.polarBilin (x.2 i) (y.2 i) :=
    QuadraticMap.polar_comm n _ _
  simp only [sym 0, sym 1, sym 2]
  ring

theorem cubicNorm_smul : CubicSpecification.normHomogeneous n γ := by
  intro r x
  change cubicNorm n γ (r • x) = r ^ 3 * cubicNorm n γ x
  simp only [CubicSpecification.cubicNorm, Fin.sum_univ_three,
    Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, n.map_smul,
    smul_mul_assoc, mul_smul_comm, map_smul]
  ring

private theorem norm_cyclic (h : NormLaws n) (a b c : R) (x y z : A) (r s t : R) :
    a * b * c - (s * t * a * n x + t * r * b * n y + r * s * c * n z) +
        r * s * t * compositionTrace n ((x * y) * z) =
      b * c * a - (t * r * b * n y + r * s * c * n z + s * t * a * n x) +
        s * t * r * compositionTrace n ((y * z) * x) := by
  rw [← compositionTrace_mul_cyclic h x y z]
  ring

private theorem adjoint_diagonal_coord (h : NormLaws n)
    (a b c r s t : R) (x y z : A) :
    (c * a - t * r * n y) * (a * b - r * s * n z) -
        s * t * n (-a • x + r • conjugate n (y * z)) =
      (a * b * c - (s * t * a * n x + t * r * b * n y + r * s * c * n z) +
        r * s * t * compositionTrace n ((x * y) * z)) * a := by
  rw [norm_add, n.map_smul, n.map_smul, norm_conjugate h, h.map_mul,
    LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    ← compositionTrace_mul_as_polar h, ← compositionTrace_mul_assoc h]
  ring

private theorem moufang_trace (h : NormLaws n) (x y z : A) :
    n x • conjugate n (y * z) + (x * y) * (z * x) =
      compositionTrace n ((x * y) * z) • x := by
  rw [(composition_isAlternative h).moufang_middle x z y, compositionTrace_mul_assoc h]
  have eq := congrArg (· * x) (conjugate_apply n (x * (y * z)))
  simp only [conjugate_mul h, sub_mul, smul_mul_assoc, one_mul,
    (conjugate_right_products h x _).2] at eq
  rw [conjugate_mul h y z, eq]
  abel

private theorem adjoint_block_coord (h : NormLaws n)
    (a b c r s t : R) (x y z : A) :
    -(b * c - s * t * n x) • (-a • x + r • conjugate n (y * z)) +
      r • conjugate n ((-b • y + s • conjugate n (z * x)) *
                       (-c • z + t • conjugate n (x * y))) =
      (a * b * c - (s * t * a * n x + t * r * b * n y + r * s * c * n z) +
        r * s * t * compositionTrace n ((x * y) * z)) • x := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul]
  rw [conjugate_mul h y (conjugate n (x * y)), conjugate_involutive h,
    (conjugate_right_products h y x).1,
    conjugate_mul h (conjugate n (z * x)) z, conjugate_involutive h,
    (conjugate_left_products h z x).1,
    conjugate_mul h (conjugate n (z * x)) (conjugate n (x * y)),
    conjugate_involutive h, conjugate_involutive h]
  conv_rhs => rw [add_smul, mul_smul, ← moufang_trace h x y z]
  module

theorem cubic_adjoint_identity : CubicSpecification.adjointIdentity n γ := by
  intro hn x
  have h := IsOctonionNorm.toNormLaws hn
  let a := x.1 0
  let b := x.1 1
  let c := x.1 2
  let r : R := γ 0
  let s : R := γ 1
  let t : R := γ 2
  let p := x.2 0
  let q := x.2 1
  let z := x.2 2
  have H₀ : cubicNorm n γ x =
      a * b * c - (s * t * a * n p + t * r * b * n q + r * s * c * n z) +
        r * s * t * compositionTrace n ((p * q) * z) := by
    simp only [CubicSpecification.cubicNorm, CubicSpecification.weightProduct, Fin.sum_univ_three]
    rfl
  have H₁ := H₀.trans (norm_cyclic h a b c p q z r s t)
  have H₂ := H₁.trans (norm_cyclic h b c a q z p s t r)
  change cubicAdjoint n γ (cubicAdjoint n γ x) = cubicNorm n γ x • x
  apply coordinate_ext
  · intro i
    fin_cases i
    · rw [H₀]
      exact adjoint_diagonal_coord h a b c r s t p q z
    · rw [H₁]
      exact adjoint_diagonal_coord h b c a s t r q z p
    · rw [H₂]
      exact adjoint_diagonal_coord h c a b t r s z p q
  · intro i
    fin_cases i
    · rw [H₀]
      exact adjoint_block_coord h a b c r s t p q z
    · rw [H₁]
      exact adjoint_block_coord h b c a s t r q z p
    · rw [H₂]
      exact adjoint_block_coord h c a b t r s z p q

section Extension

variable (B : Type w) [CommRing B] [Algebra R B]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem extendCoordinates_apply (x : Coordinates R A) :
    extendCoordinates B x = (fun i => algebraMap R B (x.1 i), fun i => 1 ⊗ₜ[R] x.2 i) := by
  change coordinatesBaseChange B (1 ⊗ₜ[R] x) = _
  rw [coordinatesBaseChange_tmul]
  simp

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem extendCoordinates_add (x y : Coordinates R A) :
    extendCoordinates B (x + y) = extendCoordinates B x + extendCoordinates B y := by
  change coordinatesBaseChange B (1 ⊗ₜ[R] (x + y)) = _
  rw [TensorProduct.tmul_add, map_add]
  rfl

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem extendCoordinates_sub (x y : Coordinates R A) :
    extendCoordinates B (x - y) = extendCoordinates B x - extendCoordinates B y := by
  change coordinatesBaseChange B (1 ⊗ₜ[R] (x - y)) = _
  rw [TensorProduct.tmul_sub, map_sub]
  rfl

theorem extendCoordinates_unit :
    extendCoordinates B (cubicUnit (R := R) (A := A)) = cubicUnit := by
  rw [extendCoordinates_apply]
  apply coordinate_ext <;> simp [CubicSpecification.cubicUnit]

private theorem extend_blockWeight (i : Fin 3) :
    blockWeight (baseChangedWeights B γ) i = algebraMap R B (blockWeight γ i) := by
  simp only [blockWeight, CubicSpecification.blockWeight, map_mul]
  rfl

private theorem extend_weightProduct :
    weightProduct (baseChangedWeights B γ) = algebraMap R B (weightProduct γ) := by
  simp only [weightProduct, CubicSpecification.weightProduct, map_mul]
  rfl

variable [Module.Projective R A]

theorem cubicNorm_extend (x : Coordinates R A) :
    cubicNorm (normBaseChange B n) (baseChangedWeights B γ) (extendCoordinates B x) =
      algebraMap R B (cubicNorm n γ x) := by
  rw [extendCoordinates_apply]
  simp [CubicSpecification.cubicNorm, extend_blockWeight, extend_weightProduct,
    Algebra.TensorProduct.tmul_mul_tmul, normBaseChange_tmul,
    compositionTrace_baseChange_tmul, map_mul, map_sub, map_add, map_sum]

theorem cubicAdjoint_extend (x : Coordinates R A) :
    cubicAdjoint (normBaseChange B n) (baseChangedWeights B γ) (extendCoordinates B x) =
      extendCoordinates B (cubicAdjoint n γ x) := by
  rw [extendCoordinates_apply, extendCoordinates_apply]
  apply coordinate_ext
  · intro i
    simp [CubicSpecification.cubicAdjoint, extend_blockWeight, map_mul, map_sub, normBaseChange_tmul]
  · intro i
    simp only [CubicSpecification.cubicAdjoint, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      conjugate_baseChange, LinearMap.baseChange_tmul, TensorProduct.tmul_add]
    have balance (r : R) (a : A) :
        algebraMap R B r • ((1 : B) ⊗ₜ[R] a) = 1 ⊗ₜ[R] (r • a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]
    rw [← map_neg, balance]
    exact congrArg (_ + ·) (balance _ _)

theorem tracePairing_extend (x y : Coordinates R A) :
    tracePairing (normBaseChange B n) (baseChangedWeights B γ) (extendCoordinates B x)
      (extendCoordinates B y) = algebraMap R B (tracePairing n γ x y) := by
  rw [extendCoordinates_apply, extendCoordinates_apply, tracePairing_apply, tracePairing_apply]
  have polar : (normBaseChange B n).polarBilin = LinearMap.BilinForm.baseChange B n.polarBilin :=
    polar_normBaseChange B n
  simp only [extend_blockWeight, map_sum, map_add, map_mul, polar,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]

omit [Module.Projective R A] in
theorem cubic_baseChange : CubicSpecification.cubicBaseChange n γ B := by
  intro h
  let := h.projective
  exact ⟨extendCoordinates_unit B, cubicNorm_extend γ B, cubicAdjoint_extend γ B,
    tracePairing_extend γ B⟩

section Naturality

variable {D : Type z} [CommRing D] [Algebra R D]

abbrev mapExtendedCoordinates := @CubicSpecification.mapExtendedCoordinates

omit [IsScalarTower R A A] [SMulCommClass R A A] [Module.Projective R A] in
theorem coordinates_extension_naturality :
    CubicSpecification.coordinatesExtensionNaturality (R := R) (A := A) B (D := D) := by
  intro f x
  change mapExtendedCoordinates B f (coordinatesBaseChange B x) =
    coordinatesBaseChange D (f.toLinearMap.rTensor (Coordinates R A) x)
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    rw [coordinatesBaseChange_tmul, LinearMap.rTensor_tmul, coordinatesBaseChange_tmul]
    simp [CubicSpecification.mapExtendedCoordinates, LinearMap.rTensor_tmul]
  | add x y hx hy =>
    simp only [map_add]
    rw [← hx, ← hy]
    apply coordinate_ext <;> simp [CubicSpecification.mapExtendedCoordinates]

variable (f : B →ₐ[R] D)

local notation "φ" => f.toLinearMap.rTensor A

omit [IsScalarTower R A A] [SMulCommClass R A A] [Module.Projective R A] in
private theorem tensor_map_smul (r : B) (x : B ⊗[R] A) :
    φ (r • x) = f r • φ x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    simp [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul]
  | add x y hx hy => simp [smul_add, hx, hy]

omit [Module.Projective R A] in
private theorem tensor_map_mul (x y : B ⊗[R] A) :
    φ (x * y) = φ x * φ y := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [add_mul, hx, hy]
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp [mul_add, hx, hy]
    | tmul t y => simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem tensor_map_polar (x y : B ⊗[R] A) :
    (normBaseChange D n).polarBilin (φ x) (φ y) =
      f ((normBaseChange B n).polarBilin x y) := by
  have hB : (normBaseChange B n).polarBilin = LinearMap.BilinForm.baseChange B n.polarBilin :=
    polar_normBaseChange B n
  have hD : (normBaseChange D n).polarBilin = LinearMap.BilinForm.baseChange D n.polarBilin :=
    polar_normBaseChange D n
  rw [hB, hD]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t y =>
      simp [LinearMap.rTensor_tmul, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

private theorem tensor_map_norm (x : B ⊗[R] A) :
    normBaseChange D n (φ x) = f (normBaseChange B n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp [LinearMap.rTensor_tmul, normBaseChange_tmul]
  | add x y hx hy => simp [norm_add, hx, hy, tensor_map_polar B f]

private theorem tensor_map_trace (x : B ⊗[R] A) :
    compositionTrace (normBaseChange D n) (φ x) =
      f (compositionTrace (normBaseChange B n) x) := by
  rw [compositionTrace_apply, compositionTrace_apply]
  have one : φ (1 : B ⊗[R] A) = 1 := by
    change φ (1 ⊗ₜ[R] (1 : A)) = 1 ⊗ₜ[R] (1 : A)
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  rw [← one, tensor_map_polar B f]

private theorem tensor_map_conjugate (x : B ⊗[R] A) :
    conjugate (normBaseChange D n) (φ x) = φ (conjugate (normBaseChange B n) x) := by
  rw [conjugate_baseChange, conjugate_baseChange]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s x => simp [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul]

private theorem map_changed_weight (i : Fin 3) :
    f (baseChangedWeights B γ i : B) = (baseChangedWeights D γ i : D) :=
  f.commutes _

private theorem map_changed_blockWeight (i : Fin 3) :
    f (blockWeight (baseChangedWeights B γ) i) = blockWeight (baseChangedWeights D γ) i := by
  simp only [blockWeight, CubicSpecification.blockWeight, map_mul, map_changed_weight γ B f]

private theorem map_changed_weightProduct :
    f (weightProduct (baseChangedWeights B γ)) = weightProduct (baseChangedWeights D γ) := by
  simp only [weightProduct, CubicSpecification.weightProduct, map_mul, map_changed_weight γ B f]

omit [Module.Projective R A] in
theorem cubic_extension_naturality : CubicSpecification.cubicExtensionNaturality n γ B (D := D) := by
  intro h
  let := h.projective
  let qB := normBaseChange B n
  let qD := normBaseChange D n
  let γB := baseChangedWeights B γ
  let γD := baseChangedWeights D γ
  change ∀ (f : B →ₐ[R] D) (x y : Coordinates B (B ⊗[R] A)),
    let e := mapExtendedCoordinates B (A := A) f
    cubicNorm qD γD (e x) = f (cubicNorm qB γB x) ∧
      cubicAdjoint qD γD (e x) = e (cubicAdjoint qB γB x) ∧
      tracePairing qD γD (e x) (e y) = f (tracePairing qB γB x y)
  intro f x y
  let e := mapExtendedCoordinates B (A := A) f
  change cubicNorm qD γD (e x) = f (cubicNorm qB γB x) ∧
    cubicAdjoint qD γD (e x) = e (cubicAdjoint qB γB x) ∧
    tracePairing qD γD (e x) (e y) = f (tracePairing qB γB x y)
  refine ⟨?_, ?_, ?_⟩
  · simp only [qB, qD, γB, γD, e, CubicSpecification.cubicNorm,
      CubicSpecification.mapExtendedCoordinates, map_add, map_sub, map_mul, map_sum,
      tensor_map_norm B f, ← tensor_map_mul B f, tensor_map_trace B f,
      map_changed_blockWeight γ B f, map_changed_weightProduct γ B f]
  · apply coordinate_ext
    · intro i
      simp only [qB, qD, γB, γD, e, CubicSpecification.cubicAdjoint,
        CubicSpecification.mapExtendedCoordinates, map_sub, map_mul, tensor_map_norm B f,
        map_changed_blockWeight γ B f]
    · intro i
      simp only [qB, qD, γB, γD, e, CubicSpecification.cubicAdjoint,
        CubicSpecification.mapExtendedCoordinates, map_add, tensor_map_smul B f,
        map_neg, map_changed_weight γ B f]
      rw [← tensor_map_mul B f, tensor_map_conjugate B f]
  · simp only [qB, qD, γB, γD, e, tracePairing_apply, CubicSpecification.mapExtendedCoordinates,
      map_sum, map_add, map_mul, tensor_map_polar B f, map_changed_blockWeight γ B f]

end Naturality

end Extension

section Coefficients

open Polynomial (C X coeff)

theorem cubic_line_polynomial (h : IsOctonionNorm n) (x y : Coordinates R A) :
    letI := h.projective
    cubicLinePolynomial n γ x y =
      C (cubicNorm n γ x) + X * C (tracePairing n γ (cubicAdjoint n γ x) y) +
      X ^ 2 * C (tracePairing n γ (cubicAdjoint n γ y) x) + X ^ 3 * C (cubicNorm n γ y) := by
  let := h.projective
  let q := normBaseChange (Polynomial R) n
  let δ := baseChangedWeights (Polynomial R) γ
  let e := extendCoordinates (R := R) (A := A) (Polynomial R)
  change cubicNorm q δ (e x + (X : Polynomial R) • e y) = _
  have hP : IsOctonionNorm q := octonion_norm_baseChange h (Polynomial R)
  have expansion : cubicNorm q δ (e x + (X : Polynomial R) • e y) = cubicNorm q δ (e x) +
      X * tracePairing q δ (cubicAdjoint q δ (e x)) (e y) +
      X ^ 2 * tracePairing q δ (cubicAdjoint q δ (e y)) (e x) + X ^ 3 * cubicNorm q δ (e y) :=
    cubicNorm_add_smul δ (IsOctonionNorm.toNormLaws hP) (e x) (e y) X
  rw [expansion]
  dsimp only [q, δ, e]
  rw [cubicAdjoint_extend, cubicAdjoint_extend, tracePairing_extend, tracePairing_extend,
    cubicNorm_extend, cubicNorm_extend]
  rfl

theorem cubic_norm_derivative : CubicSpecification.normDerivativeFormula n γ := by
  intro h
  let := h.projective
  intro x y
  change (cubicLinePolynomial n γ x y).coeff 1 = _
  rw [cubic_line_polynomial γ h x y]
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_comm X]

private theorem normDerivative_unit (h : IsOctonionNorm n) (x : Coordinates R A) :
    letI := h.projective
    normDerivative n γ cubicUnit x = linearTrace n γ x := by
  let := h.projective
  have d : normDerivative n γ cubicUnit x = tracePairing n γ (cubicAdjoint n γ cubicUnit) x :=
    cubic_norm_derivative γ h cubicUnit x
  have u : cubicAdjoint n γ cubicUnit = cubicUnit := (cubic_unit_identities (n := n) γ).2.1
  rw [d, u, tracePairing_comm]
  rfl

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem tracePairing_cross_unit (x y : Coordinates R A) :
    tracePairing n γ (adjointCross n γ cubicUnit x) y =
      linearTrace n γ x * linearTrace n γ y - tracePairing n γ x y := by
  have cross : adjointCross n γ cubicUnit x = linearTrace n γ x • cubicUnit - x :=
    (cubic_unit_identities (n := n) γ).2.2 x
  rw [cross, map_sub, LinearMap.sub_apply, LinearMap.map_smul₂,
    tracePairing_comm γ cubicUnit y]
  rfl

private theorem mixedCoefficient_eq (h : IsOctonionNorm n) (x y : Coordinates R A) :
    letI := h.projective
    normMixedCoefficient n γ x y = tracePairing n γ (adjointCross n γ cubicUnit x) y := by
  let := h.projective
  let q := normBaseChange (Polynomial R) n
  let δ := baseChangedWeights (Polynomial R) γ
  let e := extendCoordinates (R := R) (A := A) (Polynomial R)
  have hP : IsOctonionNorm q := octonion_norm_baseChange h (Polynomial R)
  let := hP.projective
  have deriv : normDerivative q δ (cubicUnit + (X : Polynomial R) • e x) (e y) =
      tracePairing q δ (cubicAdjoint q δ (cubicUnit + (X : Polynomial R) • e x)) (e y) :=
    cubic_norm_derivative δ hP _ _
  have line : cubicAdjoint q δ (cubicUnit + (X : Polynomial R) • e x) =
      cubicAdjoint q δ cubicUnit + (X : Polynomial R) • adjointCross q δ cubicUnit (e x) +
        (X * X : Polynomial R) • cubicAdjoint q δ (e x) :=
    cubicAdjoint_add_smul δ _ _ X
  change (normDerivative q δ (cubicUnit + (X : Polynomial R) • e x) (e y)).coeff 1 = _
  rw [deriv, line]
  have unit : cubicAdjoint q δ cubicUnit = cubicUnit := (cubic_unit_identities (n := q) δ).2.1
  have cross : adjointCross q δ cubicUnit (e x) = e (adjointCross n γ cubicUnit x) := by
    dsimp only [e, q, δ]
    rw [← extendCoordinates_unit (R := R) (A := A) (Polynomial R)]
    change cubicAdjoint _ _ (_ + _) - cubicAdjoint _ _ _ - cubicAdjoint _ _ _ =
      extendCoordinates _ (cubicAdjoint _ _ (_ + _) - cubicAdjoint _ _ _ - cubicAdjoint _ _ _)
    rw [← extendCoordinates_add, cubicAdjoint_extend, cubicAdjoint_extend, cubicAdjoint_extend,
      extendCoordinates_sub, extendCoordinates_sub]
  rw [unit, cross]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smul₂, smul_eq_mul]
  rw [← extendCoordinates_unit (R := R) (A := A) (Polynomial R)]
  dsimp only [e, q, δ]
  rw [tracePairing_extend, tracePairing_extend, cubicAdjoint_extend, tracePairing_extend]
  change (C _ + X * C _ + (X * X) * C _).coeff 1 = _
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_comm X, ← pow_two]

theorem cubic_trace_coefficients : CubicSpecification.traceCoefficientFormula n γ := by
  intro h
  let := h.projective
  refine ⟨normDerivative_unit γ h, fun x y => ?_⟩
  change tracePairing n γ x y = normDerivative n γ cubicUnit x * normDerivative n γ cubicUnit y -
    normMixedCoefficient n γ x y
  rw [normDerivative_unit γ h, normDerivative_unit γ h, mixedCoefficient_eq γ h,
    tracePairing_cross_unit]
  ring

theorem cubic_identities_after_extension (B : Type w) [CommRing B] [Algebra R B] :
    CubicSpecification.scalarExtensionIdentities n γ B := by
  intro h
  let := h.projective
  have hB := octonion_norm_baseChange h B
  let δ := baseChangedWeights B γ
  exact ⟨cubic_unit_identities δ, tracePairing_perfect δ hB.perfect,
    cubic_adjoint_identity δ hB, cubic_norm_derivative δ hB, (cubic_trace_coefficients δ hB).2⟩

end Coefficients

end LinearAlgebraicGroups.Albert
