import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.Simplicity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitModel
import Mathlib.RingTheory.Flat.Equalizer

/-! The ideal calculation in the split model and its faithfully flat descent. -/

namespace LinearAlgebraicGroups.Albert

open SplitSpecification SimplicitySpecification
open HermitianSpecification CubicSpecification
open _root_.LinearAlgebraicGroups.Composition
open scoped TensorProduct BigOperators
open _root_.TensorProduct

universe u v

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

section Ground

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (J : ParaQuadratic R M)

private def groundQuadratic : QuadraticMap R M (Module.End R M) :=
  (TensorProduct.lid R M).conj.toLinearMap.compQuadraticMap ((J.op R).comp (TensorProduct.lid R M).symm.toLinearMap)

private theorem groundQuadratic_apply (x y : M) :
    groundQuadratic J x y = J.groundOp x y := rfl

private theorem groundPolar_apply (x y z : M) :
    (groundQuadratic J).polarBilin x z y = groundTriple J x y z := by
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, groundTriple,
    ← groundQuadratic_apply J]

private theorem triple_add_last (x y z w : M) :
    groundTriple J x y (z + w) = groundTriple J x y z + groundTriple J x y w := by
  simp only [← groundPolar_apply, map_add, LinearMap.add_apply]

private theorem triple_smul_last (r : R) (x y z : M) :
    groundTriple J x y (r • z) = r • groundTriple J x y z := by
  simp only [← groundPolar_apply, map_smul, LinearMap.smul_apply]

private theorem scalarIdeal_mem {e : M} {I : Submodule R M} {r : R} :
    r ∈ scalarIdeal e I ↔ r • e ∈ I := Iff.rfl

private theorem scalarMultiple_isIdeal (a : Ideal R) :
    IsQuadraticIdeal J (a • (⊤ : Submodule R M)) := by
  let I := a • (⊤ : Submodule R M)
  have hgen {r : R} (hr : r ∈ a) (x : M) : r • x ∈ I :=
    Submodule.smul_mem_smul hr Submodule.mem_top
  have hU : ∀ x y : M, y ∈ I → J.groundOp x y ∈ I := by
    intro x y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr m _
      rw [map_smul]
      exact hgen hr _
    · intro m n hm hn
      rw [map_add]
      exact I.add_mem hm hn
  have hT : ∀ x y z : M, z ∈ I → groundTriple J x y z ∈ I := by
    intro x y z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr m _
      rw [triple_smul_last]
      exact hgen hr _
    · intro m n hm hn
      rw [triple_add_last]
      exact I.add_mem hm hn
  refine ⟨⟨hU, hT⟩, ?_⟩
  intro x y hx
  refine Submodule.smul_induction_on' hx ?_ ?_
  · intro r hr m _
    rw [← groundQuadratic_apply, (groundQuadratic J).map_smul, LinearMap.smul_apply,
      mul_smul]
    exact I.smul_mem r (hgen hr _)
  · intro m hm n hn hUm hUn
    have h := hT m y n hn
    unfold groundTriple at h
    convert I.add_mem (I.add_mem h hUn) hUm using 1
    abel

end Ground

section Split

variable (R : Type u) [CommRing R]

local notation "V" => Coordinates R (Zorn R)
local notation "E" => (FrameSpecification.frameAxis (R := R) (A := Zorn R))
local notation "D" => (CubicSpecification.singleBlockCoordinates (R := R) (A := Zorn R))
local notation "n" => (Zorn.norm R)
local notation "γ" => (LowerRankSpecification.untwisted R)
local notation "U" => (QuadraticOperatorSpecification.applyOperator n γ)
local notation "T" => (QuadraticOperatorSpecification.triple n γ)

open private coordinate_ext tracePairing_block_single adjointCross_diagonal adjointCross_block
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CubicIdentities
open private frame_trace cross_zero_left from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameParameters
open private ground_operator from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators

private theorem axis_block_cross {i j : Fin 3} (h : j ≠ i) (a : Zorn R) :
    CubicSpecification.adjointCross n γ (E j) (D i a) = 0 := by
  apply coordinate_ext
  · intro k
    simp [adjointCross_diagonal, FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
      CubicSpecification.singleBlockCoordinates]
  · intro k
    by_cases hk : k = i
    · subst k
      simp [adjointCross_block, FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, Pi.single_apply, Ne.symm h]
    · simp [adjointCross_block, FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, Pi.single_apply, hk]

private theorem untwisted_weight (i : Fin 3) : blockWeight γ i = (1 : R) := by
  simp [CubicSpecification.blockWeight, LowerRankSpecification.untwisted]

private theorem axis_block_pair {i j : Fin 3} (h : j ≠ i) (a b : Zorn R) :
    T (E j) (D i b) (D i a) = (Zorn.norm R).polarBilin a b • E j := by
  rw [(cubic_operator_identities γ (Zorn.isOctonion R)).2.1, frame_trace,
    tracePairing_block_single, axis_block_cross R h, untwisted_weight, cross_zero_left]
  simp [CubicSpecification.singleBlockCoordinates]

private theorem axis_to_block {i j : Fin 3} (h : j ≠ i) (b : Zorn R) :
    T (E j) (E j) (D i b) = D i b := by
  rw [(cubic_operator_identities γ (Zorn.isOctonion R)).2.1, frame_trace,
    tracePairing_comm _ (D i b), frame_trace, axis_block_cross R h, cross_zero_left]
  simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
    CubicSpecification.singleBlockCoordinates]

private theorem singleBlock_linear (i : Fin 3) : ∃ f : Zorn R →ₗ[R] V, ∀ b, f b = D i b := by
  refine ⟨(LinearMap.inr R (Fin 3 → R) (Fin 3 → Zorn R)).comp (LinearMap.single R (fun _ : Fin 3 => Zorn R) i), ?_⟩
  intro b
  rfl

/-- The diagonal and block projections extract the components of every outer ideal. -/
private theorem split_coordinate_ideals (I : Submodule R V)
    (hU : ∀ x y, y ∈ I → U x y ∈ I) (hT : ∀ x y z, z ∈ I → T x y z ∈ I) :
    I = scalarIdeal (cubicUnit : V) I • (⊤ : Submodule R V) := by
  classical
  let a := scalarIdeal (cubicUnit : V) I
  let F := hermitian_frame (R := R) (A := Zorn R) n γ
  have diag (x : V) (hx : x ∈ I) (i : Fin 3) : x.1 i • E i ∈ I := by
    rw [← F.2.2.1 i x]
    exact hU _ _ hx
  have block (x : V) (hx : x ∈ I) (i : Fin 3) : D i (x.2 i) ∈ I := by
    rw [← F.2.2.2.1 i x]
    exact I.sub_mem (I.sub_mem (hU _ _ hx) (hU _ _ hx)) (hU _ _ hx)
  have polarOne : (Zorn.norm R).polarBilin (Zorn.first R) (Zorn.second R) = 1 := by
    simpa [Zorn.first, Zorn.second, ZornSpecification.first, ZornSpecification.second]
      using Zorn.polar_formula R 1 0 0 1 0 0 0 0
  have moveBlock {r : R} {i j : Fin 3} (hji : j ≠ i) (hr : r • E j ∈ I) (b : Zorn R) :
      r • D i b ∈ I := by
    let Q := weightedHermitianJordan γ (Zorn.isOctonion R)
    have op (x y : V) : (ParaQuadratic.ofJordan Q).groundOp x y = U x y :=
      ground_operator γ (Zorn.isOctonion R) x y
    have tr (x y z : V) : groundTriple (ParaQuadratic.ofJordan Q) x y z = T x y z := by
      simp only [groundTriple, QuadraticOperatorSpecification.triple, op]
    have ht := hT (D i b) (E j) (r • E j) hr
    rw [← tr, triple_smul_last, tr] at ht
    have hsym : T (D i b) (E j) (E j) = T (E j) (E j) (D i b) := by
      unfold QuadraticOperatorSpecification.triple
      rw [add_comm (D i b) (E j)]
      abel
    rwa [hsym, axis_to_block R hji] at ht
  have moveAxis {r : R} {j k : Fin 3} (hr : r • E j ∈ I) : r • E k ∈ I := by
    by_cases hjk : j = k
    · rwa [← hjk]
    obtain ⟨i, hji, hki⟩ : ∃ i : Fin 3, j ≠ i ∧ k ≠ i := by
      fin_cases j <;> fin_cases k <;> first | contradiction | decide
    obtain ⟨f, hf⟩ := singleBlock_linear R i
    have hb := moveBlock hji hr (Zorn.first R)
    rw [← hf, ← map_smul, hf] at hb
    have ht := hT (E k) (D i (Zorn.second R)) _ hb
    rwa [axis_block_pair R hki, LinearMap.map_smul₂, smul_eq_mul, polarOne, mul_one] at ht
  have axisScalar {r : R} {j : Fin 3} (hr : r • E j ∈ I) : r ∈ a := by
    apply scalarIdeal_mem.mpr
    change r • (CubicSpecification.cubicUnit : V) ∈ I
    rw [← F.1, Finset.smul_sum]
    exact Submodule.sum_mem I fun k _ => moveAxis hr
  have scalarActs {r : R} (hr : r ∈ a) (x : V) : r • x ∈ I := by
    have haxis (i : Fin 3) : r • E i ∈ I := by
      obtain h := diag (r • cubicUnit) (scalarIdeal_mem.mp hr) i
      simpa [CubicSpecification.cubicUnit] using h
    rw [← F.2.2.2.2.2.2 x, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i _
    rw [F.2.2.1, F.2.2.2.1, smul_add, smul_comm r (x.1 i)]
    exact I.add_mem (I.smul_mem _ (haxis i))
      (moveBlock (j := cyclicNext i) (by fin_cases i <;> decide) (haxis _) _)
  refine le_antisymm (fun x hx => ?_) (Submodule.smul_le.mpr fun r hr x _ => scalarActs hr x)
  rw [← F.2.2.2.2.2.2 x]
  apply Submodule.sum_mem
  intro i _
  rw [F.2.2.1, F.2.2.2.1]
  refine Submodule.add_mem _ (Submodule.smul_mem_smul (axisScalar (diag x hx i)) trivial) ?_
  let j := cyclicNext i
  have hji : j ≠ i := by fin_cases i <;> decide
  have pair_mem (b : Zorn R) : (Zorn.norm R).polarBilin (x.2 i) b ∈ a :=
    axisScalar (axis_block_pair R hji (x.2 i) b ▸ hT (E j) (D i b) _ (block x hx i))
  let B := Zorn.coordinateBasis R
  letI : (Zorn.norm R).polarBilin.IsPerfPair := Zorn.perfect R
  have hcoeff (l : Option (Fin 3) ⊕ Option (Fin 3)) : B.repr (x.2 i) l ∈ a := by
    simpa using pair_mem ((Zorn.norm R).polarBilin.flip.toPerfPair.symm (B.coord l))
  obtain ⟨f, hf⟩ := singleBlock_linear R i
  rw [← hf, ← B.sum_repr (x.2 i), map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (hcoeff l) trivial

end Split

section Descent

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Type u) [CommRing S] [Algebra R S]

private theorem span_tmul_one :
    Submodule.span S (Set.range fun x : M => (1 : S) ⊗ₜ[R] x) = ⊤ := by
  rw [← Submodule.baseChange_top (R := R) (M := M) S, Submodule.baseChange_eq_span]
  congr 1
  ext t
  simp [Submodule.mem_map, LinearMap.mem_range]

private theorem mem_of_linear_on_span {P N : Type*} [AddCommGroup P] [Module S P]
    [AddCommGroup N] [Module S N] (f : P →ₗ[S] N) {I : Submodule S N}
    {s : Set P} (h : ∀ x ∈ s, f x ∈ I) {x : P} (hx : x ∈ Submodule.span S s) :
    f x ∈ I :=
  (Submodule.span_le.mpr (show s ⊆ I.comap f from h)) hx

private theorem baseChange_outer (J : ParaQuadratic R M) (I : Submodule R M)
    (h : IsOuterIdeal J I) :
    IsOuterIdeal (J.baseChange S) (I.baseChange S) := by
  let Q := J.op S
  let B := QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] M)) Q
  let L := I.baseChange S
  let eval (y : S ⊗[R] M) : Module.End S (S ⊗[R] M) →ₗ[S] S ⊗[R] M :=
    LinearMap.applyₗ y
  have hop (x y : S ⊗[R] M) : (J.baseChange S).groundOp x y = Q x y :=
    J.groundOp_baseChange S x y
  have ht (x y z : S ⊗[R] M) : groundTriple (J.baseChange S) x y z = B x z y := by
    simp [groundTriple, hop, B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  have htgen (x y z : M) :
      B (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] z) (1 ⊗ₜ[R] y) =
        (1 : S) ⊗ₜ[R] groundTriple J x y z := by
    simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply,
      ← tmul_add, Q, J.natural_ground, groundTriple, tmul_sub]
  have allSpan (x : S ⊗[R] M) :
      x ∈ Submodule.span S (Set.range fun m : M => (1 : S) ⊗ₜ[R] m) :=
    span_tmul_one (R := R) (M := M) S ▸ Submodule.mem_top
  have idealSpan {y : S ⊗[R] M} (hy : y ∈ L) :
      y ∈ Submodule.span S (I.map (TensorProduct.mk R S M 1)) := by
    simpa only [L, Submodule.baseChange_eq_span] using hy
  have hB (x y z : S ⊗[R] M) (hz : z ∈ L) : B x z y ∈ L := by
    refine mem_of_linear_on_span S ((eval y).comp (B.flip z)) ?_ (allSpan x)
    rintro _ ⟨x, rfl⟩
    change B (1 ⊗ₜ[R] x) z y ∈ L
    refine mem_of_linear_on_span S ((eval y).comp (B (1 ⊗ₜ[R] x))) ?_ (idealSpan hz)
    rintro _ ⟨z, hz, rfl⟩
    change B (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] z) y ∈ L
    refine mem_of_linear_on_span S (B _ _) ?_ (allSpan y)
    rintro _ ⟨y, rfl⟩
    rw [htgen]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (h.2 x y z hz)
  refine ⟨?_, fun x y z hz => ht x y z ▸ hB x y z hz⟩
  intro x y hy
  rw [hop]
  refine mem_of_linear_on_span S (Q x) ?_ (idealSpan hy)
  rintro _ ⟨y, hy, rfl⟩
  have hx := allSpan x
  induction hx using Submodule.span_induction with
  | mem _ hx =>
      obtain ⟨x, rfl⟩ := hx
      change J.op S (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) ∈ L
      rw [J.natural_ground]
      exact Submodule.tmul_mem_baseChange_of_mem 1 (h.1 x y hy)
  | zero => simp [Q]
  | add x z _ _ hx hz =>
      -- The ideal is in the middle slot here, so use linearity in the outer slots.
      have hcross (a b : S ⊗[R] M) : B a b (1 ⊗ₜ[R] y) ∈ L := by
        refine mem_of_linear_on_span S ((eval (1 ⊗ₜ[R] y)).comp (B.flip b)) ?_ (allSpan a)
        rintro _ ⟨a, rfl⟩
        change B (1 ⊗ₜ[R] a) b (1 ⊗ₜ[R] y) ∈ L
        refine mem_of_linear_on_span S ((eval (1 ⊗ₜ[R] y)).comp (B (1 ⊗ₜ[R] a))) ?_ (allSpan b)
        rintro _ ⟨b, rfl⟩
        change B (1 ⊗ₜ[R] a) (1 ⊗ₜ[R] b) (1 ⊗ₜ[R] y) ∈ L
        rw [htgen]
        exact Submodule.tmul_mem_baseChange_of_mem 1
          (I.sub_mem (I.sub_mem (h.1 _ _ hy) (h.1 _ _ hy)) (h.1 _ _ hy))
      have hc := hcross x z
      simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply] at hc
      simp only [TensorProduct.mk_apply] at hx hz ⊢
      convert L.add_mem (L.add_mem hc hz) hx using 1
      abel
  | smul a x _ hx =>
      rw [Q.map_smul, LinearMap.smul_apply]
      exact L.smul_mem _ hx

private theorem baseChange_scalarIdeal [Module.Flat R S] (e : M) (I : Submodule R M) :
    scalarIdeal (1 ⊗ₜ[R] e : S ⊗[R] M) (I.baseChange S) =
      (scalarIdeal e I).map (algebraMap R S) := by
  let f := I.mkQ ∘ₗ LinearMap.toSpanSingleton R M e
  let ρ := AlgebraTensorModule.rid R S S
  have hker : (f.baseChange S).ker = (f.ker).baseChange S :=
    Module.Flat.ker_lTensor_eq S S f
  have hI : (I.mkQ.baseChange S).ker = I.baseChange S := by
    change ((AlgebraTensorModule.lTensor S S) I.mkQ).ker = _
    rw [Module.Flat.ker_lTensor_eq S S I.mkQ, Submodule.ker_mkQ]
    rfl
  have heq : (scalarIdeal e I : Submodule R R) = f.ker := by
    ext r
    change r • e ∈ I ↔ (Submodule.Quotient.mk (r • e) : M ⧸ I) = 0
    exact (Submodule.Quotient.mk_eq_zero I).symm
  have htransport :
      (scalarIdeal (1 ⊗ₜ[R] e : S ⊗[R] M) (I.baseChange S) : Submodule S S) =
        (f.baseChange S).ker.map ρ.toLinearMap := by
    ext s
    rw [scalarIdeal_mem, ← hI, Submodule.mem_map]
    constructor
    · intro hs
      refine ⟨s ⊗ₜ[R] 1, ?_, by simp [ρ]⟩
      simpa [f, TensorProduct.smul_tmul'] using hs
    · rintro ⟨t, ht, rfl⟩
      rw [← ρ.symm_apply_apply t] at ht
      change ρ t ⊗ₜ[R] (1 : R) ∈ (f.baseChange S).ker at ht
      simpa [f, TensorProduct.smul_tmul'] using ht
  apply Submodule.ext
  intro s
  change s ∈ (scalarIdeal (1 ⊗ₜ[R] e : S ⊗[R] M) (I.baseChange S) : Submodule S S) ↔ _
  rw [htransport, hker, ← heq, Submodule.baseChange_eq_span, Submodule.map_span]
  have hset :
      ρ.toLinearMap '' (Submodule.map (TensorProduct.mk R S R 1) (scalarIdeal e I : Submodule R R) :
        Set (S ⊗[R] R)) = algebraMap R S '' (scalarIdeal e I : Set R) := by
    ext t
    simp [Submodule.mem_map, ρ, Algebra.smul_def]
  rw [hset]
  rfl

private theorem tmul_one_smul (r : R) (m : M) :
    (1 : S) ⊗ₜ[R] (r • m) = algebraMap R S r • ((1 : S) ⊗ₜ[R] m) := by
  rw [← TensorProduct.smul_tmul, ← IsScalarTower.algebraMap_smul S r (1 : S),
    TensorProduct.smul_tmul']

private theorem baseChange_scalarMultiple (a : Ideal R) :
    (a • (⊤ : Submodule R M)).baseChange S =
      a.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) := by
  let I := a • (⊤ : Submodule R M)
  let L := a.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M))
  refine le_antisymm ?_ ?_
  · rw [Submodule.baseChange_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    change (1 : S) ⊗ₜ[R] x ∈ L
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      rw [tmul_one_smul S]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R S) hr) trivial
    · intro x y hx hy
      rw [tmul_add]
      exact L.add_mem hx hy
  · apply Submodule.smul_le.mpr
    intro s hs x _
    refine mem_of_linear_on_span S ((LinearMap.toSpanSingleton S (S ⊗[R] M) x))
      ?_ (show s ∈ Submodule.span S (algebraMap R S '' (a : Set R)) from hs)
    rintro _ ⟨r, hr, rfl⟩
    change algebraMap R S r • x ∈ I.baseChange S
    refine mem_of_linear_on_span S (algebraMap R S r • LinearMap.id) ?_
      (show x ∈ Submodule.span S (Set.range fun m : M => (1 : S) ⊗ₜ[R] m) from
        span_tmul_one (R := R) (M := M) S ▸ Submodule.mem_top)
    rintro _ ⟨m, rfl⟩
    change algebraMap R S r • ((1 : S) ⊗ₜ[R] m) ∈ I.baseChange S
    rw [← tmul_one_smul S]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.smul_mem_smul hr trivial)

private theorem split_cover_ideal (J : ParaQuadratic R M) (I : Submodule R M)
    (h : IsOuterIdeal J I) (hc : OnComponent J S .octonion) :
    I.baseChange S =
      scalarIdeal (1 ⊗ₜ[R] J.unit : S ⊗[R] M) (I.baseChange S) •
        (⊤ : Submodule S (S ⊗[R] M)) := by
  obtain ⟨e, he, hop⟩ := hc
  let L := I.baseChange S
  let K := L.map e.toLinearMap
  have hL := baseChange_outer S J I h
  have hu (x y : S ⊗[R] M) : e ((J.baseChange S).groundOp x y) =
      QuadraticOperatorSpecification.applyOperator (Zorn.norm S)
        (LowerRankSpecification.untwisted S) (e x) (e y) := by
    rw [J.groundOp_baseChange]
    exact hop x y
  have htr (x y z : S ⊗[R] M) : e (groundTriple (J.baseChange S) x y z) =
      QuadraticOperatorSpecification.triple (Zorn.norm S)
        (LowerRankSpecification.untwisted S) (e x) (e y) (e z) := by
    simp only [groundTriple, QuadraticOperatorSpecification.triple, map_sub, hu, map_add]
  have hK := split_coordinate_ideals S K (by
    intro x y hy
    obtain ⟨y, hy, rfl⟩ := hy
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [LinearEquiv.coe_coe, ← hu]
    exact Submodule.mem_map_of_mem (hL.1 x y hy)) (by
    intro x y z hz
    obtain ⟨z, hz, rfl⟩ := hz
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [LinearEquiv.coe_coe, ← htr]
    exact Submodule.mem_map_of_mem (hL.2 x y z hz))
  have hscalar : scalarIdeal (cubicUnit : Coordinates S (Zorn S)) K =
      scalarIdeal (1 ⊗ₜ[R] J.unit : S ⊗[R] M) L := by
    ext r
    simp only [scalarIdeal_mem, ← he, ← map_smul, K, LinearEquiv.coe_coe,
      Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [hscalar] at hK
  apply (Submodule.map_injective_of_injective e.injective)
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact hK

end Descent

theorem albert_outer_ideals : AlbertOuterIdealsType.{u, v} := by
  intro R _ M _ _ J hJ I
  have hclass (h : IsOuterIdeal J I) :
      I = scalarIdeal J.unit I • (⊤ : Submodule R M) := by
    obtain ⟨S, _, _, hff, hc⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
    letI := hff
    apply Submodule.baseChange_injective (A := S)
    rw [split_cover_ideal S J I h hc, baseChange_scalarIdeal, baseChange_scalarMultiple]
  refine ⟨⟨hclass, ?_⟩, ?_⟩
  · intro he
    exact he ▸ (scalarMultiple_isIdeal J (scalarIdeal J.unit I)).1
  · intro h
    exact hclass h ▸ scalarMultiple_isIdeal J (scalarIdeal J.unit I)

private theorem albert_unit_ne_zero {k : Type u} [Field k] {M : Type v} [AddCommGroup M]
    [Module k M] (J : ParaQuadratic k M) (hJ : IsAlbert J) : J.unit ≠ 0 := by
  obtain ⟨S, _, _, hff, e, he, _⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  letI := hff
  haveI : Nontrivial S := (FaithfulSMul.algebraMap_injective k S).nontrivial
  intro hz
  rw [hz, tmul_zero, map_zero] at he
  exact zero_ne_one (congrArg (fun x : Coordinates S (Zorn S) => x.1 0) he)

private theorem albert_outer_trivial {k : Type u} [Field k] {M : Type v} [AddCommGroup M]
    [Module k M] (J : ParaQuadratic k M) (hJ : IsAlbert J) (I : Submodule k M)
    (hI : IsOuterIdeal J I) : I = ⊥ ∨ I = ⊤ := by
  have he := (albert_outer_ideals J hJ I).1.mp hI
  rcases (scalarIdeal J.unit I).eq_bot_or_top with h | h
  · left
    simpa only [h, Submodule.bot_smul] using he
  · right
    simpa only [h, Submodule.top_smul] using he

theorem albert_quadratic_simple : AlbertQuadraticSimpleType.{u, v} := by
  intro k _ M _ _ J hJ
  exact ⟨freudenthal_is_jordan J hJ.1, albert_unit_ne_zero J hJ,
    fun I hI => albert_outer_trivial J hJ I hI.1⟩

section Linear

open private QuadraticJordan.groundProduct_at
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticJordan

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

private theorem linear_ideal_is_outer (J : QuadraticJordan R M) (d : Rˣ) (hd : (d : R) = 2)
    (I : Submodule R M) (hI : ∀ x y, y ∈ I → J.groundProduct d x y ∈ I) :
    IsOuterIdeal (ParaQuadratic.ofJordan J) I := by
  let p := J.groundProduct d
  have hcomm (x y : M) : p x y = p y x := (QuadraticJordan.toLinearJordan J d hd).comm x y
  have hop (x y : M) : (ParaQuadratic.ofJordan J).groundOp x y =
      (2 : R) • p x (p x y) - p (p x x) y := by
    apply (TensorProduct.lid R M).symm.injective
    change (1 : R) ⊗ₜ[R] (ParaQuadratic.ofJordan J).groundOp x y = _
    rw [← (ParaQuadratic.ofJordan J).groundOp_lift]
    change J.op R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) = _
    simp only [p, map_sub, map_smul, QuadraticJordan.groundProduct_at]
    rw [QuadraticJordan.op_eq_operatorOfProduct J R d hd]
    have h (a b : M) : (1 : R) ⊗ₜ[R] J.groundProduct d a b =
        J.linearProduct R d (1 ⊗ₜ[R] a) (1 ⊗ₜ[R] b) :=
      QuadraticJordan.groundProduct_at J d a b
    rw [h x y, h x x]
    rfl
  refine ⟨?_, ?_⟩
  · intro x y hy
    rw [hop]
    exact I.sub_mem (I.smul_mem _ (hI _ _ (hI _ _ hy))) (hI _ _ hy)
  · intro x y z hz
    have hleft (w : M) : p z w ∈ I := hcomm z w ▸ hI w z hz
    have hsum : (2 : R) • (p x (p z y) + p z (p x y)) -
        p (p x z + p z x) y ∈ I :=
      I.sub_mem (I.smul_mem _ (I.add_mem (hI _ _ (hleft y)) (hleft (p x y)))) (by
        rw [hcomm]
        exact hI _ _ (I.add_mem (hI _ _ hz) (hleft x)))
    convert hsum using 1
    unfold groundTriple
    simp only [hop, map_add, LinearMap.add_apply, smul_add]
    abel

theorem albert_linear_simple : AlbertLinearSimpleType.{u, v} := by
  intro k _ M _ _ J hJ d hd
  refine ⟨albert_unit_ne_zero (ParaQuadratic.ofJordan J) hJ, ?_⟩
  intro I hI
  exact albert_outer_trivial (ParaQuadratic.ofJordan J) hJ I (linear_ideal_is_outer J d hd I hI)

end Linear
end LinearAlgebraicGroups.Albert
