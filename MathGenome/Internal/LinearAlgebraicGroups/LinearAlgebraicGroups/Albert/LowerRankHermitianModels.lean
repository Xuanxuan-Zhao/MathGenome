import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.LowerRankHermitianModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.ZornModel
import Batteries.Tactic.OpenPrivate

/-! The untwisted Hermitian models and their restrictions from Zorn coordinates. -/

namespace LinearAlgebraicGroups.Albert.LowerRank

open _root_.LinearAlgebraicGroups.Composition hiding conjugate scalarNorm
open Composition.AdjointSpecification (conjugate trace)
open LowerRankSpecification
open scoped Matrix TensorProduct

universe u v

noncomputable section

variable {R : Type u} [CommRing R]

private theorem trace_of_norm {C : Type v} [NonAssocRing C] [Module R C]
    {n : QuadraticForm R C} {e : C →ₗ[R] Zorn R}
    (hone : e 1 = 1) (hnorm : ∀ x, ZornSpecification.norm R (e x) = n x) (x : C) :
    trace n x = trace (ZornSpecification.norm R) (e x) := by
  change n.polarBilin x 1 = (ZornSpecification.norm R).polarBilin (e x) 1
  rw [← hone]
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hnorm]

private theorem conjugate_of_norm {C : Type v} [NonAssocRing C] [Module R C]
    {n : QuadraticForm R C} {e : C →ₗ[R] Zorn R}
    (hone : e 1 = 1) (hnorm : ∀ x, ZornSpecification.norm R (e x) = n x) (x : C) :
    e (conjugate n x) = conjugate (ZornSpecification.norm R) (e x) := by
  change e (trace n x • (1 : C) - x) = trace (ZornSpecification.norm R) (e x) • 1 - e x
  rw [map_sub, map_smul, hone, trace_of_norm hone hnorm]

private def axis (a : R) : Fin 3 → R := ![a, 0, 0]

private theorem axis_single (a : R) : Pi.single (0 : Fin 3) a = axis a := by
  funext i
  fin_cases i <;> simp [axis]

@[simp] private theorem scalar_slots (a : R) :
    scalarEmbedding R a = Zorn.ofCoordinates (a, 0, 0, a) := rfl

@[simp] private theorem pair_slots (a b : R) :
    pairEmbedding R (a, b) = Zorn.ofCoordinates (a, 0, 0, b) := rfl

@[simp] private theorem quaternion_slots (x : SplitQuaternion R) :
    quaternionEmbedding R x = Zorn.ofCoordinates (x 0 0, axis (x 0 1), axis (x 1 0), x 1 1) := by
  change Zorn.ofCoordinates (x 0 0, Pi.single 0 (x 0 1), Pi.single 0 (x 1 0), x 1 1) = _
  simp only [axis_single]

private theorem diagonal_mul (a b c d : R) :
    Zorn.ofCoordinates (a, 0, 0, b) * Zorn.ofCoordinates (c, 0, 0, d) =
      Zorn.ofCoordinates (a * c, 0, 0, b * d) := by
  change Zorn.ofCoordinates (Composition.Specification.zornProduct (a, 0, 0, b) (c, 0, 0, d)) = _
  simp [Composition.Specification.zornProduct]

private theorem axis_dot (a b : R) : dotProduct (axis a) (axis b) = a * b := by
  simp [dotProduct, Fin.sum_univ_three, axis]

private theorem axis_cross (a b : R) : crossProduct (axis a) (axis b) = 0 := by
  funext i
  fin_cases i <;> simp [crossProduct, axis]

private theorem axis_add (a b : R) : axis a + axis b = axis (a + b) := by
  funext i
  fin_cases i <;> simp [axis]

private theorem axis_smul (a b : R) : a • axis b = axis (a * b) := by
  funext i
  fin_cases i <;> simp [axis, smul_eq_mul]

private theorem axis_neg (a : R) : -axis a = axis (-a) := by
  funext i
  fin_cases i <;> simp [axis]

private theorem matrix_norm (x : SplitQuaternion R) : quaternionNorm R x = x.det := by
  rw [Matrix.det_fin_two]
  rfl

theorem embeddings : LowerRankSpecification.embeddingsType.{u} := by
  intro R _
  refine ⟨⟨?_, rfl, ?_, ?_, ?_⟩, ⟨?_, rfl, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact LinearMap.ext fun _ => rfl
  · intro a b
    simp only [scalar_slots, diagonal_mul]
  · intro a
    rw [scalar_slots, Zorn.norm_formula]
    simp [Composition.Specification.zornNorm, Composition.Specification.scalarNorm]
  · apply conjugate_of_norm (e := scalarEmbedding R) rfl
    intro a
    rw [scalar_slots, Zorn.norm_formula]
    simp [Composition.Specification.zornNorm, Composition.Specification.scalarNorm]
  · exact LinearMap.ext fun _ => rfl
  · rintro ⟨a, b⟩ ⟨c, d⟩
    change pairEmbedding R (a * c, b * d) = _
    simp only [pair_slots, diagonal_mul]
  · rintro ⟨a, b⟩
    rw [pair_slots, Zorn.norm_formula]
    simp [Composition.Specification.zornNorm, pairNorm]
  · apply conjugate_of_norm (e := pairEmbedding R) rfl
    rintro ⟨a, b⟩
    rw [pair_slots, Zorn.norm_formula]
    simp [Composition.Specification.zornNorm, pairNorm]
  · apply LinearMap.ext
    intro x
    change quaternionProjection R (quaternionEmbedding R x) = x
    rw [quaternion_slots]
    change !![x 0 0, axis (x 0 1) 0; axis (x 1 0) 0, x 1 1] = x
    exact (Matrix.eta_fin_two x).symm
  · rw [quaternion_slots]
    have h : axis (0 : R) = 0 := by funext i; fin_cases i <;> rfl
    simp [h]
    rfl
  · intro x y
    simp only [quaternion_slots]
    change Zorn.ofCoordinates
      ((x * y) 0 0, axis ((x * y) 0 1), axis ((x * y) 1 0), (x * y) 1 1) =
      Zorn.ofCoordinates (Composition.Specification.zornProduct
        (x 0 0, axis (x 0 1), axis (x 1 0), x 1 1)
        (y 0 0, axis (y 0 1), axis (y 1 0), y 1 1))
    simp only [Composition.Specification.zornProduct, axis_dot, axis_cross, axis_smul,
      sub_zero, add_zero, axis_add, Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_comm (y 1 1), mul_comm (y 0 0), add_comm (x 1 1 * y 1 1)]
  · intro x
    rw [quaternion_slots, Zorn.norm_formula]
    change x 0 0 * x 1 1 - dotProduct (axis (x 0 1)) (axis (x 1 0)) = _
    rw [axis_dot]
    rfl
  · apply conjugate_of_norm
    · rw [quaternion_slots]
      have h : axis (0 : R) = 0 := by funext i; fin_cases i <;> rfl
      simp [h]
      rfl
    · intro x
      rw [quaternion_slots, Zorn.norm_formula]
      change x 0 0 * x 1 1 - dotProduct (axis (x 0 1)) (axis (x 1 0)) = _
      rw [axis_dot]
      rfl

theorem composition_formulas : LowerRankSpecification.compositionFormulasType.{u} := by
  intro R _
  obtain ⟨⟨hs, _, _, _, hsc⟩, ⟨hp, _, _, _, hpc⟩, ⟨hq, _, _, _, hqc⟩⟩ := embeddings R
  have inj {C : Type u} [AddCommGroup C] [Module R C] {e : C →ₗ[R] Zorn R}
      {p : Zorn R →ₗ[R] C} (h : p.comp e = LinearMap.id) : Function.Injective e :=
    Function.LeftInverse.injective (fun x => LinearMap.congr_fun h x)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    refine ⟨by rw [pow_two]; rfl, (inj hs) ?_⟩
    rw [hsc, scalar_slots, Zorn.conjugate_formula]
    simp
  · intro a b
    refine ⟨rfl, (inj hp) ?_⟩
    rw [hpc, pair_slots, pair_slots, Zorn.conjugate_formula]
    simp
  · intro x
    refine ⟨matrix_norm x, (inj hq) ?_⟩
    rw [hqc, quaternion_slots, quaternion_slots, Zorn.conjugate_formula,
      axis_neg, axis_neg, Matrix.adjugate_fin_two]
    rfl

private theorem scalar_conjugate (r : R) : conjugate (scalarNorm R) r = r :=
  (composition_formulas R).1 r |>.2

theorem scalar_adjoint : LowerRankSpecification.scalarAdjointType.{u} := by
  intro R _ x
  apply Prod.ext
  · funext i
    simp [CubicSpecification.cubicAdjoint, LowerRankSpecification.scalarAdjoint,
      CubicSpecification.blockWeight, Composition.Specification.scalarNorm, pow_two]
  · funext i
    simp [CubicSpecification.cubicAdjoint, LowerRankSpecification.scalarAdjoint,
      scalar_conjugate, smul_eq_mul]
    ring


@[simp] private theorem scalar_assemble (x : Coordinates R R) :
    assemble (scalarNorm R) (untwisted R) x = scalarMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianSpecification.assemble, scalarMatrix, scalar_conjugate, smul_eq_mul]

@[simp] private theorem scalar_trace_apply (x y : Coordinates R R) :
    tracePairing (scalarNorm R) (untwisted R) x y =
      ∑ i, (x.1 i * y.1 i + 2 * x.2 i * y.2 i) := by
  rw [tracePairing_apply]
  simp only [CubicSpecification.blockWeight, Units.val_one, mul_one, one_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (_ + ·) (Composition.scalar_polar R _ _)

theorem scalar_trace : LowerRankSpecification.scalarTraceType.{u} := by
  intro R _
  refine ⟨Composition.scalar_polar_perfect_iff R, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    let e : Coordinates R R := (0, Pi.single 0 1)
    let f : Coordinates R R →ₗ[R] R :=
      (LinearMap.proj 0).comp (LinearMap.snd R _ _)
    obtain ⟨x, hx⟩ := (LinearMap.IsPerfPair.bijective_left
      (tracePairing (scalarNorm R) (untwisted R))).surjective f
    have heq := LinearMap.congr_fun hx e
    rw [scalar_trace_apply, Fin.sum_univ_three] at heq
    have hu : (2 : R) * x.2 0 = 1 := by
      simpa [e, f, Pi.single_apply] using heq
    exact ⟨⟨2, x.2 0, hu, (mul_comm _ _).trans hu⟩, rfl⟩
  · intro h
    exact tracePairing_perfect (untwisted R) ((Composition.scalar_polar_perfect_iff R).mpr h)
  · intro h c y
    rw [scalar_trace_apply]
    simp [h]
  · intro h hn hd
    let := hn
    let x : Coordinates R R := (0, Pi.single 0 1)
    have hx : x = 0 := hd.1 x fun y => by rw [scalar_trace_apply]; simp [x, h]
    have : (1 : R) = 0 := by
      simpa [x] using congrArg (fun z : Coordinates R R => z.2 0) hx
    exact one_ne_zero this

theorem scalar_sandwich : LowerRankSpecification.scalarSandwichType.{u} := by
  intro R _ x y
  change scalarMatrix (tracePairing (scalarNorm R) (untwisted R) x y • x -
    adjointCross (scalarNorm R) (untwisted R)
      (cubicAdjoint (scalarNorm R) (untwisted R) x) y) = _
  have ha (z : Coordinates R R) :
      CubicSpecification.cubicAdjoint (scalarNorm R) (untwisted R) z =
        LowerRankSpecification.scalarAdjoint z := scalar_adjoint R z
  simp only [CubicSpecification.adjointCross, ha, scalar_trace_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarMatrix, LowerRankSpecification.scalarAdjoint, Fin.sum_univ_three,
      HermitianSpecification.cyclicNext, HermitianSpecification.cyclicPrev,
      Matrix.mul_apply, smul_eq_mul] <;> ring

private theorem scalar_mem_iff (X : Mat R) :
    X ∈ hermitian (scalarNorm R) (untwisted R) ↔ X.IsSymm := by
  change ((∀ i j, conjugate (scalarNorm R) (X j i) =
    HermitianSpecification.weight (untwisted R) i j • X i j) ∧ _) ↔ X.transpose = X
  simp only [scalar_conjugate, HermitianSpecification.weight, untwisted, inv_one, mul_one,
    Units.val_one, one_smul]
  constructor
  · intro h
    exact Matrix.ext h.1
  · intro h
    exact ⟨fun i j => congr_fun (congr_fun h i) j, fun i => ⟨X i i, mul_one _⟩⟩


open private entry_cases from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.HermitianCoordinates

private theorem untwisted_weight (i j : Fin 3) :
    HermitianSpecification.weight (untwisted R) i j = 1 := by
  simp [HermitianSpecification.weight]

private theorem hermitian_coordinates {C : Type*} [NonAssocRing C] [Module R C]
    {n : QuadraticForm R C} {e : C →ₗ[R] Zorn R} {p : Zorn R →ₗ[R] C}
    (h : embeddingLaws n e p) :
    ∃ f : Coordinates R C ≃ₗ[R] hermitian n (untwisted R),
      ∀ x, (f x : Mat C) = assemble n (untwisted R) x := by
  obtain ⟨hp, h1, _, _, hc⟩ := h
  have hinj : Function.Injective e :=
    Function.LeftInverse.injective (fun x => LinearMap.congr_fun hp x)
  have ci (x : C) : conjugate n (conjugate n x) = x := by
    apply hinj
    rw [hc, hc, Composition.conjugate_involutive (Zorn.isOctonion R).toNormLaws]
  have cu : conjugate n (1 : C) = 1 := by
    apply hinj
    rw [hc, h1, Composition.conjugate_one (Zorn.isOctonion R).toNormLaws]
  let f : Coordinates R C →ₗ[R] hermitian n (untwisted R) :=
    { toFun := fun x => ⟨assemble n (untwisted R) x, by
        refine ⟨fun i j => ?_, fun i => ⟨x.1 i, (assemble_diagonal x i).symm⟩⟩
        rw [untwisted_weight, one_smul]
        rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;>
          simp [assemble_diagonal, assemble_forward, assemble_backward, cu, ci]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Matrix.ext
        intro i j
        rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;>
          simp [Matrix.add_apply, assemble_diagonal, assemble_forward, assemble_backward, add_smul]
      map_smul' := by
        intro r x
        apply Subtype.ext
        apply Matrix.ext
        intro i j
        rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;>
          simp [Matrix.smul_apply, assemble_diagonal, assemble_forward, assemble_backward, mul_smul] }
  refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro x y hxy
    have hh : assemble n (untwisted R) x = assemble n (untwisted R) y := congrArg Subtype.val hxy
    apply Prod.ext <;> funext i
    · have hi := congrArg (fun M : Mat C => scalarProjection R (e (M i i))) hh
      simpa only [assemble_diagonal, map_smul, h1, smul_eq_mul, mul_one,
        show scalarProjection R (1 : Zorn R) = 1 from rfl] using hi
    · simpa only [assemble_forward, Units.val_one, one_smul] using
        congrArg (fun M : Mat C => M (cyclicNext i) (cyclicPrev i)) hh
  · intro x
    obtain ⟨hx, hd⟩ := x.property
    choose a ha using hd
    refine ⟨(a, fun i => x.val (cyclicNext i) (cyclicPrev i)), ?_⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change assemble n (untwisted R) _ i j = x.val i j
    rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · exact (assemble_diagonal _ i).trans (ha i)
    · simp [assemble_forward]
    · simpa only [assemble_backward, untwisted_weight, Units.val_one, one_smul] using
        (show conjugate n (x.val (cyclicNext k) (cyclicPrev k)) =
          HermitianSpecification.weight (untwisted R) (cyclicPrev k) (cyclicNext k) •
            x.val (cyclicPrev k) (cyclicNext k) from hx _ _)

theorem scalar_matrix : LowerRankSpecification.scalarMatrixType.{u} := by
  intro R _
  obtain ⟨f, hf⟩ := hermitian_coordinates (embeddings R).1
  exact ⟨f, fun x => (hf x).trans (scalar_assemble x), scalar_mem_iff⟩

section Agreement

variable {C D : Type*} [NonAssocRing C] [Module R C] [NonAssocRing D] [Module R D]
variable {n : QuadraticForm R C} {m : QuadraticForm R D} {e : C →ₗ[R] D}

@[simp] private theorem mapBlocks_diag (x : Coordinates R C) (i : Fin 3) :
    (mapBlocks e x).1 i = x.1 i := rfl

@[simp] private theorem mapBlocks_off (x : Coordinates R C) (i : Fin 3) :
    (mapBlocks e x).2 i = e (x.2 i) := rfl

private theorem mapBlocks_unit : mapBlocks e (cubicUnit (R := R) (A := C)) = cubicUnit := by
  apply Prod.ext
  · rfl
  · funext i
    exact e.map_zero

private theorem mapBlocks_comp {E : Type*} [AddCommGroup E] [Module R E]
    (f : D →ₗ[R] E) :
    mapBlocks (f.comp e) = (mapBlocks f).comp (mapBlocks e) := rfl

private theorem polar_map (hn : ∀ x, m (e x) = n x) (x y : C) :
    m.polarBilin (e x) (e y) = n.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hn]

private theorem formula_agreement (h1 : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y)
    (hn : ∀ x, m (e x) = n x) : formulaAgreement n m e := by
  have t (x : C) : trace m (e x) = trace n x := by
    change m.polarBilin (e x) 1 = n.polarBilin x 1
    rw [← h1, polar_map hn]
  have c (x : C) : conjugate m (e x) = e (conjugate n x) := by
    simp only [Composition.conjugate_apply, map_sub, map_smul, h1, t]
  have adj (x : Coordinates R C) :
      cubicAdjoint m (untwisted R) (mapBlocks e x) =
        mapBlocks e (cubicAdjoint n (untwisted R) x) := by
    apply Prod.ext <;> funext i
    · simp only [CubicSpecification.cubicAdjoint, mapBlocks_diag, mapBlocks_off, hn]
    · simp only [CubicSpecification.cubicAdjoint, mapBlocks_diag, mapBlocks_off,
        ← hm, c, map_add, map_smul]
  have form (x y : Coordinates R C) :
      tracePairing m (untwisted R) (mapBlocks e x) (mapBlocks e y) =
        tracePairing n (untwisted R) x y := by
    simp only [tracePairing_apply, mapBlocks_diag, mapBlocks_off, polar_map hn]
  have cross (x y : Coordinates R C) :
      adjointCross m (untwisted R) (mapBlocks e x) (mapBlocks e y) =
        mapBlocks e (adjointCross n (untwisted R) x y) := by
    simp only [CubicSpecification.adjointCross, map_sub, ← map_add, adj]
  refine ⟨mapBlocks_unit, ?_, adj, form, ?_, ?_⟩
  · intro x
    simp only [CubicSpecification.cubicNorm, mapBlocks_diag, mapBlocks_off, hn, ← hm, t]
  · intro x y
    simp only [QuadraticOperatorSpecification.applyOperator, form, adj, cross, map_sub, map_smul]
  · intro x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianSpecification.assemble, ← c, h1, map_smul]

end Agreement

section Tensors

variable {C D : Type*} [NonAssocRing C] [Module R C] [IsScalarTower R C C]
  [SMulCommClass R C C] [NonAssocRing D] [Module R D] [IsScalarTower R D D]
  [SMulCommClass R D D] {e : C →ₗ[R] D}
variable (S : Type*) [CommRing S] [Algebra R S]

omit [IsScalarTower R C C] [SMulCommClass R C C] [IsScalarTower R D D] [SMulCommClass R D D] in
private theorem baseChange_one (h : e 1 = 1) : e.baseChange S 1 = 1 := by
  change e.baseChange S (1 ⊗ₜ[R] 1) = 1 ⊗ₜ[R] 1
  rw [LinearMap.baseChange_tmul, h]

private theorem baseChange_mul (h : ∀ x y, e (x * y) = e x * e y)
    (x y : S ⊗[R] C) : e.baseChange S (x * y) = e.baseChange S x * e.baseChange S y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [add_mul, hx, hz]
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [mul_add, hy, hz]
    | tmul t y => simp [Algebra.TensorProduct.tmul_mul_tmul, h]

omit [IsScalarTower R C C] [SMulCommClass R C C] [IsScalarTower R D D] [SMulCommClass R D D] in
private theorem baseChange_norm [Module.Projective R C] [Module.Projective R D]
    {n : QuadraticForm R C} {m : QuadraticForm R D} (h : ∀ x, m (e x) = n x)
    (x : S ⊗[R] C) : normBaseChange S m (e.baseChange S x) = normBaseChange S n x := by
  have he : (normBaseChange S m).comp (e.baseChange S) = normBaseChange S n := by
    apply _root_.baseChange_ext
    intro x
    simp [h]
  exact congrArg (fun q : QuadraticForm S (S ⊗[R] C) => q x) he

omit [IsScalarTower R D D] [SMulCommClass R D D] in
private theorem coordinatesBaseChange_mapBlocks (x : S ⊗[R] Coordinates R C) :
    coordinatesBaseChange S ((mapBlocks e).baseChange S x) =
      mapBlocks (e.baseChange S) (coordinatesBaseChange S x) := by
  apply LinearMap.congr_fun (f := (coordinatesBaseChange S).toLinearMap.comp
    ((mapBlocks e).baseChange S)) (g := (mapBlocks (e.baseChange S)).comp
    (coordinatesBaseChange S).toLinearMap) _ x
  apply TensorProduct.AlgebraTensorModule.ext
  intro s a
  change coordinatesBaseChange S ((mapBlocks e).baseChange S (s ⊗ₜ[R] a)) = _
  rw [LinearMap.baseChange_tmul]
  change coordinatesBaseChange S (s ⊗ₜ[R] mapBlocks e a) =
    mapBlocks (e.baseChange S) (coordinatesBaseChange S (s ⊗ₜ[R] a))
  rw [coordinatesBaseChange_tmul, coordinatesBaseChange_tmul]
  rfl

end Tensors

section QuadraticRestriction

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (K : QuadraticJordan R N) (j : M →ₗ[R] N) (p : N →ₗ[R] M)
variable (hj : p.comp j = LinearMap.id)

include hj in
private theorem tensor_leftInverse (S : Type u) [CommRing S] [Algebra R S] :
    Function.LeftInverse (p.baseChange S) (j.baseChange S) := by
  intro x
  have he := congrArg (LinearMap.baseChange S) hj
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at he
  exact LinearMap.congr_fun he x

private def restrictOp (S : Type u) [CommRing S] [Algebra R S] :
    QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)) :=
  let b := S ⊗[R] M
  let a := S ⊗[R] N
  let post : (b →ₗ[S] a) →ₗ[S] (b →ₗ[S] b) :=
    LinearMap.llcomp S b a b (p.baseChange S)
  (post ∘ₗ LinearMap.lcomp S a (j.baseChange S)).compQuadraticMap
    ((K.op S).comp (j.baseChange S))

private theorem restrictOp_apply (S : Type u) [CommRing S] [Algebra R S]
    (x y : S ⊗[R] M) :
    restrictOp K j p S x y = p.baseChange S (K.op S (j.baseChange S x) (j.baseChange S y)) := rfl

private theorem rTensor_baseChange {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (l : M →ₗ[R] N) (x : S ⊗[R] M) :
    f.toLinearMap.rTensor N (l.baseChange S x) =
      l.baseChange T (f.toLinearMap.rTensor M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => rfl
  | add x y hx hy => simp [hx, hy]

private def restrictLaw : QuadraticOperatorLaw R M where
  op := restrictOp K j p
  natural f x y := by
    simp only [restrictOp_apply, rTensor_baseChange, K.natural]

variable (unit : M) (hu : j unit = K.unit)
variable (closed : ∀ (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M),
  j.baseChange S (restrictOp K j p S x y) = K.op S (j.baseChange S x) (j.baseChange S y))

include closed in
private theorem restrictTriple (S : Type u) [CommRing S] [Algebra R S]
    (x y z : S ⊗[R] M) :
    j.baseChange S ((restrictLaw K j p).triple S x y z) =
      K.toQuadraticOperatorLaw.triple S (j.baseChange S x) (j.baseChange S y) (j.baseChange S z) := by
  change j.baseChange S
    (QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] M))
      (restrictOp K j p S) x z y) =
    QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] N))
      (K.op S) (j.baseChange S x) (j.baseChange S z) (j.baseChange S y)
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply,
    map_sub, closed S, map_add]

private def restrictJordan : QuadraticJordan R M where
  toQuadraticOperatorLaw := restrictLaw K j p
  unit := unit
  op_unit S _ _ := by
    apply LinearMap.ext
    intro y
    change restrictOp K j p S (1 ⊗ₜ[R] unit) y = y
    apply (tensor_leftInverse j p hj S).injective
    rw [closed S, LinearMap.baseChange_tmul, hu, K.op_unit]
    rfl
  fundamental S _ _ x y := by
    apply LinearMap.ext
    intro z
    change restrictOp K j p S (restrictOp K j p S x y) z =
      restrictOp K j p S x (restrictOp K j p S y (restrictOp K j p S x z))
    apply (tensor_leftInverse j p hj S).injective
    simp only [closed S]
    exact LinearMap.congr_fun (K.fundamental S (j.baseChange S x) (j.baseChange S y))
      (j.baseChange S z)
  commuting S _ _ x y z := by
    apply (tensor_leftInverse j p hj S).injective
    change j.baseChange S (restrictOp K j p S x ((restrictLaw K j p).triple S y x z)) =
      j.baseChange S ((restrictLaw K j p).triple S (restrictOp K j p S x y) z x)
    rw [closed S, restrictTriple K j p closed, restrictTriple K j p closed, closed S]
    exact K.commuting S _ _ _

private theorem lid_baseChange (x : R ⊗[R] M) :
    j (TensorProduct.lid R M x) = TensorProduct.lid R N (j.baseChange R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

end QuadraticRestriction

section Models

variable {C : Type*} [NonAssocRing C] [Module R C] [IsScalarTower R C C]
  [SMulCommClass R C C] [Module.Projective R C]
variable {n : QuadraticForm R C} {e : C →ₗ[R] Zorn R} {p : Zorn R →ₗ[R] C}

set_option maxHeartbeats 850000 in
private theorem restrict_model (h : embeddingLaws n e p) : restrictedModel n e := by
  obtain ⟨hp, h1, hm, hn, _⟩ := h
  let wz := untwisted R
  let j := mapBlocks e
  let r := mapBlocks p
  let unit : Coordinates R C := cubicUnit
  have split : r.comp j = LinearMap.id := by
    change (mapBlocks p).comp (mapBlocks e) = _
    rw [← mapBlocks_comp, hp]
    rfl
  let ho := Zorn.isOctonion R
  obtain ⟨K, huK, ground, extended, _⟩ := weighted_hermitian_quadratic_jordan wz ho
  have hu : j unit = K.unit := huK ▸ mapBlocks_unit
  have groundForm := formula_agreement h1 hm hn
  have extForm (S : Type u) [CommRing S] [Algebra R S] :
      formulaAgreement (normBaseChange S n) (normBaseChange S (zornNorm R)) (e.baseChange S) :=
    formula_agreement (baseChange_one S h1) (baseChange_mul S hm) (baseChange_norm S hn)
  have comparison (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] Coordinates R C) :
      coordinatesBaseChange S (K.op S (j.baseChange S x) (j.baseChange S y)) =
        mapBlocks (e.baseChange S) (applyCubicOperator (normBaseChange S n) (untwisted S)
          (coordinatesBaseChange S x) (coordinatesBaseChange S y)) := by
    have hw : HermitianSpecification.baseChangedWeights S wz = untwisted S := by
      funext i
      exact map_one (Units.map (algebraMap R S).toMonoidHom)
    rw [extended S, hw, coordinatesBaseChange_mapBlocks S, coordinatesBaseChange_mapBlocks S]
    exact (extForm S).2.2.2.2.1 _ _
  have target (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] Coordinates R C) :
      K.op S (j.baseChange S x) (j.baseChange S y) = j.baseChange S
        ((coordinatesBaseChange S).symm
          (applyCubicOperator (normBaseChange S n) (untwisted S)
            (coordinatesBaseChange S x) (coordinatesBaseChange S y))) := by
    apply (coordinatesBaseChange S).injective
    rw [comparison, coordinatesBaseChange_mapBlocks, LinearEquiv.apply_symm_apply]
  have onExtension (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] Coordinates R C) :
      restrictOp K j r S x y = (coordinatesBaseChange S).symm
          (applyCubicOperator (normBaseChange S n) (untwisted S)
            (coordinatesBaseChange S x) (coordinatesBaseChange S y)) := by
    rw [restrictOp_apply, target, tensor_leftInverse j r split S]
  have closed (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] Coordinates R C) :
      j.baseChange S (restrictOp K j r S x y) = K.op S (j.baseChange S x) (j.baseChange S y) := by
    rw [onExtension, ← target]
  let J := restrictJordan K j r split unit hu closed
  refine ⟨J, rfl, ?_, ?_, groundForm, ?_⟩
  · intro x y
    apply (Function.LeftInverse.injective (f := j) (g := r)
      (fun z => LinearMap.congr_fun split z))
    change j (TensorProduct.lid R _ (restrictOp K j r R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y))) =
      j (applyCubicOperator n wz x y)
    rw [lid_baseChange, closed R, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    change K.groundOp (j x) (j y) = _
    rw [ground]
    exact groundForm.2.2.2.2.1 x y
  · intro S _ _ x y
    change coordinatesBaseChange S (restrictOp K j r S x y) = _
    rw [onExtension, LinearEquiv.apply_symm_apply]
  · intro S _ _
    let b := Zorn.baseChange R S
    apply formula_agreement
    · change b (e.baseChange S 1) = 1
      rw [baseChange_one S h1, Zorn.baseChange_one]
    · intro x y
      change b (e.baseChange S (x * y)) = b (e.baseChange S x) * b (e.baseChange S y)
      rw [baseChange_mul S hm, Zorn.baseChange_mul]
    · intro x
      have normZ := congrArg (fun q : QuadraticForm S (S ⊗[R] Zorn R) => q (e.baseChange S x))
        (Zorn.baseChange_norm (R := R) (S := S))
      change zornNorm S (b (e.baseChange S x)) = normBaseChange S n x
      exact normZ.symm.trans (baseChange_norm S hn x)

end Models

theorem restricted_models : LowerRankSpecification.restrictedModelsType.{u} := by
  intro R _
  obtain ⟨hs, hp, hq⟩ := embeddings R
  exact ⟨restrict_model hs, restrict_model hp, restrict_model hq,
    restrict_model (p := LinearMap.id) ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩


private theorem matrix_model {C : Type*} [NonAssocRing C] [Module R C]
    [Module.Free R C] [Module.Finite R C]
    {n : QuadraticForm R C} {e : C →ₗ[R] Zorn R} {p : Zorn R →ₗ[R] C}
    (h : embeddingLaws n e p) (d : ℕ) (hr : ∀ q : PrimeSpectrum R, Module.rankAtStalk C q = d) :
    matrixModel n (3 + 3 * d) := by
  obtain ⟨f, hf⟩ := hermitian_coordinates h
  refine ⟨f, hf, Module.Finite.equiv f, Module.Free.of_equiv f, fun q => ?_⟩
  let := q.nontrivial
  rw [← Module.rankAtStalk_eq_of_equiv f, Module.rankAtStalk_prod]
  change Module.rankAtStalk (Fin 3 → R) q + Module.rankAtStalk (Fin 3 → C) q = _
  rw [Module.rankAtStalk_pi (fun _ : Fin 3 => R), Module.rankAtStalk_pi (fun _ : Fin 3 => C)]
  simp [hr, finsum_eq_sum_of_fintype]

theorem matrix_models : LowerRankSpecification.matrixModelsType.{u} := by
  intro R _
  obtain ⟨hs, hp, hq⟩ := embeddings R
  refine ⟨matrix_model hs 1 (fun q => ?_), matrix_model hp 2 (fun q => ?_),
    matrix_model hq 4 (fun q => ?_), matrix_model (e := LinearMap.id) (p := LinearMap.id) ?_ 8 (Zorn.isOctonion R).rank_eight⟩
  · let := q.nontrivial
    simp
  · let := q.nontrivial
    rw [Module.rankAtStalk_prod]
    simp
  · let := q.nontrivial
    change Module.rankAtStalk (Fin 2 → Fin 2 → R) q = 4
    rw [Module.rankAtStalk_pi (fun _ : Fin 2 => Fin 2 → R)]
    simp [Module.rankAtStalk_pi (fun _ : Fin 2 => R), finsum_eq_sum_of_fintype]
  · exact ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

section NativeBaseChange

variable {S : Type v} [CommRing S] [Algebra R S]
variable {C : Type u} [NonAssocRing C] [Module R C] [Module.Projective R C]
  [IsScalarTower R C C] [SMulCommClass R C C]
variable {D : Type v} [NonAssocRing D] [Module S D]
variable {n : QuadraticForm R C} {m : QuadraticForm S D}
variable {e : C →ₗ[R] Zorn R} {p : Zorn R →ₗ[R] C}
variable {f : D →ₗ[S] Zorn S} {q : Zorn S →ₗ[S] D}

private theorem native_baseChange (hR : embeddingLaws n e p) (hS : embeddingLaws m f q)
    (h : ∀ x : Zorn R,
      ZornSpecification.mapCoordinates (algebraMap R S) (e (p x)) =
        f (q (ZornSpecification.mapCoordinates (algebraMap R S) x))) :
    nativeBaseChange n m e f := by
  obtain ⟨hp, h1, hmul, hn, _⟩ := hR
  obtain ⟨hq, f1, fmul, hm, _⟩ := hS
  let B := Zorn.baseChange R S
  let F := B.toLinearMap.comp (e.baseChange S)
  let P := (p.baseChange S).comp B.symm.toLinearMap
  have pf : Function.LeftInverse P F := by
    intro x
    change p.baseChange S (B.symm (B (e.baseChange S x))) = x
    have hh := congrArg (LinearMap.baseChange S) hp
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hh
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hh x
  have qf : Function.LeftInverse q f := fun z => LinearMap.congr_fun hq z
  have proj (x : S ⊗[R] Zorn R) : F (p.baseChange S x) = f (q (B x)) := by
    induction x using TensorProduct.inductionOn with
    | tmul s z =>
      change B (e.baseChange S (p.baseChange S (s ⊗ₜ[R] z))) = f (q (B (s ⊗ₜ[R] z)))
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Zorn.baseChange_tmul,
        Zorn.baseChange_tmul, q.map_smul, f.map_smul, h]
    | add x y hx hy => simp [hx, hy]
  have commute (z : Zorn S) : F (P z) = f (q z) := by
    change F (p.baseChange S (B.symm z)) = _
    rw [proj, LinearEquiv.apply_symm_apply]
  let b : (S ⊗[R] C) ≃ₗ[S] D :=
    { __ := q.comp F
      invFun := P.comp f
      left_inv := fun z => by
        change P (f (q (F z))) = z
        rw [← commute, pf, pf]
      right_inv := fun z => by
        change q (F (P (f z))) = z
        rw [commute, qf, qf] }
  have hb (z : S ⊗[R] C) : f (b z) = F z := by
    change f (q (F z)) = F z
    rw [← commute, pf]
  refine ⟨b, hb, ?_⟩
  apply formula_agreement
  · apply qf.injective
    change f (b 1) = f 1
    rw [hb, f1]
    change B (e.baseChange S 1) = 1
    rw [baseChange_one S h1, Zorn.baseChange_one]
  · intro x y
    apply qf.injective
    change f (b (x * y)) = f (b x * b y)
    rw [fmul, hb, hb, hb]
    change B (e.baseChange S (x * y)) = B (e.baseChange S x) * B (e.baseChange S y)
    rw [baseChange_mul S hmul, Zorn.baseChange_mul]
  · intro x
    change m (b x) = normBaseChange S n x
    rw [← hm, hb]
    have hZ := congrArg (fun Q : QuadraticForm S (S ⊗[R] Zorn R) => Q (e.baseChange S x))
      (Zorn.baseChange_norm (R := R) (S := S))
    exact hZ.symm.trans (baseChange_norm S hn x)

theorem native_base_changes : LowerRankSpecification.nativeBaseChangesType.{u, v} := by
  intro R S _ _ _
  obtain ⟨hs, hp, hq⟩ := embeddings R
  obtain ⟨hs', hp', hq'⟩ := embeddings S
  refine ⟨native_baseChange hs hs' ?_, native_baseChange hp hp' ?_,
    native_baseChange hq hq' ?_, ?_⟩
  · rintro ⟨a, u, v, b⟩
    change ZornSpecification.mapCoordinates (algebraMap R S) (scalarEmbedding R a) =
      scalarEmbedding S (algebraMap R S a)
    rw [scalar_slots, scalar_slots]
    simp [ZornSpecification.mapCoordinates, Function.comp_def]
    rfl
  · rintro ⟨a, u, v, b⟩
    change ZornSpecification.mapCoordinates (algebraMap R S) (pairEmbedding R (a, b)) =
      pairEmbedding S (algebraMap R S a, algebraMap R S b)
    rw [pair_slots, pair_slots]
    simp [ZornSpecification.mapCoordinates, Function.comp_def]
    rfl
  · rintro ⟨a, u, v, b⟩
    change ZornSpecification.mapCoordinates (algebraMap R S)
      (quaternionEmbedding R !![a, u 0; v 0, b]) =
      quaternionEmbedding S !![algebraMap R S a, algebraMap R S (u 0);
        algebraMap R S (v 0), algebraMap R S b]
    rw [quaternion_slots, quaternion_slots]
    have ha (r : R) : (algebraMap R S) ∘ axis r = axis (algebraMap R S r) := by
      funext i
      fin_cases i <;> simp [axis]
    exact congrArg Zorn.ofCoordinates
      (by simp [ha])
  · exact native_baseChange (p := LinearMap.id) (q := LinearMap.id)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
      ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩ (fun _ => rfl)

end NativeBaseChange

section Components

variable {I : Type u} (B : I → Type u) [∀ i, CommRing (B i)]

private def zornComponents :
    letI (i : I) := componentModule B (fun i => Zorn (B i)) i
    Zorn (∀ i, B i) ≃ₗ[∀ i, B i] (∀ i, Zorn (B i)) :=
  letI (i : I) := componentModule B (fun i => Zorn (B i)) i
  { toFun := fun x i => ZornSpecification.mapCoordinates (Pi.evalRingHom B i) x
    invFun := fun x => Zorn.ofCoordinates
      (fun i => (Zorn.coordinates _ (x i)).1,
        fun j i => (Zorn.coordinates _ (x i)).2.1 j,
        fun j i => (Zorn.coordinates _ (x i)).2.2.1 j,
        fun i => (Zorn.coordinates _ (x i)).2.2.2)
    left_inv := by rintro ⟨a, u, v, b⟩; rfl
    right_inv := by
      intro x
      funext i
      change (Zorn.coordinates (B i)).symm (Zorn.coordinates (B i) (x i)) = x i
      exact (Zorn.coordinates (B i)).symm_apply_apply _
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable (C : I → Type u) [∀ i, NonAssocRing (C i)] [∀ i, Module (B i) (C i)]
variable [∀ i, IsScalarTower (B i) (C i) (C i)] [∀ i, SMulCommClass (B i) (C i) (C i)]

set_option maxHeartbeats 950000 in
set_option linter.style.haveILetI false in
private theorem construct_components (n : ∀ i, QuadraticForm (B i) (C i))
    (e : ∀ i, C i →ₗ[B i] Zorn (B i)) (p : ∀ i, Zorn (B i) →ₗ[B i] C i)
    (h : ∀ i, embeddingLaws (n i) (e i) (p i)) : componentModels B C n := by
  let A := ∀ i, B i
  letI (i : I) : Module A (C i) := componentModule B C i
  letI (i : I) : Module A (Zorn (B i)) := componentModule B (fun i => Zorn (B i)) i
  let C' := ∀ i, C i
  letI : IsScalarTower A C' C' :=
    ⟨fun r x y => funext fun i => smul_mul_assoc (r i) (x i) (y i)⟩
  letI : SMulCommClass A C' C' :=
    ⟨fun r x y => funext fun i => smul_comm (r i) (x i) (y i)⟩
  let Z := zornComponents B
  let E : C' →ₗ[A] (∀ i, Zorn (B i)) :=
    { toFun := fun x i => e i (x i)
      map_add' := fun x y => funext fun i => (e i).map_add (x i) (y i)
      map_smul' := fun r x => funext fun i => (e i).map_smul (r i) (x i) }
  let P : (∀ i, Zorn (B i)) →ₗ[A] C' :=
    { toFun := fun x i => p i (x i)
      map_add' := fun x y => funext fun i => (p i).map_add (x i) (y i)
      map_smul' := fun r x => funext fun i => (p i).map_smul (r i) (x i) }
  let incl := Z.symm.toLinearMap.comp E
  let proj := P.comp Z.toLinearMap
  have ep (x : C') (i : I) : Z (incl x) i = e i (x i) := by
    change Z (Z.symm (E x)) i = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have split : proj.comp incl = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext i
    change p i (Z (incl x) i) = x i
    rw [ep]
    exact LinearMap.congr_fun (h i).1 (x i)
  have hone : incl 1 = 1 := by
    apply Z.injective
    funext i
    rw [ep]
    exact (h i).2.1
  have hmul (x y : C') : incl (x * y) = incl x * incl y := by
    apply Z.injective
    funext i
    have hm (a b : Zorn A) : Z (a * b) i = Z a i * Z b i :=
      Zorn.mapCoordinates_mul (Pi.evalRingHom B i) a b
    rw [ep, hm, ep, ep]
    exact (h i).2.2.1 (x i) (y i)
  let N := (zornNorm A).comp incl
  have nn (x : C') (i : I) : N x i = n i (x i) := by
    have hn := Zorn.mapCoordinates_norm (Pi.evalRingHom B i) (incl x)
    change zornNorm (B i) (Z (incl x) i) = N x i at hn
    rw [ep] at hn
    exact hn.symm.trans ((h i).2.2.2.1 (x i))
  let projective := Module.Projective.of_split incl proj split
  letI : Module.Projective A C' := projective
  have inclLaws : embeddingLaws N incl proj :=
    ⟨split, hone, hmul, fun _ => rfl, conjugate_of_norm hone (fun _ => rfl)⟩
  obtain ⟨J, hunit, hop, hext, _, _⟩ := restrict_model inclLaws
  have np (i : I) (x y : C') : N.polarBilin x y i = (n i).polarBilin (x i) (y i) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    change N (x + y) i - N x i - N y i = _
    rw [nn, nn, nn]
    rfl
  have nt (i : I) (x : C') : trace N x i = trace (n i) (x i) := np i x 1
  have nc (i : I) (x : C') : conjugate N x i = conjugate (n i) (x i) := by
    change trace N x i • (1 : C i) - x i = trace (n i) (x i) • 1 - x i
    rw [nt]
  let w := untwisted A
  let t (i : I) := untwisted (B i)
  let F := componentCoordinates B C
  have bw (j : Fin 3) : CubicSpecification.blockWeight w j = 1 := by
    simp [CubicSpecification.blockWeight, w]
  have bw' (i : I) (j : Fin 3) : CubicSpecification.blockWeight (t i) j = 1 := by
    simp [CubicSpecification.blockWeight, t]
  have ha (i : I) (x : Coordinates A C') : F (cubicAdjoint N w x) i =
      cubicAdjoint (n i) (t i) (F x i) := by
    apply Prod.ext <;> funext j
    · change (x.1 (cyclicNext j) * x.1 (cyclicPrev j) -
          CubicSpecification.blockWeight w j * N (x.2 j)) i = _
      rw [bw, one_mul]
      change x.1 (cyclicNext j) i * x.1 (cyclicPrev j) i - N (x.2 j) i = _
      rw [nn]
      simp [CubicSpecification.cubicAdjoint, bw', F, componentCoordinates]
    · change (-(x.1 j) • x.2 j + (w j : A) •
          conjugate N (x.2 (cyclicNext j) * x.2 (cyclicPrev j))) i = _
      simp only [w, Units.val_one, one_smul]
      change -(x.1 j i) • x.2 j i +
        conjugate N (x.2 (cyclicNext j) * x.2 (cyclicPrev j)) i = _
      rw [nc]
      simp [CubicSpecification.cubicAdjoint, t, F, componentCoordinates]
      rfl
  have ht (i : I) (x y : Coordinates A C') :
      tracePairing N w x y i = tracePairing (n i) (t i) (F x i) (F y i) := by
    rw [tracePairing_apply, tracePairing_apply]
    change (Pi.evalRingHom B i) (∑ j : Fin 3, (x.1 j * y.1 j +
      CubicSpecification.blockWeight w j * N.polarBilin (x.2 j) (y.2 j))) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [bw, bw', one_mul, map_add, map_mul]
    change x.1 j i * y.1 j i + N.polarBilin (x.2 j) (y.2 j) i =
      x.1 j i * y.1 j i + (n i).polarBilin (x.2 j i) (y.2 j i)
    rw [np]
  let permute : Coordinates A C' ≃ (∀ i, Coordinates (B i) (C i)) :=
    { toFun := F
      invFun := fun x => (fun j i => (x i).1 j, fun j i => (x i).2 j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨permute.bijective, N, projective, J, hunit, nn, hop, hext, ?_, ha, ht, ?_⟩
  · intro i x
    change (Pi.evalRingHom B i) (cubicNorm N w x) = cubicNorm (n i) (t i) (F x i)
    have wp : CubicSpecification.weightProduct w = 1 := by
      simp [CubicSpecification.weightProduct, w]
    have wp' : CubicSpecification.weightProduct (t i) = 1 := by
      simp [CubicSpecification.weightProduct, t]
    simp only [CubicSpecification.cubicNorm, wp, wp', bw, bw', one_mul,
      map_add, map_sub, map_mul, map_sum]
    have hsum : (∑ j : Fin 3, (Pi.evalRingHom B i) (x.1 j) *
          (Pi.evalRingHom B i) (N (x.2 j))) =
        ∑ j : Fin 3, x.1 j i * n i (x.2 j i) := by
      apply Finset.sum_congr rfl
      intro j _
      change x.1 j i * N (x.2 j) i = _
      rw [nn]
    rw [hsum]
    change _ + trace N ((x.2 0 * x.2 1) * x.2 2) i = _
    rw [nt]
    rfl
  · intro i x y
    rw [hop]
    change F (tracePairing N w x y • x - adjointCross N w (cubicAdjoint N w x) y) i = _
    have fadd (a b : Coordinates A C') : F (a + b) i = F a i + F b i := rfl
    have fsub (a b : Coordinates A C') : F (a - b) i = F a i - F b i := rfl
    have fsmul (r : A) (z : Coordinates A C') : F (r • z) i = r i • F z i := rfl
    simp only [QuadraticOperatorSpecification.applyOperator, CubicSpecification.adjointCross,
      fadd, fsub, fsmul, ha, ht]
    rfl

theorem component_models : LowerRankSpecification.componentModelsType.{u} := by
  intro I _ B C _ _ _ _ _ n e p h
  exact construct_components B C n e p h

theorem idempotent_decomposition : LowerRankSpecification.idempotentDecompositionType.{u} := by
  intro R I _ _ a h
  let f := RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - a i})
  exact ⟨RingEquiv.ofBijective f h.bijective_pi, fun _ _ => rfl⟩

end Components

open private groundProduct_at from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticJordan

private theorem groundProduct_formula {M : Type*} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (d : Rˣ) (x y : M) :
    J.groundProduct d x y = (↑d⁻¹ : R) •
      (J.groundOp (x + y) J.unit - J.groundOp x J.unit - J.groundOp y J.unit) := by
  let l := TensorProduct.lid R M
  have h := groundProduct_at J d x y
  have eq := congrArg l h
  rw [LinearEquiv.apply_symm_apply, QuadraticJordan.linearProduct_apply, map_smul,
    Algebra.algebraMap_self, RingHom.id_apply] at eq
  rw [eq]
  congr 1
  change l (QuadraticMap.polarBilin (R := R) (N := Module.End R (R ⊗[R] M))
    (J.op R) (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) (1 ⊗ₜ[R] J.unit)) = _
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply,
    ← TensorProduct.tmul_add, map_sub]
  rfl

private theorem matrix_product {C : Type*} [NonAssocRing C] [Module R C]
    {n : QuadraticForm R C} {e : C →ₗ[R] Zorn R} {p : Zorn R →ₗ[R] C}
    (h : embeddingLaws n e p) : matrixProduct n := by
  obtain ⟨hp, h1, hm, hn, _⟩ := h
  let f : C →+* Zorn R :=
    { toFun := e
      map_one' := h1
      map_mul' := hm
      map_zero' := e.map_zero
      map_add' := e.map_add }
  have he : Function.Injective e :=
    Function.LeftInverse.injective (fun a => LinearMap.congr_fun hp a)
  let w := untwisted R
  let U := applyCubicOperator n w
  let M := assemble n w
  have F := formula_agreement h1 hm hn
  have sq (x : Coordinates R C) : M (U x cubicUnit) = M x * M x := by
    apply Matrix.map_injective he
    have op := F.2.2.2.2.1 x cubicUnit
    rw [mapBlocks_unit] at op
    calc
      (M (U x cubicUnit)).map e =
          assemble (zornNorm R) w
            (applyCubicOperator (zornNorm R) w (mapBlocks e x) cubicUnit) :=
        ((congrArg (assemble (zornNorm R) w) op).trans (F.2.2.2.2.2 _)).symm
      _ = assemble (zornNorm R) w (mapBlocks e x) *
            assemble (zornNorm R) w (mapBlocks e x) :=
        cubic_operator_matrix_square w (Zorn.isOctonion R) _
      _ = (M x * M x).map e :=
        (congrArg₂ (· * ·) (F.2.2.2.2.2 x) (F.2.2.2.2.2 x)).trans
          (Matrix.map_mul (f := f)).symm
  intro J hu hU d _ x y
  obtain ⟨a, ha⟩ := hermitian_coordinates
    (show embeddingLaws n e p from ⟨hp, h1, hm, hn, conjugate_of_norm h1 hn⟩)
  let A := (hermitian n w).subtype.comp a.toLinearMap
  have eq (z : Coordinates R C) : A z = M z := ha z
  change M (J.groundProduct d x y) = _
  rw [groundProduct_formula, hu, hU, hU, hU]
  rw [← eq, map_smul, map_sub, map_sub, eq, eq, eq, sq, sq, sq, ← eq (x + y), map_add, eq, eq]
  congr 1
  rw [add_mul, mul_add, mul_add]
  abel

theorem matrix_products : LowerRankSpecification.matrixProductsType.{u} := by
  intro R _
  obtain ⟨hs, hp, hq⟩ := embeddings R
  exact ⟨matrix_product hs, matrix_product hp, matrix_product hq,
    matrix_product (e := LinearMap.id) (p := LinearMap.id)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

private theorem perfect_dualProd (V : Type*) [AddCommGroup V] [Module R V]
    [Module.IsReflexive R V] : (QuadraticForm.dualProd R V).polarBilin.IsPerfPair := by
  let b := (QuadraticForm.dualProd R V).polarBilin
  let e : (Module.Dual R V × V) ≃ₗ[R] Module.Dual R (Module.Dual R V × V) :=
    (LinearEquiv.prodComm R (Module.Dual R V) V).trans <|
      ((Module.evalEquiv R V).prodCongr (LinearEquiv.refl R _)).trans
        (Module.dualProdDualEquivDual R _ _)
  have hh : e.toLinearMap = b := by
    apply LinearMap.ext₂
    intro x y
    change y.1 x.2 + x.1 y.2 = _
    simp [b, QuadraticMap.polar, QuadraticForm.dualProd_apply]
    abel
  refine ⟨?_, ?_⟩
  · change Function.Bijective b
    rw [← hh]
    exact e.bijective
  · have hf : b.flip = b := LinearMap.ext₂ fun _ _ => QuadraticMap.polar_comm _ _ _
    change Function.Bijective b.flip
    rw [hf, ← hh]
    exact e.bijective

private theorem perfect_hyperbolic {C : Type*} [AddCommGroup C] [Module R C]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.IsReflexive R V]
    (n : QuadraticForm R C) (f : C ≃ₗ[R] Module.Dual R V × V)
    (h : ∀ x, (QuadraticForm.dualProd R V) (f x) = n x) : n.polarBilin.IsPerfPair := by
  have he : (QuadraticForm.dualProd R V).comp f.toLinearMap = n := QuadraticMap.ext h
  rw [← he, QuadraticMap.polarBilin_comp]
  let := perfect_dualProd (R := R) V
  infer_instance

private def quaternionColumns : SplitQuaternion R ≃ₗ[R] ((Fin 2 → R) × (Fin 2 → R)) where
  toFun x := (![x 0 0, x 0 1], ![x 1 1, -x 1 0])
  invFun z := !![z.1 0, z.1 1; -z.2 1, z.2 0]
  left_inv x := by simp [← Matrix.eta_fin_two]
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_add' x y := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [add_comm]
  map_smul' r x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [smul_eq_mul]

theorem regular_trace : LowerRankSpecification.regularTraceType.{u} := by
  intro R _
  let W := Fin 1 → R
  let f : R ≃ₗ[R] W := (LinearEquiv.piUnique R (fun _ : Fin 1 => R)).symm
  have hp : (pairNorm R).polarBilin.IsPerfPair := by
    apply perfect_hyperbolic _ ((f.trans (dotProductEquiv R (Fin 1))).prodCongr f)
    rintro ⟨a, b⟩
    change (dotProductEquiv R (Fin 1) (f a)) (f b) = a * b
    simp [dotProductEquiv, dotProduct, f]
    rfl
  have hq : (quaternionNorm R).polarBilin.IsPerfPair := by
    apply perfect_hyperbolic _ (quaternionColumns.trans
      ((dotProductEquiv R (Fin 2)).prodCongr (LinearEquiv.refl R _)))
    intro x
    rw [matrix_norm, Matrix.det_fin_two]
    change (dotProductEquiv R (Fin 2) ![x 0 0, x 0 1]) ![x 1 1, -x 1 0] = _
    simp [dotProductEquiv, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]
  exact ⟨hp, hq, tracePairing_perfect _ hp, tracePairing_perfect _ hq,
    tracePairing_perfect _ (Zorn.perfect R)⟩

end

end LinearAlgebraicGroups.Albert.LowerRank
