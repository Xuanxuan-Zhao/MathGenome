import Specs.LinearAlgebraicGroups.Albert.Triality
import LinearAlgebraicGroups.Albert.SplitSpin
import LinearAlgebraicGroups.Albert.FrameParameters
import LinearAlgebraicGroups.Albert.IntrinsicCubic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.Triality

open CliffordAlgebra Module TrialitySpecification
open _root_.LinearAlgebraicGroups.Composition
open Composition.Zorn (norm first second)
open HermitianSpecification CubicSpecification FrameSpecification QuadraticOperatorSpecification
open scoped BigOperators TensorProduct
open private map_isometry_evenOdd map_isometry_reverse from LinearAlgebraicGroups.Albert.SplitSpin

set_option linter.style.haveILetI false

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]

local notation "C" => Zorn R
local notation "n" => norm R
local notation "B" => QuadraticMap.polarBilin (norm R)
local notation "bar" => Composition.conjugate (norm R)

private abbrev laws := (Zorn.isOctonion R).toNormLaws

private theorem polar_eq (f : C ≃ₗ[R] C) (multiplier : R) (hf : ∀ x, n (f x) = multiplier * n x)
    (x y : C) : B (f x) (f y) = multiplier * B x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hf, mul_sub]

private theorem polar_iso (f : C ≃ₗ[R] C) (hf : ∀ x, n (f x) = n x)
    (x y : C) : B (f x) (f y) = B x y := by
  simpa using polar_eq f 1 (by simpa using hf) x y

private theorem eq_of_polar_left {x y : C} (h : ∀ z, B x z = B y z) : x = y :=
  (Zorn.perfect R).bijective_left.1 (LinearMap.ext h)

private theorem eq_of_polar_right {x y : C} (h : ∀ z, B z x = B z y) : x = y :=
  (Zorn.perfect R).bijective_right.1 (LinearMap.ext h)

private def conjugation : C ≃ₗ[R] C :=
  LinearEquiv.ofInvolutive bar (conjugate_involutive (laws (R := R)))

@[simp] private theorem conjugation_apply (x : C) : conjugation x = bar x := rfl

private theorem norm_conj (x : C) : n (bar x) = n x :=
  norm_conjugate laws x

private theorem conj_conj (x : C) : bar (bar x) = x :=
  conjugate_involutive laws x

private theorem paired_trace (a b c : C) : B (bar (a * b)) c = compositionTrace n ((a * b) * c) := by
  rw [compositionTrace_mul_as_polar laws]
  have h := polar_iso conjugation norm_conj (a * b) (bar c)
  simpa only [conjugation_apply, conj_conj] using h

private theorem cyclic_of_first (h : Triple R) (hn : ∀ i x, n (h i x) = n x)
    (h₀ : ∀ a b, h 0 (bar (a * b)) = bar (h 1 a * h 2 b)) : IsRelated h := by
  let t (a b c : C) := compositionTrace n ((a * b) * c)
  have rot (a b c : C) : t a b c = t b c a := compositionTrace_mul_cyclic laws a b c
  have inv (a b c : C) : t (h 1 a) (h 2 b) (h 0 c) = t a b c := by
    simpa only [h₀, paired_trace, t] using polar_iso (h 0) (hn 0) (bar (a * b)) c
  have recover (i : Fin 3) (a b : C)
      (hi : ∀ c, t (h (cyclicNext i) a) (h (cyclicPrev i) b) (h i c) = t a b c) :
      h i (bar (a * b)) = bar (h (cyclicNext i) a * h (cyclicPrev i) b) := by
    apply eq_of_polar_left
    intro z
    obtain ⟨c, rfl⟩ := (h i).surjective z
    rw [polar_iso _ (hn i), paired_trace, paired_trace]
    exact (hi c).symm
  refine ⟨hn, fun i => ?_⟩
  fin_cases i
  · exact h₀
  · intro a b
    apply recover 1 a b
    intro c
    change t (h 2 a) (h 0 b) (h 1 c) = t a b c
    exact (rot _ _ _).symm.trans ((inv c a b).trans (rot _ _ _))
  · intro a b
    apply recover 2 a b
    intro c
    change t (h 0 a) (h 1 b) (h 2 c) = t a b c
    exact (rot _ _ _).trans ((inv b c a).trans (rot _ _ _).symm)

section Frame

private abbrev oneWeights (R : Type u) [CommRing R] : Fin 3 → Rˣ := fun _ => 1

private def blockwise (h : Triple R) : Model R ≃ₗ[R] Model R :=
  (LinearEquiv.refl R (Fin 3 → R)).prodCongr (LinearEquiv.piCongrRight h)

@[simp] private theorem blockwise_apply (h : Triple R) (x : Model R) :
    blockwise h x = (x.1, fun i => h i (x.2 i)) := rfl

private theorem blockwise_frame (h : Triple R) (i : Fin 3) :
    blockwise h (FrameSpecification.frameAxis i) = FrameSpecification.frameAxis i := by
  refine Prod.ext rfl ?_
  funext j
  exact (h j).map_zero

private theorem blockwise_adjoint (h : Triple R) (hh : IsRelated h) (x : Model R) :
    blockwise h (CubicSpecification.cubicAdjoint n (oneWeights R) x) =
      CubicSpecification.cubicAdjoint n (oneWeights R) (blockwise h x) := by
  apply Prod.ext <;> funext i
  · simp [CubicSpecification.cubicAdjoint, hh.1]
  · simp [CubicSpecification.cubicAdjoint, oneWeights, hh.2]

private theorem blockwise_pairing (h : Triple R) (hh : IsRelated h) (x y : Model R) :
    CubicSpecification.tracePairing n (oneWeights R) (blockwise h x) (blockwise h y) =
      CubicSpecification.tracePairing n (oneWeights R) x y := by
  change (∑ i, (x.1 i * y.1 i + CubicSpecification.blockWeight (oneWeights R) i *
      B (h i (x.2 i)) (h i (y.2 i)))) = _
  simp only [polar_iso _ (hh.1 _)]
  rfl

private theorem blockwise_fixes (h : Triple R) (hh : IsRelated h) : FixesFrame (blockwise h) := by
  refine ⟨blockwise_frame h, ?_⟩
  intro x y
  change blockwise h (applyOperator n (oneWeights R) x y) =
    applyOperator n (oneWeights R) (blockwise h x) (blockwise h y)
  simp only [applyOperator, CubicSpecification.adjointCross, map_sub, map_add, map_smul, blockwise_adjoint h hh,
    blockwise_pairing h hh]

private theorem frame_projects (g : Model R ≃ₗ[R] Model R) (hg : FixesFrame g)
    (x : Model R) (i : Fin 3) :
    g (CubicSpecification.singleBlockCoordinates i (x.2 i)) = CubicSpecification.singleBlockCoordinates i ((g x).2 i) := by
  let T := triple n (oneWeights R)
  have hT := (hermitian_frame n (oneWeights R)).2.2.2.1 i
  rw [← hT x, ← hT (g x)]
  change g (T (FrameSpecification.frameAxis (cyclicNext i)) x (FrameSpecification.frameAxis (cyclicPrev i))) =
    T (FrameSpecification.frameAxis (cyclicNext i)) (g x) (FrameSpecification.frameAxis (cyclicPrev i))
  simp only [T, triple, map_sub, hg.2, map_add, hg.1]

private theorem frame_diagonal (g : Model R ≃ₗ[R] Model R) (hg : FixesFrame g)
    (x : Model R) (i : Fin 3) : (g x).1 i = x.1 i := by
  have hp := (hermitian_frame n (oneWeights R)).2.2.1 i
  have h := hg.2 (FrameSpecification.frameAxis i) x
  change g (applyOperator n (oneWeights R) (FrameSpecification.frameAxis i) x) =
    applyOperator n (oneWeights R) (g (FrameSpecification.frameAxis i)) (g x) at h
  rw [hg.1, hp, hp, map_smul, hg.1] at h
  simpa [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates] using (congrArg (fun z : Model R => z.1 i) h).symm

private def blockMap (g : Model R ≃ₗ[R] Model R) (i : Fin 3) : C →ₗ[R] C :=
  ((LinearMap.proj i).comp (LinearMap.snd R _ _)).comp
    (g.toLinearMap.comp ((0 : C →ₗ[R] (Fin 3 → R)).prod (LinearMap.single R (fun _ : Fin 3 => C) i)))

private theorem blockMap_apply (g : Model R ≃ₗ[R] Model R) (i : Fin 3) (x : C) :
    blockMap g i x = (g (CubicSpecification.singleBlockCoordinates i x)).2 i := rfl

private theorem blockMap_spec (g : Model R ≃ₗ[R] Model R) (hg : FixesFrame g)
    (i : Fin 3) (x : Model R) :
    blockMap g i (x.2 i) = (g x).2 i := by
  simpa [blockMap_apply, CubicSpecification.singleBlockCoordinates] using
    congrArg (fun z : Model R => z.2 i) (frame_projects g hg x i)

private def frameBlocks (g : frameStabilizer (R := R)) : Triple R := fun i =>
  { blockMap g.val i with
    invFun := blockMap (g⁻¹).val i
    left_inv := fun x => by
      change blockMap (g⁻¹).val i (blockMap g.val i x) = x
      rw [blockMap_apply g.val, blockMap_spec _ (g⁻¹).property]
      simp [CubicSpecification.singleBlockCoordinates]
    right_inv := fun x => by
      change blockMap g.val i (blockMap (g⁻¹).val i x) = x
      rw [blockMap_apply (g⁻¹).val, blockMap_spec _ g.property]
      simp [CubicSpecification.singleBlockCoordinates] }

private theorem blockwise_frameBlocks (g : frameStabilizer (R := R)) :
    blockwise (frameBlocks g) = g.val := by
  apply LinearEquiv.ext
  intro x
  exact Prod.ext (funext fun i => (frame_diagonal _ g.property x i).symm)
    (funext fun i => blockMap_spec _ g.property i x)

private theorem blockwise_injective : Function.Injective (blockwise (R := R)) := by
  intro h k he
  funext i
  ext x
  simpa [CubicSpecification.singleBlockCoordinates] using
    congrArg (fun f : Model R ≃ₗ[R] Model R => (f (CubicSpecification.singleBlockCoordinates i x)).2 i) he

private theorem frameBlocks_related (g : frameStabilizer (R := R)) :
    IsRelated (frameBlocks g) := by
  let h := frameBlocks g
  let U := applyOperator n (oneWeights R)
  let A := CubicSpecification.cubicAdjoint n (oneWeights R)
  let t := CubicSpecification.linearTrace n (oneWeights R)
  let S := CubicSpecification.quadraticTrace n (oneWeights R)
  have hs : ∀ x : Model R, U x CubicSpecification.cubicUnit = A x + t x • x - S x • CubicSpecification.cubicUnit :=
    (cubic_operator_identities (oneWeights R) (Zorn.isOctonion R)).2.2.2.2.2.2.2.2.1
  have hu : g.val (CubicSpecification.cubicUnit : Model R) = CubicSpecification.cubicUnit := by
    rw [← blockwise_frameBlocks g]
    simp [CubicSpecification.cubicUnit, Pi.zero_def]
  have sq (x : Model R) : g.val (U x CubicSpecification.cubicUnit) = U (g.val x) CubicSpecification.cubicUnit := by
    rw [show g.val (U x CubicSpecification.cubicUnit) = U (g.val x) (g.val CubicSpecification.cubicUnit) from g.property.2 x CubicSpecification.cubicUnit, hu]
  have sq' (x : Model R) : blockwise h (U x CubicSpecification.cubicUnit) = U (blockwise h x) CubicSpecification.cubicUnit := by
    simpa only [h, blockwise_frameBlocks] using sq x
  constructor
  · intro i x
    let j := cyclicNext i
    have hj : j ≠ i := by
      dsimp [j]
      revert i
      decide
    have hsq := congrArg (fun z : Model R => z.1 j) (sq' (CubicSpecification.singleBlockCoordinates i x))
    simp only [hs, blockwise_apply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsq
    have hblock (y : C) : blockwise h (CubicSpecification.singleBlockCoordinates i y) =
        CubicSpecification.singleBlockCoordinates i (h i y) := by
      refine Prod.ext rfl ?_
      funext k
      by_cases hk : k = i
      · subst k
        simp [CubicSpecification.singleBlockCoordinates]
      · simp [CubicSpecification.singleBlockCoordinates, Pi.single_eq_of_ne hk]
    change _ = (A (blockwise h (CubicSpecification.singleBlockCoordinates i x))).1 j +
      t (blockwise h (CubicSpecification.singleBlockCoordinates i x)) * 0 -
      S (blockwise h (CubicSpecification.singleBlockCoordinates i x)) * 1 at hsq
    rw [hblock] at hsq
    have hsingle : CubicSpecification.singleBlockFormulas n (oneWeights R) :=
      cubic_single_block_formulas (oneWeights R)
    have hd (y : C) : A (CubicSpecification.singleBlockCoordinates i y) =
        CubicSpecification.diagonalCoordinates (Pi.single i (-n y)) := by
      simpa [A, CubicSpecification.blockWeight, oneWeights] using
        (hsingle i y).2.1
    have ht (y : C) : t (A (CubicSpecification.singleBlockCoordinates i y)) = -n y := by
      rw [hd]
      change CubicSpecification.linearTrace n (oneWeights R) _ = _
      rw [linearTrace_apply]
      simp [CubicSpecification.diagonalCoordinates]
    have hS (y : C) : S (CubicSpecification.singleBlockCoordinates i y) = -n y := ht y
    change (A (CubicSpecification.singleBlockCoordinates i x)).1 j +
        t (CubicSpecification.singleBlockCoordinates i x) * 0 -
        S (CubicSpecification.singleBlockCoordinates i x) * 1 = _ at hsq
    rw [hS, hS, hd, hd] at hsq
    simpa [CubicSpecification.singleBlockCoordinates, CubicSpecification.diagonalCoordinates,
      Pi.single_eq_of_ne hj] using hsq.symm
  · intro i a b
    let j := cyclicNext i
    let k := cyclicPrev i
    let x : Model R := (0, Pi.single j a + Pi.single k b)
    have hjk : j ≠ k := by
      dsimp [j, k]
      revert i
      decide
    have hsq := congrArg (fun z : Model R => z.2 i) (sq' x)
    change h i ((U x CubicSpecification.cubicUnit).2 i) =
      (U (blockwise h x) CubicSpecification.cubicUnit).2 i at hsq
    rw [hs, hs] at hsq
    have hx (y : Model R) (hy : y.1 = 0) : t y = 0 := by
      change CubicSpecification.linearTrace n (oneWeights R) y = 0
      rw [linearTrace_apply, hy]
      simp
    rw [hx x rfl, hx (blockwise h x) rfl] at hsq
    simpa [A, CubicSpecification.cubicAdjoint, oneWeights, x, j, k, Pi.single_eq_of_ne hjk,
      Pi.single_eq_of_ne hjk.symm, CubicSpecification.cubicUnit, Pi.zero_def] using hsq

theorem frameTriality : FrameTriality.{u} := by
  intro R _
  let f : relatedTriples (R := R) →* frameStabilizer (R := R) :=
    { toFun := fun h => ⟨blockwise h.val, blockwise_fixes h.val h.property⟩
      map_one' := Subtype.ext (LinearEquiv.ext fun _ => rfl)
      map_mul' := fun _ _ => Subtype.ext (LinearEquiv.ext fun _ => rfl) }
  have hf : Function.Bijective f := by
    refine ⟨fun h k he => Subtype.ext (blockwise_injective (congrArg Subtype.val he)), ?_⟩
    intro g
    exact ⟨⟨frameBlocks g, frameBlocks_related g⟩, Subtype.ext (blockwise_frameBlocks g)⟩
  exact ⟨MulEquiv.ofBijective f hf, fun _ _ => rfl⟩

theorem frameLaw : FrameLaw.{u} := by
  intro R _ J hunit hop g
  rw [SplitSpecification.ParaQuadratic.isIso_iff_ground]
  constructor
  · rintro ⟨hf, hu⟩
    refine ⟨hf, ?_, fun x y => ?_⟩
    · rw [hunit, ← (hermitian_frame (norm R) (oneWeights R)).1, map_sum]
      simp [hf]
    · simpa only [hop] using hu x y
  · rintro ⟨hf, -, hU⟩
    exact ⟨hf, fun x y => by simpa only [hop] using hU x y⟩

theorem cubicFrameStabilizer : CubicFrameStabilizer.{u} := by
  intro R _
  obtain ⟨J, hunit, hground, -, -⟩ :=
    weighted_hermitian_quadratic_jordan (oneWeights R) (Zorn.isOctonion R)
  let K := SplitSpecification.ParaQuadratic.ofJordan J
  have hc : SplitSpecification.OnComponent K R .octonion := by
    refine ⟨TensorProduct.lid R (Model R), ?_, ?_⟩
    · simpa [K, SplitSpecification.ParaQuadratic.ofJordan] using hunit
    · intro x y
      obtain ⟨x, rfl⟩ := (TensorProduct.lid R (Model R)).symm.surjective x
      obtain ⟨y, rfl⟩ := (TensorProduct.lid R (Model R)).symm.surjective y
      simp only [TensorProduct.lid_symm_apply, K.groundOp_lift, TensorProduct.lid_tmul, one_smul]
      change J.groundOp x y = applyOperator (norm R) (oneWeights R) x y
      exact hground x y
  have hK : SplitSpecification.IsAlbert K :=
    (SplitSpecification.albert_iff_split_octonion_after_cover K).mpr
      ⟨R, inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨hF, agrees⟩ := intrinsic_coefficients K hK
  obtain ⟨F, hF, -⟩ := hF
  refine ⟨J, F, hunit, hground, hK, hF, agrees F hF, fun g => ?_⟩
  rw [← intrinsic_norm_automorphisms K F hK hF g]
  exact frameLaw R K hunit hground g

end Frame

section Clifford

private abbrev paired : LinearMap.BilinForm R (C × C) :=
  CliffordSpecification.octonionPairing

private theorem paired_apply (x y : C × C) : paired x y = B x.1 y.1 + B x.2 y.2 := rfl

private theorem paired_right_injective {x y : C × C}
    (h : ∀ z, paired z x = paired z y) : x = y := by
  apply Prod.ext
  · apply eq_of_polar_right
    intro z
    simpa [paired_apply] using h (z, 0)
  · apply eq_of_polar_right
    intro z
    simpa [paired_apply] using h (0, z)

private theorem action_apply (c : C) (x : C × C) :
    CliffordSpecification.octonionOperator c x = (c * x.2, bar c * x.1) := rfl

variable (e : CliffordAlgebra (norm R) ≃ₐ[R] Module.End R (Zorn R × Zorn R))
  (he : ∀ c : Zorn R, e (ι (norm R) c) = CliffordSpecification.octonionOperator c)

include e he in
private theorem clifford_vector_injective : Function.Injective (ι n) := by
  intro c d h
  have h' := congrArg (fun a : CliffordAlgebra n => (e a (0, 1)).1) h
  simpa only [he, action_apply, mul_one] using h'

include e in
private theorem clifford_scalar_injective :
    Function.Injective (algebraMap R (CliffordAlgebra n)) := by
  intro r s h
  have h' := congrArg (fun a : CliffordAlgebra n =>
    (Zorn.coordinates R ((e a (1, 0)).1)).1) h
  change (Zorn.coordinates R (e (algebraMap R _ r) (1, 0)).1).1 =
    (Zorn.coordinates R (e (algebraMap R _ s) (1, 0)).1).1 at h'
  rw [AlgEquiv.commutes, AlgEquiv.commutes] at h'
  change r * (1 : R) = s * 1 at h'
  simpa using h'

private theorem spin_normalizes (s : CliffordUnits R) (g : C ≃ₗ[R] C)
    (h : ∀ x, (s : CliffordAlgebra n) * ι n x = ι n (g x) * s) :
    (fun x : CliffordAlgebra n => s * x * ↑s⁻¹) '' LinearMap.range (ι n) =
      LinearMap.range (ι n) := by
  have hv (x : C) : (s : CliffordAlgebra n) * ι n x * ↑s⁻¹ = ι n (g x) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨g x, (hv x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨ι n (g.symm x), ⟨g.symm x, rfl⟩, (hv (g.symm x)).trans (congrArg (ι n) (g.apply_symm_apply x))⟩

include e he in
private theorem exists_vector_equiv (s : CliffordUnits R)
    (hs : (fun x : CliffordAlgebra n => s * x * ↑s⁻¹) '' LinearMap.range (ι n) =
      LinearMap.range (ι n)) :
    ∃ g : C ≃ₗ[R] C, ∀ x, (s : CliffordAlgebra n) * ι n x = ι n (g x) * s := by
  let P : CliffordAlgebra n →ₗ[R] C := (LinearMap.fst R C C).comp
    ((LinearMap.applyₗ (R := R) (M := C × C) (M₂ := C × C) (0, 1)).comp e.toLinearEquiv.toLinearMap)
  have hp (x : C) : P (ι n x) = x := by
    change (e (ι n x) (0, 1)).1 = _
    rw [he, action_apply, mul_one]
  let F : Module.End R C :=
    P.comp (((LinearMap.mulRight R (↑s⁻¹ : CliffordAlgebra n)).comp
      (Algebra.lmul R _ (s : CliffordAlgebra n))).comp (ι n))
  have hF (x : C) : ι n (F x) = (s : CliffordAlgebra n) * ι n x * ↑s⁻¹ := by
    obtain ⟨y, hy⟩ : (s : CliffordAlgebra n) * ι n x * ↑s⁻¹ ∈ LinearMap.range (ι n) := by
      change _ ∈ (↑(LinearMap.range (ι n)) : Set (CliffordAlgebra n))
      rw [← hs]
      exact ⟨ι n x, ⟨x, rfl⟩, rfl⟩
    change ι n (P ((s : CliffordAlgebra n) * ι n x * ↑s⁻¹)) = _
    rw [← hy, hp]
  have hb : Function.Bijective F := by
    constructor
    · intro x y hxy
      apply clifford_vector_injective e he
      have h := congrArg (ι n) hxy
      simp only [hF] at h
      have hh := congrArg (fun z : CliffordAlgebra n => (↑s⁻¹ : CliffordAlgebra n) * z * s) h
      simpa [mul_assoc, ← mul_assoc (↑s⁻¹ : CliffordAlgebra n) (s : CliffordAlgebra n)] using hh
    · intro y
      have hy : ι n y ∈ (↑(LinearMap.range (ι n)) : Set (CliffordAlgebra n)) := ⟨y, rfl⟩
      rw [← hs] at hy
      obtain ⟨z, ⟨x, rfl⟩, hx⟩ := hy
      exact ⟨x, clifford_vector_injective e he ((hF x).trans hx)⟩
  refine ⟨LinearEquiv.ofBijective F hb, fun x => ?_⟩
  change _ = ι n (F x) * s
  rw [hF, mul_assoc ((s : CliffordAlgebra n) * ι n x), Units.inv_mul, mul_one]

include e in
private theorem vector_norm (s : CliffordUnits R) (g : C ≃ₗ[R] C)
    (h : ∀ x, (s : CliffordAlgebra n) * ι n x = ι n (g x) * s) (x : C) :
    n (g x) = n x := by
  apply clifford_scalar_injective e
  have hh : (s : CliffordAlgebra n) * (ι n x * ι n x) = (ι n (g x) * ι n (g x)) * s := by
    rw [← mul_assoc, h, mul_assoc, h, ← mul_assoc]
  rw [ι_sq_scalar, ι_sq_scalar, Algebra.commutes] at hh
  apply_fun (fun z : CliffordAlgebra n => z * (↑s⁻¹ : CliffordAlgebra n)) at hh
  simpa [mul_assoc] using hh.symm

private theorem block_intertwining (p g q : C ≃ₗ[R] C)
    (hp : ∀ x, n (p x) = n x) (hq : ∀ x, n (q x) = n x)
    (h : ∀ c x, p (c * x) = g c * q x) (c x : C) :
    q (bar c * x) = bar (g c) * p x := by
  apply eq_of_polar_left
  intro y
  obtain ⟨y, rfl⟩ := q.surjective y
  calc
    B (q (bar c * x)) (q y) = B (bar c * x) y := polar_iso q hq _ _
    _ = B x (c * y) := by
      have had := left_mul_adjoint laws (bar c) x y
      change B (bar c * x) y = B x (bar (bar c) * y) at had
      simpa only [conj_conj] using had
    _ = B (p x) (p (c * y)) := (polar_iso p hp _ _).symm
    _ = B (p x) (g c * q y) := by rw [h]
    _ = B (bar (g c) * p x) (q y) := by
      have had := left_mul_adjoint laws (bar (g c)) (p x) (q y)
      change B (bar (g c) * p x) (q y) = B (p x) (bar (bar (g c)) * q y) at had
      simpa only [conj_conj] using had.symm

include e he in
private theorem spin_of_related
    (heven : ∀ a, a ∈ evenOdd n 0 ↔
      (∀ x, (e a (x, 0)).2 = 0) ∧ (∀ y, (e a (0, y)).1 = 0))
    (hadj : ∀ a, LinearMap.IsAdjointPair paired paired (e a) (e (reverse a)))
    (h : relatedTriples (R := R)) :
    ∃ s : CliffordUnits R, IsSpin s ∧ Corresponds e h s := by
  let p := (conjugation.trans (h.val 0)).trans conjugation
  let q := h.val 2
  let U := LinearMap.GeneralLinearGroup.ofLinearEquiv (p.prodCongr q)
  let s : CliffordUnits R := Units.map e.symm.toMonoidHom U
  have hs (x y : C) : e s (x, y) = (p x, q y) := by
    change e (e.symm (U : Module.End R (C × C))) (x, y) = _
    rw [e.apply_symm_apply]
    rfl
  have hp (x : C) : n (p x) = n x := by
    change n (bar (h.val 0 (bar x))) = _
    rw [norm_conj, h.property.1, norm_conj]
  have hq : ∀ x, n (q x) = n x := h.property.1 2
  have htop (c x : C) : p (c * x) = h.val 1 c * q x := by
    have h₀ := h.property.2 0 c x
    change h.val 0 (bar (c * x)) = bar (h.val 1 c * q x) at h₀
    change bar (h.val 0 (bar (c * x))) = _
    rw [h₀, conj_conj]
  have hv (c : C) : (s : CliffordAlgebra n) * ι n c = ι n (h.val 1 c) * s := by
    apply e.injective
    rw [map_mul, map_mul, he, he]
    apply LinearMap.ext
    rintro ⟨x, y⟩
    change e s (CliffordSpecification.octonionOperator c (x, y)) =
      CliffordSpecification.octonionOperator (h.val 1 c) (e s (x, y))
    rw [action_apply, hs, hs, action_apply]
    exact Prod.ext (htop c y) (block_intertwining p (h.val 1) q hp hq htop c x)
  have hpolar (x y : C × C) : paired (e s x) (e s y) = paired x y := by
    rcases x with ⟨x, x'⟩
    rcases y with ⟨y, y'⟩
    simp only [hs, paired_apply, polar_iso _ hp, polar_iso _ hq]
  have hrev : reverse (s : CliffordAlgebra n) * s = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    apply LinearMap.ext
    intro x
    apply paired_right_injective
    intro y
    change paired y (e (reverse (s : CliffordAlgebra n)) (e s x)) = paired y x
    rw [← hadj (s : CliffordAlgebra n) y (e s x), hpolar]
  refine ⟨s, ⟨(heven _).mpr ⟨fun x => ?_, fun y => ?_⟩, hrev,
    spin_normalizes s (h.val 1) hv⟩, ⟨hs, hv⟩⟩
  · rw [hs, map_zero]
  · rw [hs, map_zero]

include e he in
private theorem related_of_spin
    (heven : ∀ a, a ∈ evenOdd n 0 ↔
      (∀ x, (e a (x, 0)).2 = 0) ∧ (∀ y, (e a (0, y)).1 = 0))
    (hadj : ∀ a, LinearMap.IsAdjointPair paired paired (e a) (e (reverse a)))
    (s : CliffordUnits R) (hs : IsSpin s) :
    ∃ h : relatedTriples (R := R), Corresponds e h s := by
  obtain ⟨g, hg⟩ := exists_vector_equiv e he s hs.2.2
  have hgn := vector_norm e s g hg
  have hr : reverse (s : CliffordAlgebra n) = ↑s⁻¹ := by
    have hh := congrArg (fun z : CliffordAlgebra n => z * (↑s⁻¹ : CliffordAlgebra n)) hs.2.1
    simpa [mul_assoc] using hh
  have hi : (↑s⁻¹ : CliffordAlgebra n) ∈ evenOdd n 0 :=
    hr ▸ ((reverse_mem_evenOdd_iff (Q := n)).mpr hs.1)
  let D (a : CliffordAlgebra n) : C →ₗ[R] C :=
    (LinearMap.fst R C C).comp ((e a).comp (LinearMap.inl R C C))
  let E (a : CliffordAlgebra n) : C →ₗ[R] C :=
    (LinearMap.snd R C C).comp ((e a).comp (LinearMap.inr R C C))
  have hdiag (a : CliffordAlgebra n) (ha : a ∈ evenOdd n 0) (x y : C) :
      e a (x, y) = (D a x, E a y) := by
    obtain ⟨h₁, h₂⟩ := (heven a).mp ha
    rw [show (x, y) = (x, 0) + (0, y) by simp, map_add]
    exact Prod.ext (by change (e a (x, 0)).1 + (e a (0, y)).1 = _; rw [h₂, add_zero]; rfl)
      (by change (e a (x, 0)).2 + (e a (0, y)).2 = _; rw [h₁, zero_add]; rfl)
  have hleft (x y : C) :
      e (↑s⁻¹ : CliffordAlgebra n) (e s (x, y)) = (x, y) := by
    change (e (↑s⁻¹ : CliffordAlgebra n) * e (s : CliffordAlgebra n)) (x, y) = _
    rw [← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
  have hright (x y : C) :
      e s (e (↑s⁻¹ : CliffordAlgebra n) (x, y)) = (x, y) := by
    change (e (s : CliffordAlgebra n) * e (↑s⁻¹ : CliffordAlgebra n)) (x, y) = _
    rw [← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
  have hleft' := hleft
  have hright' := hright
  simp only [hdiag _ hs.1, hdiag _ hi] at hleft' hright'
  let p : C ≃ₗ[R] C :=
    { D s with
      invFun := D (↑s⁻¹)
      left_inv := fun x => congrArg Prod.fst (hleft' x 0)
      right_inv := fun x => congrArg Prod.fst (hright' x 0) }
  let q : C ≃ₗ[R] C :=
    { E s with
      invFun := E (↑s⁻¹)
      left_inv := fun y => congrArg Prod.snd (hleft' 0 y)
      right_inv := fun y => congrArg Prod.snd (hright' 0 y) }
  have hd (x y : C) : e s (x, y) = (p x, q y) := hdiag _ hs.1 x y
  have htop (c y : C) : p (c * y) = g c * q y := by
    have h := congrArg (fun a : CliffordAlgebra n => (e a (0, y)).1) (hg c)
    simp only [map_mul, Module.End.mul_apply, he, action_apply, hd, mul_zero] at h
    exact h
  have hqp (y : C) : n (p y) = n (q y) := by
    simpa only [one_mul, Zorn.norm_mul, hgn, Zorn.norm_one] using congrArg n (htop 1 y)
  let multiplier := n (q 1)
  have hp (x : C) : n (p x) = multiplier * n x := by
    simpa only [mul_one, Zorn.norm_mul, hgn, multiplier, mul_comm (n x) (n (q 1))] using congrArg n (htop x 1)
  have hpolar (x y : C) : B (p x) (p y) = B x y := by
    have hh := hadj (s : CliffordAlgebra n) (x, 0) (e s (y, 0))
    rw [hr, hleft] at hh
    simpa only [hd, map_zero, paired_apply, LinearMap.zero_apply, map_zero, add_zero] using hh
  -- The complementary Zorn idempotents detect the common multiplier over every ring.
  have hunit : B (first R) (second R) = 1 := by
    rw [show first R = Zorn.ofCoordinates (1, 0, 0, 0) from rfl,
      show second R = Zorn.ofCoordinates (0, 0, 0, 1) from rfl, Zorn.polar_formula]
    simp
  have hmultiplier : multiplier = 1 := by
    have hh := polar_eq p multiplier hp (first R) (second R)
    rw [hpolar, hunit, mul_one] at hh
    exact hh.symm
  have hpn (x : C) : n (p x) = n x := by simpa [hmultiplier] using hp x
  let h₁ := (conjugation.trans p).trans conjugation
  let h : Triple R := ![h₁, g, q]
  have hn : ∀ i x, n (h i x) = n x := by
    intro i x
    fin_cases i
    · change n (bar (p (bar x))) = n x
      rw [norm_conj, hpn, norm_conj]
    · exact hgn x
    · exact (hqp x).symm.trans (hpn x)
  have h₀ (c y : C) : h 0 (bar (c * y)) = bar (h 1 c * h 2 y) := by
    change bar (p (bar (bar (c * y)))) = bar (g c * q y)
    rw [conj_conj, htop]
  refine ⟨⟨h, cyclic_of_first h hn h₀⟩, ⟨fun x y => ?_, hg⟩⟩
  change e s (x, y) = (bar (bar (p (bar (bar x)))), q y)
  rw [conj_conj, conj_conj, hd]

theorem cliffordTriality : CliffordTriality.{u} := by
  intro R _ e he heven hadj
  constructor
  · intro h
    obtain ⟨s, hs, hc⟩ := spin_of_related e he heven hadj h
    refine ⟨s, ⟨hs, hc⟩, fun t ht => ?_⟩
    apply Units.ext
    apply e.injective
    exact LinearMap.ext fun ⟨x, y⟩ => (ht.2.1 x y).trans (hc.1 x y).symm
  · intro s hs
    obtain ⟨h, hh⟩ := related_of_spin e he heven hadj s hs
    refine ⟨h, hh, fun k hk => ?_⟩
    apply Subtype.ext
    funext i
    apply LinearEquiv.ext
    intro x
    fin_cases i
    · apply (conjugate_involutive (laws (R := R))).injective
      have heq := congrArg Prod.fst ((hk.1 (Composition.conjugate (norm R) x) 0).symm.trans
        (hh.1 (Composition.conjugate (norm R) x) 0))
      change Composition.conjugate (norm R) (k.val 0 x) = Composition.conjugate (norm R) (h.val 0 x)
      simpa only [conj_conj] using heq
    · apply clifford_vector_injective e he
      have heq := (hk.2 x).symm.trans (hh.2 x)
      exact (Units.mulRight s).injective heq
    · exact congrArg Prod.snd ((hk.1 0 x).symm.trans (hh.1 0 x))

end Clifford

section HalfSpin

open private occupation matchingOccupation wedgeProjector wedgeProjector_apply
  contract hyperbolicOperator_apply octonionBlock octonionBlock_zero octonionBlock_one
  octonionOperator_grade graded_action from LinearAlgebraicGroups.Albert.CliffordModel

theorem halfSpinBlocks : HalfSpinBlocks.{u} := by
  intro R _ e he
  have heq : e = CliffordModel.octonionEquiv := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro c
    exact (he c).trans (CliffordModel.octonionEquiv_ι c).symm
  subst e
  classical
  let I := Option (Fin 3)
  letI : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  let E := I → R
  let q := QuadraticForm.dualProd R E
  let W := ExteriorAlgebra R E
  let b := Pi.basisFun R I
  let d := Zorn.hyperbolicIsometry R
  let a := CliffordModel.octonionEquiv (R := R)
  let bCl := CliffordModel.hyperbolicEquiv b
  let A : Module.End R W ≃ₐ[R] Module.End R (Zorn R × Zorn R) :=
    bCl.symm.trans ((equivOfIsometry d).symm.trans a)
  -- This vector is killed by every contraction.
  let vac : Zorn R × Zorn R := (first R, 0)
  let coord := b.ExteriorAlgebra.coord (∅ : Finset I)
  let rankOne (x : W) : Module.End R W := (LinearMap.toSpanSingleton R _ x).comp coord
  have hRank (T : Module.End R W) (x : W) : T * rankOne x = rankOne (T x) := by
    apply LinearMap.ext
    intro y
    exact T.map_smul (coord y) x
  let F : W →ₗ[R] Zorn R × Zorn R :=
    { toFun := fun x => A (rankOne x) vac
      map_add' := fun x y => by
        rw [show rankOne (x + y) = rankOne x + rankOne y by
          apply LinearMap.ext; intro z; exact smul_add (coord z) x y, map_add]
        rfl
      map_smul' := fun r x => by
        rw [show rankOne (r • x) = r • rankOne x by
          apply LinearMap.ext; intro z; exact smul_comm (coord z) r x, map_smul]
        rfl }
  have hF (T : Module.End R W) (x : W) : F (T x) = A T (F x) := by
    change A (rankOne (T x)) vac = A T (A (rankOne x) vac)
    rw [← hRank T x, map_mul, Module.End.mul_apply]
  have hA (z : Module.Dual R E × E) :
      A (CliffordSpecification.hyperbolicOperator z) =
        CliffordSpecification.octonionOperator (d.symm z) := by
    rw [← CliffordModel.hyperbolicEquiv_ι b]
    change a ((equivOfIsometry d).symm (bCl.symm (bCl (ι q z)))) = _
    rw [bCl.symm_apply_apply, equivOfIsometry_symm, equivOfIsometry_apply, map_apply_ι]
    exact CliffordModel.octonionEquiv_ι _
  have hvac (f : Module.Dual R E) : A (contract f) vac = 0 := by
    rw [show contract f = CliffordSpecification.hyperbolicOperator (f, 0) by
      ext x; simp [hyperbolicOperator_apply]]
    rw [hA, action_apply]
    have hcoords : (Zorn.hyperbolicCoordinates R (d.symm (f, (0 : E)))).2 = 0 := by
      change (d (d.symm (f, (0 : E)))).2 = _
      rw [d.apply_symm_apply]
    generalize hcz : d.symm (f, (0 : E)) = z at hcoords ⊢
    obtain ⟨s, u, v, t⟩ := z
    have ht : t = 0 := congrFun hcoords none
    have hv : v = 0 := by
      funext i
      have hh : -v i = 0 := congrFun hcoords (some i)
      exact neg_eq_zero.mp hh
    subst t
    subst v
    apply Prod.ext
    · exact mul_zero _
    · change Composition.conjugate (norm R) (Zorn.ofCoordinates (s, u, 0, 0)) * first R = 0
      rw [Zorn.conjugate_formula]
      change Composition.Specification.zornProduct (0, -u, -0, s) (1, 0, 0, 0) = 0
      simp [Composition.Specification.zornProduct]
  have hb₀ : b.ExteriorAlgebra (∅ : Finset I) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  have hproj : rankOne 1 = wedgeProjector b (∅ : Finset I) := by
    apply b.ExteriorAlgebra.ext
    intro i
    rw [wedgeProjector_apply]
    change coord (b.ExteriorAlgebra i) • (1 : W) = _
    have hc : coord (b.ExteriorAlgebra i) = if ∅ = i then 1 else 0 := by
      change (b.ExteriorAlgebra.coord ∅) (b.ExteriorAlgebra i) = _
      simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
    rw [hc]
    by_cases hi : ∅ = i
    · subst i
      rw [ite_eq_left rfl, one_smul, hb₀, ite_eq_left rfl]
    · rw [ite_eq_right hi, zero_smul, ite_eq_right hi]
  -- The projector onto the empty wedge fixes the octonion vector.
  have hVac : F (1 : W) = vac := by
    change A (rankOne 1) vac = vac
    rw [hproj]
    let l := (Finset.univ : Finset I).toList
    change A ((l.map (matchingOccupation b ∅)).prod) vac = vac
    induction l with
    | nil => simp [Module.End.one_apply]
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]
      simp only [matchingOccupation, Finset.notMem_empty, ite_false, occupation, map_sub, map_one,
        map_mul, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, hvac, map_zero, sub_zero]
  have hsurj : Function.Surjective F := by
    intro y
    let T : Module.End R (Zorn R × Zorn R) :=
      (LinearMap.toSpanSingleton R _ y).comp
        ((LinearMap.fst R R _).comp ((Zorn.coordinates R).toLinearMap.comp (LinearMap.fst R (Zorn R) (Zorn R))))
    refine ⟨A.symm T 1, ?_⟩
    rw [hF, hVac, A.apply_symm_apply]
    change (1 : R) • y = y
    exact one_smul _ _
  have hbij : Function.Bijective F := by
    by_cases hR : Subsingleton R
    · letI := hR
      letI := Module.subsingleton R W
      exact ⟨Function.injective_of_subsingleton _, hsurj⟩
    · letI := not_subsingleton_iff_nontrivial.mp hR
      have := Module.Free.of_basis b.ExteriorAlgebra
      have := Module.Finite.of_basis b.ExteriorAlgebra
      apply OrzechProperty.bijective_of_surjective_of_finrank_le F hsurj
      rw [Module.finrank_eq_card_basis b.ExteriorAlgebra,
        Module.finrank_eq_card_basis ((Zorn.coordinateBasis R).prod (Zorn.coordinateBasis R))]
      simp [I, Fintype.card_finset]
  let F' := LinearEquiv.ofBijective F hbij
  have hInt (t : CliffordAlgebra (norm R)) (x : W) : F' (bCl (equivOfIsometry d t) x) = a t (F' x) := by
    have h := hF (bCl (equivOfIsometry d t)) x
    change F (bCl (equivOfIsometry d t) x) = a t (F x)
    rw [h]
    change a ((equivOfIsometry d).symm (bCl.symm (bCl (equivOfIsometry d t)))) (F x) = _
    rw [bCl.symm_apply_apply, AlgEquiv.symm_apply_apply]
  let ins : (0 : QuadraticForm R E) →qᵢ (norm R) :=
    ⟨d.symm.toLinearEquiv.toLinearMap.comp (LinearMap.inr R (Module.Dual R E) E), fun x =>
      by exact d.symm.map_app (0, x)⟩
  have hcreate : bCl.toAlgHom.comp ((equivOfIsometry d).toAlgHom.comp (CliffordAlgebra.map ins)) =
      Algebra.lmul R W := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change bCl (equivOfIsometry d (CliffordAlgebra.map ins (ι (0 : QuadraticForm R E) x))) =
      Algebra.lmul R W (ι (0 : QuadraticForm R E) x)
    rw [map_apply_ι, equivOfIsometry_apply, map_apply_ι]
    have hh : d.toIsometry (ins x) = (0, x) := d.apply_symm_apply (0, x)
    rw [hh, CliffordModel.hyperbolicEquiv_ι]
    apply LinearMap.ext
    intro y
    rw [hyperbolicOperator_apply]
    simp only [map_zero, LinearMap.zero_apply, add_zero]
    rfl
  have hgrade (k : ZMod 2) (x : W) (hx : x ∈ evenOdd (0 : QuadraticForm R E) k) :
      F x ∈ octonionBlock R k := by
    have hi := hInt (CliffordAlgebra.map ins x) 1
    have he := AlgHom.congr_fun hcreate x
    change bCl (equivOfIsometry d (CliffordAlgebra.map ins x)) = Algebra.lmul R W x at he
    rw [he] at hi
    change F (x * 1) = a (CliffordAlgebra.map ins x) (F 1) at hi
    rw [mul_one, hVac] at hi
    rw [hi]
    have hgrade := graded_action (norm R) ((Zorn.coordinateBasis R).reindex
        (toLex : (I ⊕ I) ≃ Lex (I ⊕ I))) (octonionBlock R) a.toAlgHom
      (fun j c z hz => by
        change a (ι (norm R) c) z ∈ _
        rw [CliffordModel.octonionEquiv_ι]
        exact octonionOperator_grade j c z hz)
      (map_isometry_evenOdd ins hx) ((octonionBlock_zero vac).mpr rfl)
    rw [add_zero] at hgrade
    exact hgrade
  have hz (x : W) (hx : x ∈ evenOdd (0 : QuadraticForm R E) 0) : (F x).2 = 0 :=
    (octonionBlock_zero _).mp (hgrade 0 x hx)
  have ho (x : W) (hx : x ∈ evenOdd (0 : QuadraticForm R E) 1) : (F x).1 = 0 :=
    (octonionBlock_one _).mp (hgrade 1 x hx)
  have hrep (h : Triple R) (s : CliffordUnits R) (hs : Corresponds a h s) :
      (∀ c, (s : CliffordAlgebra (norm R)) * ι (norm R) c * ↑s⁻¹ = ι (norm R) (h 1 c)) ∧
      ∀ x, F' (bCl (equivOfIsometry d s) x) =
        (Composition.conjugate (norm R) (h 0 (Composition.conjugate (norm R) (F' x).1)),
          h 2 (F' x).2) := by
    constructor
    · intro c
      rw [hs.2, mul_assoc, Units.mul_inv, mul_one]
    · intro x
      rw [hInt]
      exact hs.1 (F' x).1 (F' x).2
  refine ⟨d, bCl, F', rfl, CliffordModel.hyperbolicEquiv_ι b,
    hInt, fun x => ⟨hz x, ?_⟩, fun x => ⟨ho x, ?_⟩, hrep⟩
  all_goals
    intro hx
    have ht : x ∈ evenOdd (0 : QuadraticForm R E) 0 ⊔ evenOdd (0 : QuadraticForm R E) 1 :=
      (evenOdd_isCompl (0 : QuadraticForm R E)).sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz', hsum⟩ := Submodule.mem_sup.mp ht
    subst x
  · change (F (y + z)).2 = 0 at hx
    have hh : (F z).2 = 0 := by simpa [map_add, hz y hy] using hx
    have hzero : F z = 0 := Prod.ext (ho z hz') hh
    have hz0 := hbij.1 (hzero.trans F.map_zero.symm)
    simpa [hz0] using hy
  · change (F (y + z)).1 = 0 at hx
    have hh : (F y).1 = 0 := by simpa [map_add, ho z hz'] using hx
    have hzero : F y = 0 := Prod.ext hh (hz y hy)
    have hy0 := hbij.1 (hzero.trans F.map_zero.symm)
    simpa [hy0] using hz'

end HalfSpin

section Scalars

open SpinSpecification (ScalarClifford vectors reversion evenPart spinUnits coefficientMap)
open private cliffordEquiv_vector cliffordEquiv_even from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

private noncomputable def zornBasis (R : Type u) [CommRing R] : Basis (Fin 8) R (Zorn R) :=
  (Zorn.coordinateBasis R).reindex (Fintype.equivOfCardEq (by simp))

variable (R) (S : Type v) [CommRing S] [Algebra R S]

private def extendedZornIsometry :
    (CliffordSpecification.coefficientForm S n (zornBasis R)).IsometryEquiv (norm S) :=
  { (Zorn.baseChange R S) with
    map_app' := fun x => by
      change norm S (Zorn.baseChange R S x) = CliffordSpecification.coefficientForm S n (zornBasis R) x
      rw [CliffordModel.coefficient_form_agreement S n (zornBasis R)]
      change _ = Composition.normBaseChange S n x
      rw [Zorn.baseChange_norm]
      rfl }

private def extendedClifford : ScalarClifford n S ≃ₐ[S] CliffordAlgebra (norm S) :=
  (CliffordModel.baseChangeEquiv S n (zornBasis R)).trans
    (equivOfIsometry (extendedZornIsometry R S))

@[simp] private theorem extendedClifford_vector (x : S ⊗[R] C) :
    extendedClifford R S (vectors n S x) = ι (norm S) (Zorn.baseChange R S x) := by
  change equivOfIsometry (extendedZornIsometry R S)
    (CliffordModel.baseChangeEquiv S n (zornBasis R) (vectors n S x)) = _
  have h := cliffordEquiv_vector n S (zornBasis R) x
  change CliffordModel.baseChangeEquiv S n (zornBasis R) (vectors n S x) = _ at h
  rw [h, equivOfIsometry_apply, map_apply_ι]
  rfl

@[simp] private theorem extendedClifford_tmul_vector (x : C) :
    extendedClifford R S (1 ⊗ₜ[R] ι n x) =
      ι (norm S) (ZornSpecification.mapCoordinates (algebraMap R S) x) := by
  have h := extendedClifford_vector R S (1 ⊗ₜ[R] x)
  simpa only [LinearMap.baseChange_tmul, Zorn.baseChange_tmul, one_smul] using h

private theorem extendedClifford_reverse (x : ScalarClifford n S) :
    extendedClifford R S (reversion n S x) = reverse (extendedClifford R S x) := by
  change CliffordAlgebra.map (extendedZornIsometry R S).toIsometry
    (CliffordModel.baseChangeEquiv S n (zornBasis R) (reversion n S x)) = _
  rw [baseChangeEquiv_reverse, map_isometry_reverse]
  rfl

private theorem extendedClifford_even (x : ScalarClifford n S) :
    extendedClifford R S x ∈ evenOdd (norm S) 0 ↔ x ∈ evenPart n S := by
  let d := equivOfIsometry (extendedZornIsometry R S)
  let a := CliffordModel.baseChangeEquiv S n (zornBasis R) x
  change d a ∈ _ ↔ _
  have h₁ : a ∈ evenOdd (CliffordSpecification.coefficientForm S n (zornBasis R)) 0 ↔
      x ∈ evenPart n S := cliffordEquiv_even n S (zornBasis R) x
  rw [← h₁]
  constructor
  · intro hx
    have hh := map_isometry_evenOdd (extendedZornIsometry R S).symm.toIsometry hx
    change d.symm (d a) ∈ _ at hh
    simpa only [AlgEquiv.symm_apply_apply] using hh
  · exact map_isometry_evenOdd (extendedZornIsometry R S).toIsometry

private abbrev spinPoints := SpinFunctor.Spin n S (zornBasis R)

private theorem extendedClifford_spin (s : (ScalarClifford n S)ˣ) :
    s ∈ spinUnits n S ↔ IsSpin (Units.map (extendedClifford R S).toMonoidHom s) := by
  let d := extendedClifford R S
  let U : CliffordUnits S := Units.map d.toMonoidHom s
  have hv (x : S ⊗[R] C) : d (vectors n S x) = ι (norm S) (Zorn.baseChange R S x) :=
    extendedClifford_vector R S x
  have hM (a : (ScalarClifford n S)ˣ) (x : ScalarClifford n S) :
      d (SpinSpecification.conjugate n S a x) = d a * d x * d (↑a⁻¹) := by
    simp [SpinSpecification.conjugate]
  have hrel (a : ScalarClifford n S) :
      d a ∈ LinearMap.range (ι (norm S)) ↔ a ∈ LinearMap.range (vectors n S) := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := (Zorn.baseChange R S).surjective x
      exact ⟨y, d.injective ((hv y).trans hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hv x).symm⟩
  have hinv (x : CliffordAlgebra (norm S)) :
      (U : CliffordAlgebra (norm S)) * ((↑U⁻¹ : CliffordAlgebra (norm S)) * x * U) * ↑U⁻¹ = x := by
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have hrev : reverse (U : CliffordAlgebra (norm S)) * U = 1 ↔ reversion n S s * s = 1 := by
    change reverse (d s) * d s = 1 ↔ _
    rw [← extendedClifford_reverse, ← map_mul, ← map_one d, d.injective.eq_iff]
  change _ ↔ d s ∈ _ ∧ _ ∧ _
  constructor
  · rintro ⟨hE, hN, hF, hI⟩
    refine ⟨(extendedClifford_even R S _).mpr hE, hrev.mpr hN, ?_⟩
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := d.surjective z
      change d s * d x * d (↑s⁻¹) ∈ LinearMap.range (ι (norm S))
      rw [← hM]
      exact (hrel _).mpr (hF ((hrel _).mp hz))
    · intro hy
      obtain ⟨x, rfl⟩ := d.surjective y
      refine ⟨d (SpinSpecification.conjugate n S s⁻¹ x), (hrel _).mpr (hI ((hrel _).mp hy)), ?_⟩
      change (U : CliffordAlgebra (norm S)) *
        d (SpinSpecification.conjugate n S s⁻¹ x) * ↑U⁻¹ = d x
      rw [hM]
      exact hinv (d x)
  · rintro ⟨hE, hN, hF⟩
    refine ⟨(extendedClifford_even R S _).mp hE, hrev.mp hN, ?_, ?_⟩
    · intro x hx
      apply (hrel _).mp
      rw [hM]
      change _ ∈ (↑(LinearMap.range (ι (norm S))) : Set (CliffordAlgebra (norm S)))
      rw [← hF]
      exact ⟨d x, (hrel _).mpr hx, rfl⟩
    · intro x hx
      apply (hrel _).mp
      have hdx : d x ∈ (↑(LinearMap.range (ι (norm S))) : Set (CliffordAlgebra (norm S))) :=
        (hrel _).mpr hx
      rw [← hF] at hdx
      obtain ⟨y, hy, heq⟩ := hdx
      rw [hM]
      change (↑U⁻¹ : CliffordAlgebra (norm S)) * d x * U ∈ _
      change (U : CliffordAlgebra (norm S)) * y * ↑U⁻¹ = d x at heq
      rw [← heq]
      have hcancel : (↑U⁻¹ : CliffordAlgebra (norm S)) *
          ((U : CliffordAlgebra (norm S)) * y * ↑U⁻¹) * U = y := by
        simp only [← mul_assoc, Units.inv_mul, one_mul]
        rw [mul_assoc, Units.inv_mul, mul_one]
      rwa [hcancel]

private theorem corresponds_mul {K : Type*} [CommRing K]
    (a : CliffordAlgebra (norm K) →ₐ[K] Module.End K (Zorn K × Zorn K))
    {h k : Triple K} {s t : CliffordUnits K}
    (hs : Corresponds a h s) (ht : Corresponds a k t) :
    Corresponds a (h * k) (s * t) := by
  constructor
  · intro x y
    change a ((s : CliffordAlgebra (norm K)) * t) (x, y) = _
    rw [map_mul, Module.End.mul_apply, ht.1, hs.1, conj_conj]
    rfl
  · intro x
    change ((s : CliffordAlgebra (norm K)) * t) * ι (norm K) x =
      ι (norm K) (h 1 (k 1 x)) * (s * t : CliffordUnits K)
    rw [mul_assoc, ht.2, ← mul_assoc, hs.2, mul_assoc]
    rfl

private abbrev spinRelated (s : spinPoints R S) :
    relatedTriples (R := S) :=
  ((cliffordTriality S CliffordModel.octonionEquiv CliffordModel.octonionEquiv_ι
      CliffordModel.octonionEquiv_even CliffordModel.octonionEquiv_adjoint).2 _
    ((extendedClifford_spin R S s.val).mp s.property)).exists.choose

private theorem spinRelated_spec (s : spinPoints R S) :
    Corresponds (CliffordModel.octonionEquiv (R := S)).toAlgHom (spinRelated R S s)
      (Units.map (extendedClifford R S).toMonoidHom s.val) :=
  ((cliffordTriality S CliffordModel.octonionEquiv CliffordModel.octonionEquiv_ι
      CliffordModel.octonionEquiv_even CliffordModel.octonionEquiv_adjoint).2 _
    ((extendedClifford_spin R S s.val).mp s.property)).exists.choose_spec

private theorem spinRelated_unique (s : spinPoints R S) (h : relatedTriples (R := S))
    (hh : Corresponds (CliffordModel.octonionEquiv (R := S)).toAlgHom h
      (Units.map (extendedClifford R S).toMonoidHom s.val)) :
    h = spinRelated R S s :=
  ((cliffordTriality S CliffordModel.octonionEquiv CliffordModel.octonionEquiv_ι
      CliffordModel.octonionEquiv_even CliffordModel.octonionEquiv_adjoint).2 _
    ((extendedClifford_spin R S s.val).mp s.property)).unique hh (spinRelated_spec R S s)

private def spinRelatedHom : spinPoints R S →* relatedTriples (R := S) :=
  MonoidHom.mk' (spinRelated R S) (fun s t => by
    symm
    apply spinRelated_unique R S (s * t)
    change Corresponds (CliffordModel.octonionEquiv (R := S)).toAlgHom
      ((spinRelated R S s).val * (spinRelated R S t).val)
        (Units.map (extendedClifford R S).toMonoidHom (s.val * t.val))
    rw [map_mul]
    exact corresponds_mul _ (spinRelated_spec R S s) (spinRelated_spec R S t))

private def spinRelatedEquiv : spinPoints R S ≃* relatedTriples (R := S) := by
  apply MulEquiv.ofBijective (spinRelatedHom R S)
  constructor
  · intro s t heq
    have heq' : spinRelated R S s = spinRelated R S t := heq
    apply Subtype.ext
    apply Units.ext
    apply (extendedClifford R S).injective
    apply CliffordModel.octonionEquiv.injective
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hs := (spinRelated_spec R S s).1 x y
    have ht := (spinRelated_spec R S t).1 x y
    rw [heq'] at hs
    exact hs.trans ht.symm
  · intro h
    obtain ⟨s, hs, hc⟩ := spin_of_related CliffordModel.octonionEquiv
      CliffordModel.octonionEquiv_ι CliffordModel.octonionEquiv_even
      CliffordModel.octonionEquiv_adjoint h
    let t := Units.map (extendedClifford R S).symm.toMonoidHom s
    have heq : Units.map (extendedClifford R S).toMonoidHom t = s := by
      apply Units.ext
      exact (extendedClifford R S).apply_symm_apply _
    refine ⟨⟨t, (extendedClifford_spin R S t).mpr (heq.symm ▸ hs)⟩, ?_⟩
    symm
    apply spinRelated_unique R S
    rwa [heq]

open Composition.ZornSpecification (mapCoordinates)

private theorem map_octonion_add {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (x y : Zorn K) :
    mapCoordinates f (x + y) = mapCoordinates f x + mapCoordinates f y := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨a', u', v', b'⟩
  change (f (a + a'), f ∘ (u + u'), f ∘ (v + v'), f (b + b')) =
    (f a + f a', (f ∘ u) + (f ∘ u'), (f ∘ v) + (f ∘ v'), f b + f b')
  simp [Function.comp_def, Pi.add_def]

private theorem map_octonion_smul {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (r : K) (x : Zorn K) :
    mapCoordinates f (r • x) = f r • mapCoordinates f x := by
  rcases x with ⟨a, u, v, b⟩
  change (f (r * a), f ∘ (r • u), f ∘ (r • v), f (r * b)) =
    (f r * f a, f r • (f ∘ u), f r • (f ∘ v), f r * f b)
  simp [Function.comp_def, Pi.smul_def, smul_eq_mul]

private theorem map_octonion_conj {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (x : Zorn K) :
    mapCoordinates f (Composition.conjugate (norm K) x) =
      Composition.conjugate (norm L) (mapCoordinates f x) := by
  rcases x with ⟨a, u, v, b⟩
  change mapCoordinates f (Composition.conjugate (norm K) (Zorn.ofCoordinates (a, u, v, b))) =
    Composition.conjugate (norm L) (Zorn.ofCoordinates (f a, f ∘ u, f ∘ v, f b))
  rw [Zorn.conjugate_formula, Zorn.conjugate_formula]
  change (f b, f ∘ (-u), f ∘ (-v), f a) = (f b, -(f ∘ u), -(f ∘ v), f a)
  simp [Function.comp_def, Pi.neg_def]

@[simp] private theorem map_octonion_zero {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) : mapCoordinates f 0 = 0 := by
  change (f 0, f ∘ (0 : Fin 3 → K), f ∘ (0 : Fin 3 → K), f 0) =
    ((0, 0, 0, 0) : Composition.Specification.ZornCoordinates L)
  simp [Function.comp_def, Pi.zero_def]

@[simp] private theorem map_octonion_one {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) : mapCoordinates f 1 = 1 := by
  change (f 1, f ∘ (0 : Fin 3 → K), f ∘ (0 : Fin 3 → K), f 1) =
    ((1, 0, 0, 1) : Composition.Specification.ZornCoordinates L)
  simp [Function.comp_def, Pi.zero_def]

private def mapPair {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (x : Zorn K × Zorn K) : Zorn L × Zorn L :=
  (mapCoordinates f x.1, mapCoordinates f x.2)

private theorem mapPair_add {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (x y : Zorn K × Zorn K) :
    mapPair f (x + y) = mapPair f x + mapPair f y :=
  Prod.ext (map_octonion_add f x.1 y.1) (map_octonion_add f x.2 y.2)

private theorem mapPair_operator {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (c : Zorn K) (x : Zorn K × Zorn K) :
    mapPair f (CliffordSpecification.octonionOperator c x) =
      CliffordSpecification.octonionOperator (mapCoordinates f c) (mapPair f x) := by
  simp only [action_apply, mapPair, Zorn.mapCoordinates_mul, map_octonion_conj]

private abbrev scalarOctonion : ScalarClifford n S →ₐ[S] Module.End S (Zorn S × Zorn S) :=
  (CliffordModel.octonionEquiv (R := S)).toAlgHom.comp (extendedClifford R S).toAlgHom

private def originalOctonion : CliffordAlgebra n →+* Module.End S (Zorn S × Zorn S) :=
  (scalarOctonion R S).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

private theorem originalOctonion_scalar (r : R) (x : Zorn S × Zorn S) :
    originalOctonion R S (algebraMap R _ r) x = (algebraMap R S r) • x := by
  change scalarOctonion R S
    ((Algebra.TensorProduct.includeRight : CliffordAlgebra n →ₐ[R] ScalarClifford n S)
      (algebraMap R _ r)) x = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (ScalarClifford n S), AlgHom.commutes]
  rfl

private theorem originalOctonion_ι (x : C) :
    originalOctonion R S (ι n x) =
      CliffordSpecification.octonionOperator (mapCoordinates (algebraMap R S) x) := by
  change CliffordModel.octonionEquiv (extendedClifford R S (1 ⊗ₜ[R] ι n x)) = _
  rw [extendedClifford_tmul_vector, CliffordModel.octonionEquiv_ι]

variable {S} {T : Type w} [CommRing T] [Algebra R T]

private theorem map_originalOctonion (f : S →ₐ[R] T) (a : CliffordAlgebra n)
    (x : Zorn S × Zorn S) :
    mapPair f.toRingHom (originalOctonion R S a x) =
      originalOctonion R T a (mapPair f.toRingHom x) := by
  induction a using CliffordAlgebra.induction generalizing x with
  | algebraMap r =>
    rw [originalOctonion_scalar, originalOctonion_scalar]
    apply Prod.ext <;> simp [mapPair, map_octonion_smul]
  | ι c =>
    rw [originalOctonion_ι, originalOctonion_ι, mapPair_operator]
    congr 2
    rcases c with ⟨a, u, v, b⟩
    change (f (algebraMap R S a), f ∘ (algebraMap R S ∘ u), f ∘ (algebraMap R S ∘ v),
      f (algebraMap R S b)) =
      (algebraMap R T a, algebraMap R T ∘ u, algebraMap R T ∘ v, algebraMap R T b)
    simp [Function.comp_def]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, mapPair_add, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb]

private theorem scalarOctonion_tmul (r : S) (a : CliffordAlgebra n) (x : Zorn S × Zorn S) :
    scalarOctonion R S (r ⊗ₜ[R] a) x = r • originalOctonion R S a x := by
  have h : r • ((1 : S) ⊗ₜ[R] a) = r ⊗ₜ[R] a := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [← h, map_smul, LinearMap.smul_apply]
  rfl

private theorem map_scalarOctonion (f : S →ₐ[R] T) (a : ScalarClifford n S)
    (x : Zorn S × Zorn S) :
    mapPair f.toRingHom (scalarOctonion R S a x) =
      scalarOctonion R T (coefficientMap n S f a) (mapPair f.toRingHom x) := by
  induction a using TensorProduct.inductionOn with

  | tmul r a =>
    change mapPair f.toRingHom (scalarOctonion R S (r ⊗ₜ[R] a) x) =
      scalarOctonion R T (f r ⊗ₜ[R] a) (mapPair f.toRingHom x)
    rw [scalarOctonion_tmul, scalarOctonion_tmul, ← map_originalOctonion R f a x]
    apply Prod.ext <;> simp [mapPair, map_octonion_smul]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, mapPair_add, ha, hb]

private theorem scalarOctonion_intertwines (s : spinPoints R S) (c : Zorn S) (x : Zorn S × Zorn S) :
    scalarOctonion R S s.val.val (CliffordSpecification.octonionOperator c x) =
      CliffordSpecification.octonionOperator ((spinRelated R S s).val 1 c)
        (scalarOctonion R S s.val.val x) := by
  have hh := (spinRelated_spec R S s).2 c
  let a := CliffordModel.octonionEquiv (R := S)
  have he := congrArg (fun z : CliffordAlgebra (norm S) => a z x) hh
  simp only [map_mul, Module.End.mul_apply, CliffordModel.octonionEquiv_ι, a] at he
  exact he

private theorem spinRelated_naturality (f : S →ₐ[R] T) (s : spinPoints R S) (i : Fin 3) (x : Zorn S) :
    mapCoordinates f.toRingHom ((spinRelated R S s).val i x) =
      (spinRelated R T (SpinFunctor.map n (zornBasis R) f s)).val i (mapCoordinates f.toRingHom x) := by
  let t := SpinFunctor.map n (zornBasis R) f s
  have ht : t.val.val = coefficientMap n S f s.val.val := rfl
  have hm (z : Zorn S × Zorn S) :
      mapPair f.toRingHom (scalarOctonion R S s.val.val z) =
        scalarOctonion R T t.val.val (mapPair f.toRingHom z) := by
    rw [ht]
    exact map_scalarOctonion R f s.val.val z
  have hs₁ (a b : Zorn S) := (spinRelated_spec R S s).1 a b
  have ht₁ (a b : Zorn T) := (spinRelated_spec R T t).1 a b
  fin_cases i
  · let j := (0 : Fin 3)
    let conjS := Composition.conjugate (norm S)
    let conjT := Composition.conjugate (norm T)
    have hh := congrArg Prod.fst (hm (conjS x, 0))
    change mapCoordinates f.toRingHom (scalarOctonion R S s.val.val (conjS x, 0)).1 =
      (scalarOctonion R T t.val.val (mapCoordinates f.toRingHom (conjS x), mapCoordinates f.toRingHom 0)).1 at hh
    change mapCoordinates f.toRingHom ((spinRelated R S s).val j x) =
      (spinRelated R T t).val j (mapCoordinates f.toRingHom x)
    apply (conjugate_involutive (laws (R := T))).injective
    change conjT _ = conjT _
    rw [show mapCoordinates f.toRingHom (conjS x) = conjT (mapCoordinates f.toRingHom x) from
      map_octonion_conj _ _, map_octonion_zero] at hh
    have hS : scalarOctonion R S s.val.val (conjS x, 0) =
        (conjS ((spinRelated R S s).val j (conjS (conjS x))), (spinRelated R S s).val 2 0) := hs₁ _ _
    have hT : scalarOctonion R T t.val.val (conjT (mapCoordinates f.toRingHom x), 0) =
        (conjT ((spinRelated R T t).val j (conjT (conjT (mapCoordinates f.toRingHom x)))),
          (spinRelated R T t).val 2 0) := ht₁ _ _
    rw [hS, hT] at hh
    dsimp only [conjS, conjT] at hh ⊢
    simpa only [conj_conj, map_octonion_conj] using hh
  · let a := scalarOctonion R S s.val.val
    let b := scalarOctonion R T t.val.val
    let y : Zorn S × Zorn S := scalarOctonion R S (↑(s.val⁻¹)) (0, 1)
    have hy : a y = (0, 1) := by
      change (a * scalarOctonion R S (↑(s.val⁻¹))) (0, 1) = _
      rw [← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
    have hb : b (mapPair f.toRingHom y) = (0, 1) := by
      rw [← hm y, hy]
      simp [mapPair]
    have hiS := scalarOctonion_intertwines R s x y
    have hiT := scalarOctonion_intertwines R t (mapCoordinates f.toRingHom x)
      (mapPair f.toRingHom y)
    change a (CliffordSpecification.octonionOperator x y) = _ at hiS
    change b (CliffordSpecification.octonionOperator (mapCoordinates f.toRingHom x)
      (mapPair f.toRingHom y)) = CliffordSpecification.octonionOperator
        ((spinRelated R T t).val 1 (mapCoordinates f.toRingHom x)) (b (mapPair f.toRingHom y)) at hiT
    rw [hb] at hiT
    have hh := hm (CliffordSpecification.octonionOperator x y)
    change mapPair f.toRingHom (a _) = b _ at hh
    rw [hiS, mapPair_operator, mapPair_operator, hiT] at hh
    rw [hy] at hh
    simp only [action_apply, mapPair, map_octonion_zero, map_octonion_one, mul_one, mul_zero] at hh
    exact congrArg Prod.fst hh
  · have hh := congrArg Prod.snd (hm (0, x))
    change mapCoordinates f.toRingHom (scalarOctonion R S s.val.val (0, x)).2 =
      (scalarOctonion R T t.val.val (mapCoordinates f.toRingHom 0, mapCoordinates f.toRingHom x)).2 at hh
    rw [map_octonion_zero] at hh
    exact (congrArg (mapCoordinates f.toRingHom) (congrArg Prod.snd (hs₁ 0 x))).symm.trans
      (hh.trans (congrArg Prod.snd (ht₁ 0 (mapCoordinates f.toRingHom x))))

private theorem intertwines_after_tensor
    {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module L N]
    (E : L ⊗[K] M ≃ₗ[L] N) (f : M →ₗ[K] M) (g : N →ₗ[L] N)
    (h : ∀ x, E (1 ⊗ₜ[K] f x) = g (E (1 ⊗ₜ[K] x))) (z : L ⊗[K] M) :
    E (f.baseChange L z) = g (E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    rw [LinearMap.baseChange_tmul]
    have htmul (y : M) : E (r ⊗ₜ[K] y) = r • E (1 ⊗ₜ[K] y) := by
      rw [← E.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [htmul, htmul, h, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem extends_actions {K L : Type v} [CommRing K] [CommRing L] (f : K →+* L)
    (h : Triple K) (k : Triple L) (g : Model K ≃ₗ[K] Model K) (l : Model L ≃ₗ[L] Model L)
    (hh : ∀ i x, mapCoordinates f (h i x) = k i (mapCoordinates f x))
    (hg : ∀ x, mapModel f (g x) = l (mapModel f x)) :
    ExtendsActions f h k g l := by
  letI : Algebra K L := f.toAlgebra
  change (∀ i z, Zorn.baseChange K L ((h i).toLinearMap.baseChange L z) =
      k i (Zorn.baseChange K L z)) ∧
    ∀ z, modelBaseChange K L (g.toLinearMap.baseChange L z) = l (modelBaseChange K L z)
  constructor
  · intro i z
    refine intertwines_after_tensor (Zorn.baseChange K L) (h i).toLinearMap (k i).toLinearMap ?_ z
    intro x
    simp only [Zorn.baseChange_tmul, one_smul, LinearEquiv.coe_coe]
    exact hh i x
  · refine intertwines_after_tensor (modelBaseChange K L) g.toLinearMap l.toLinearMap ?_
    intro x
    have hModel (y : Model K) : modelBaseChange K L (1 ⊗ₜ[K] y) = mapModel f y := by
      unfold modelBaseChange
      rw [LinearEquiv.trans_apply, show HermitianSpecification.coordinatesBaseChange L (1 ⊗ₜ[K] y) =
        (fun i => 1 * algebraMap K L (y.1 i), fun i => 1 ⊗ₜ[K] y.2 i) from
          coordinatesBaseChange_tmul L 1 y]
      apply Prod.ext <;> funext i
      · exact one_mul (f (y.1 i))
      · exact (Zorn.baseChange_tmul (1 : L) (y.2 i)).trans (one_smul L _)
    simpa only [hModel, LinearEquiv.coe_coe] using hg x

theorem scalarTriality : ScalarTriality.{u, v} := by
  intro R _
  refine ⟨fun S _ _ => spinPoints R S, fun S _ _ => extendedClifford R S,
    fun _ _ => CliffordModel.octonionEquiv,
    fun S _ _ => spinRelatedEquiv R S, fun S _ => (frameTriality S).choose,
    fun _ _ _ => rfl, fun S _ _ => extendedClifford_vector R S,
    fun _ _ => CliffordModel.octonionEquiv_ι, fun S _ _ s => spinRelated_spec R S s,
    fun S _ => (frameTriality S).choose_spec, ?_⟩
  intro S T _ _ _ _ f s
  let t := SpinFunctor.map (norm R) (zornBasis R) f s
  have hframe (x : Model S) :
      mapModel f.toRingHom (((frameTriality S).choose (spinRelated R S s)).val x) =
        ((frameTriality T).choose (spinRelated R T t)).val (mapModel f.toRingHom x) := by
    rw [(frameTriality S).choose_spec, (frameTriality T).choose_spec]
    exact Prod.ext rfl (funext fun i => spinRelated_naturality R f s i (x.2 i))
  exact ⟨t, rfl, spinRelated_naturality R f s, hframe,
    extends_actions _ _ _ _ _ (spinRelated_naturality R f s) hframe⟩

end Scalars

section Geometry

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open SpinSpecification (ScalarClifford vectors reversion evenPart spinUnits coefficientMap)
open SplitSpinSpecification (integralForm)

private def integralZornIsometry : (integralForm 4).IsometryEquiv (norm ℤ) := by
  let i : Option (Fin 3) ≃ Fin 4 := Fintype.equivOfCardEq (by simp)
  let f : (Fin 4 → ℤ) ≃ₗ[ℤ] (Option (Fin 3) → ℤ) := LinearEquiv.funCongrLeft ℤ ℤ i
  let g := f.symm.dualMap.prodCongr f
  refine (show (integralForm 4).IsometryEquiv _ from ⟨g, ?_⟩).trans (Zorn.hyperbolicIsometry ℤ).symm
  rintro ⟨d, x⟩
  change d (f.symm (f x)) = d x
  rw [f.symm_apply_apply]

section Transport

variable {K : Type*} [CommRing K] {V W : Type*}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {q : QuadraticForm K V} {q' : QuadraticForm K W}
variable (S : Type*) [CommRing S] [Algebra K S]

private def scalarIsometry (d : q.IsometryEquiv q') : ScalarClifford q S ≃ₐ[S] ScalarClifford q' S :=
  Algebra.TensorProduct.congr (.refl : S ≃ₐ[S] S) (equivOfIsometry d)

private theorem scalarIsometry_spin (d : q.IsometryEquiv q') {s : (ScalarClifford q S)ˣ}
    (hs : s ∈ spinUnits q S) : Units.map (scalarIsometry S d).toMonoidHom s ∈ spinUnits q' S := by
  let M := scalarIsometry S d
  let t := Units.map M.toMonoidHom s
  have hr (x : ScalarClifford q S) : M (reversion q S x) = reversion q' S (M x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      change r ⊗ₜ[K] CliffordAlgebra.map d.toIsometry (reverse x) =
        r ⊗ₜ[K] reverse (CliffordAlgebra.map d.toIsometry x)
      rw [map_isometry_reverse]
    | add x y hx hy => simp only [map_add, hx, hy]
  let D : S ⊗[K] V ≃ₗ[S] S ⊗[K] W :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) d.toLinearEquiv
  have hv (x : S ⊗[K] V) : M (vectors q S x) = vectors q' S (D x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      change r ⊗ₜ[K] CliffordAlgebra.map d.toIsometry (CliffordAlgebra.ι q x) = r ⊗ₜ[K] CliffordAlgebra.ι q' (d x)
      rw [map_apply_ι]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrange (x : ScalarClifford q S) :
      M x ∈ LinearMap.range (vectors q' S) ↔ x ∈ LinearMap.range (vectors q S) := by
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := D.surjective y
      exact ⟨z, M.injective ((hv z).trans hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨D y, (hv y).symm⟩
  have hc (a : (ScalarClifford q S)ˣ) (x : ScalarClifford q S) :
      SpinSpecification.conjugate q' S (Units.map M.toMonoidHom a) (M x) =
        M (SpinSpecification.conjugate q S a x) := by simp [SpinSpecification.conjugate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hM : evenPart q S ≤ (evenPart q' S).comap M.toLinearEquiv.toLinearMap := by
      rw [evenPart, Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      change (1 : S) ⊗ₜ[K] CliffordAlgebra.map d.toIsometry a ∈ evenPart q' S
      exact Submodule.tmul_mem_baseChange_of_mem _ (map_isometry_evenOdd d.toIsometry ha)
    exact hM hs.1
  · change reversion q' S (M (s : ScalarClifford q S)) * M s = 1
    rw [← hr, ← map_mul, hs.2.1, map_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := M.surjective x
    rw [hc]
    exact (hrange _).mpr (hs.2.2.1 ((hrange _).mp hx))
  · intro x hx
    obtain ⟨y, rfl⟩ := M.surjective x
    change SpinSpecification.conjugate q' S t⁻¹ (M y) ∈ _
    rw [show t⁻¹ = Units.map M.toMonoidHom s⁻¹ by rw [map_inv]]
    rw [hc]
    exact (hrange _).mpr (hs.2.2.2 ((hrange _).mp hx))

private theorem scalarIsometry_natural {T : Type*} [CommRing T] [Algebra K T]
    (d : q.IsometryEquiv q') (f : S →ₐ[K] T) (x : ScalarClifford q S) :
    scalarIsometry T d (coefficientMap q S f x) =
      coefficientMap q' S f (scalarIsometry S d x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Transport

theorem integralFrameGeometry : IntegralFrameGeometry := by
  obtain ⟨G, e, _, _, he, _, _, _, _, hsmooth, hconn⟩ := SplitSpin.spinGeometry 4 (by decide)
  let d := integralZornIsometry
  let m (S : CommAlgCat ℤ) :=
    Units.map (scalarIsometry S d).toMonoidHom
  let j (S : CommAlgCat ℤ) : SpinSpecification.SchemePoints G S →* spinPoints ℤ S :=
    ((m S).comp (e S)).codRestrict (spinPoints ℤ S) fun a =>
      scalarIsometry_spin S d ((he.1 S).2 ▸ Set.mem_range_self (f := e S) a)
  have hj (S : CommAlgCat ℤ) : Function.Bijective (j S) := by
    constructor
    · intro a b hab
      apply (he.1 S).1
      apply Units.ext
      apply (scalarIsometry S d).injective
      exact congrArg (fun u : spinPoints ℤ S => u.val.val) hab
    · intro t
      let u := Units.map (scalarIsometry S d.symm).toMonoidHom t.val
      have hu : u ∈ spinUnits (integralForm 4) S :=
        scalarIsometry_spin S d.symm t.property
      rw [← (he.1 S).2] at hu
      obtain ⟨a, ha⟩ := hu
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change m S (e S a) = t.val
      rw [ha]
      apply Units.ext
      exact (scalarIsometry S d).apply_symm_apply _
  have hj_natural {S T : CommAlgCat ℤ} (f : S ⟶ T) (a : SpinSpecification.SchemePoints G S) :
      j T ((algSpec (CommRingCat.of ℤ)).map f.op ≫ a) =
        SpinFunctor.map (norm ℤ) (zornBasis ℤ) f.hom (j S a) := by
    apply Subtype.ext
    apply Units.ext
    change scalarIsometry T d (e T _).val =
      coefficientMap (norm ℤ) S f.hom (scalarIsometry S d (e S a).val)
    rw [he.2 f a]
    exact scalarIsometry_natural S d f.hom (e S a).val
  let ρ (S : CommAlgCat ℤ) := (spinPoints ℤ S).subtype.comp (j S)
  have hρ : SpinSpecification.IsSpinPointRepresentation (norm ℤ) G ρ := by
    refine ⟨fun S => ⟨Subtype.val_injective.comp (hj S).1, ?_⟩, ?_⟩
    · ext t
      constructor
      · rintro ⟨a, rfl⟩
        exact (j S a).property
      · intro ht
        obtain ⟨a, ha⟩ := (hj S).2 ⟨t, ht⟩
        exact ⟨a, congrArg Subtype.val ha⟩
    · intro S T f a
      exact congrArg Subtype.val (hj_natural f a)
  let h (S : CommAlgCat ℤ) : SpinSpecification.SchemePoints G S ≃* relatedTriples (R := S) :=
    (MulEquiv.ofBijective (j S) (hj S)).trans (spinRelatedEquiv ℤ S)
  let p (S : CommAlgCat ℤ) : SpinSpecification.SchemePoints G S ≃* frameStabilizer (R := S) :=
    (h S).trans (frameTriality S).choose
  refine ⟨G, ?_, hconn, p, ρ, h, fun S => extendedClifford ℤ S,
    fun _ => CliffordModel.octonionEquiv, hρ, fun S => extendedClifford_vector ℤ S,
    fun _ => CliffordModel.octonionEquiv_ι, fun S a => spinRelated_spec ℤ S (j S a),
    fun S a => (frameTriality S).choose_spec (h S a), ?_⟩
  · simpa using hsmooth
  intro S T f a x
  let aT := (algSpec (CommRingCat.of ℤ)).map f.op ≫ a
  change mapModel f.hom.toRingHom
      (((frameTriality S).choose (spinRelated ℤ S (j S a))).val x) =
    ((frameTriality T).choose (spinRelated ℤ T (j T aT))).val (mapModel f.hom.toRingHom x)
  rw [show j T aT = _ from hj_natural f a, (frameTriality S).choose_spec, (frameTriality T).choose_spec]
  exact Prod.ext rfl (funext fun i => spinRelated_naturality ℤ f.hom (j S a) i (x.2 i))

end Geometry
/-- The subgroup of triples of norm isometries satisfying the cyclic identities. -/
abbrev relatedTriples (R : Type u) [CommRing R] : Subgroup (Triple R) :=
  TrialitySpecification.relatedTriples

/-- The pointwise stabilizer of the ordered diagonal frame of the split Albert model. -/
abbrev frameStabilizer (R : Type u) [CommRing R] : Subgroup (Model R ≃ₗ[R] Model R) :=
  TrialitySpecification.frameStabilizer

end

end LinearAlgebraicGroups.Albert.Triality
