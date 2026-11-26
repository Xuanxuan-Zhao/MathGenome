import Specs.LinearAlgebraicGroups.Arithmetic.BracketLatticeCompactness
import LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Localization.Integer

open scoped BigOperators NumberField RestrictedProduct

namespace LinearAlgebraicGroups.Arithmetic.BracketLatticeCompactness

open AdelicGroups AdelicLatticeBounds Filter IsDedekindDomain Set
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)

universe u v w

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)

private theorem clearDenominators {K A : Type*} [Field K] [NumberField K]
    (s : Finset A) (f : A → K) :
    ∃ t : K, t ≠ 0 ∧ ∀ a ∈ s, t * f a ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s f
  refine ⟨algebraMap (𝓞 K) K m, ?_, ?_⟩
  · exact fun hz => nonZeroDivisors.coe_ne_zero m ((IsFractionRing.injective (𝓞 K) K) (hz.trans (map_zero _).symm))
  · intro a ha
    obtain ⟨z, hz⟩ := hm a ha
    exact ⟨z, by simpa only [Algebra.smul_def] using hz⟩

private theorem integral_image {K : Type*} [Field K] [NumberField K]
    (v : NumberFinitePlace K) {x : K} (hx : x ∈ (algebraMap (𝓞 K) K).range) :
    algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  obtain ⟨a, rfl⟩ := hx
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K)
    (v.adicCompletionIntegers K) (v.adicCompletion K)]
  exact (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a).property

private theorem normalizePolynomial {I K : Type*} [Fintype I] [Field K] [NumberField K]
    (p : MvPolynomial I K) :
    ∃ t : K, t ≠ 0 ∧ ∀ (v : NumberFinitePlace K) (x : I → v.adicCompletion K),
      (∀ i, x i ∈ v.adicCompletionIntegers K) →
      (t • p).eval₂ (algebraMap K (v.adicCompletion K)) x ∈ v.adicCompletionIntegers K := by
  classical
  obtain ⟨t, ht, h⟩ := clearDenominators p.support p.coeff
  refine ⟨t, ht, fun v x hx => ?_⟩
  let O := (v.adicCompletionIntegers K).toSubring
  change _ ∈ O
  rw [MvPolynomial.eval₂_eq']
  apply Subring.sum_mem
  intro m hm
  apply Subring.mul_mem
  · apply integral_image v
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    apply h m
    by_contra hd
    exact (MvPolynomial.mem_support_iff.mp hm) (by
      rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.mp hd, smul_zero])
  · exact Subring.prod_mem O fun j _ => O.pow_mem (hx j) _

private theorem eval₂_smul {I K L : Type*} [Field K] [Field L] (f : K →+* L)
    (p : MvPolynomial I K) (t : K) (x : I → L) :
    (t • p).eval₂ f x = f t * p.eval₂ f x := by
  exact MvPolynomial.eval₂Hom_smul f x t p

private theorem bracket_map {I K L : Type*} [Fintype I] [Field K] [Field L]
    (c : I → I → I → K) (f : K →+* L) (x y : I → K) :
    embedCoordinates f (bracket c (RingHom.id K) x y) =
      bracket c f (embedCoordinates f x) (embedCoordinates f y) := by
  ext i
  simp [bracket, Matrix.mulVec, dotProduct, embedCoordinates, map_sum, map_mul]

private theorem bracket_scale {I K L : Type*} [Fintype I] [CommRing K] [CommRing L]
    (c : I → I → I → K) (f : K →+* L) (t : K) (x y : I → L) :
    bracket (fun i j k => t * c i j k) f x y = f t • bracket c f x y := by
  ext i
  simp only [bracket, Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem bracket_mem {I K L : Type*} [Fintype I] [CommRing K] [CommRing L]
    (c : I → I → I → K) (f : K →+* L) (O : Subring L)
    (hc : ∀ i j k, f (c i j k) ∈ O) {x y : I → L}
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) :
    ∀ i, bracket c f x y i ∈ O := by
  intro i
  exact O.sum_mem fun j _ =>
    O.mul_mem (O.sum_mem fun k _ => O.mul_mem (hx k) (hc k j i)) (hy j)

private def bracketLinear {I B L : Type*} [Fintype I] [CommRing B] [CommRing L] [Algebra B L]
    (c : I → I → I → L) : (I → L) →ₗ[B] (I → L) →ₗ[B] (I → L) where
  toFun x :=
    { toFun := bracket c (RingHom.id L) x
      map_add' := by intro y z; exact Matrix.mulVec_add _ y z
      map_smul' := by intro t y; exact Matrix.mulVec_smul _ t y }
  map_add' x y := by
    ext z i
    simp [bracket, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  map_smul' t x := by
    ext z i
    simp [bracket, Matrix.mulVec, dotProduct, Algebra.smul_def, mul_assoc, ← Finset.mul_sum]

open private isLattice_matrixLattice from LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
open private completedLattice_isLattice from LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection

private theorem completedStandard {I K : Type*} [Fintype I] [DecidableEq I]
    [Field K] [NumberField K] (v : NumberFinitePlace K) :
    (completedLattice v (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)) :
      Set (I → v.adicCompletion K)) = {x | ∀ i, x i ∈ v.adicCompletionIntegers K} := by
  rw [completedBasisLattice, map_one, Matrix.GeneralLinearGroup.coe_one,
    show Matrix.mulVec (1 : Matrix I I (v.adicCompletion K)) = id from
      funext Matrix.one_mulVec, Set.image_id]

private theorem mulVec_inv_cancel {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (g : Matrix.GeneralLinearGroup I K) (x : I → K) :
    g⁻¹.val.mulVec (g.val.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, show g⁻¹.val * g.val = 1 from g.inv_val, Matrix.one_mulVec]

private theorem mulVec_image_inv {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (g : Matrix.GeneralLinearGroup I K) (s : Set (I → K)) :
    g.val.mulVec '' (g⁻¹.val.mulVec '' s) = s := by
  rw [Set.image_image]
  exact Set.image_congr (fun x _ => mulVec_inv_cancel g⁻¹ x) |>.trans (Set.image_id' s)

private def localLattice {I K : Type*} [Fintype I] [DecidableEq I] [Field K] [NumberField K]
    (v : NumberFinitePlace K) (g : Matrix.GeneralLinearGroup I (v.adicCompletion K)) :
    Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K) :=
  (completedLattice v (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K))).map
    (((Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv).toLinearMap.restrictScalars _)

private instance localLattice_isLattice {I K : Type*} [Fintype I] [DecidableEq I]
    [Field K] [NumberField K] (v : NumberFinitePlace K)
    (g : Matrix.GeneralLinearGroup I (v.adicCompletion K)) :
    Submodule.IsLattice (v.adicCompletion K) (localLattice v g) := by
  let S := completedLattice v (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K))
  let e := (Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv
  let : Submodule.IsLattice K (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)) :=
    isLattice_matrixLattice (R := 𝓞 K) _
  let : Submodule.IsLattice (v.adicCompletion K) S := completedLattice_isLattice v _
  refine ⟨Submodule.FG.map (e.toLinearMap.restrictScalars _) (Submodule.IsLattice.fg (M := S)), ?_⟩
  change Submodule.span (v.adicCompletion K) (e '' (S : Set _)) = ⊤
  rw [← LinearEquiv.coe_coe, ← Submodule.map_span, Submodule.IsLattice.span_eq_top,
    Submodule.map_top, LinearEquiv.range]

private theorem localLattice_image {I K : Type*} [Fintype I] [DecidableEq I]
    [Field K] [NumberField K] (v : NumberFinitePlace K)
    (g : Matrix.GeneralLinearGroup I (v.adicCompletion K)) :
    g.val.mulVec '' (localLattice v g : Set _) =
      (completedLattice v (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)) : Set _) :=
  mulVec_image_inv g _

private theorem localLattice_eq_of_integral {I K : Type*} [Fintype I] [DecidableEq I]
    [Field K] [NumberField K] (v : NumberFinitePlace K)
    (g : Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype).range) :
    localLattice v g = completedLattice v
      (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)) := by
  apply SetLike.coe_injective
  change g⁻¹.val.mulVec '' _ = _
  rw [completedStandard]
  exact (integralMatrixIffPreservesBox (v.adicCompletionIntegers K).toSubring g⁻¹).mp
    (Subgroup.inv_mem _ hg)


private def act {N F : Type*} [Fintype N] [DecidableEq N] [CommRing F]
    (M : Matrix.GeneralLinearGroup N F) : (N → F) ≃ₗ[F] (N → F) :=
  (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv

@[simp] private theorem act_apply {N F : Type*} [Fintype N] [DecidableEq N] [CommRing F]
    (M : Matrix.GeneralLinearGroup N F) (x : N → F) : act M x = M.val.mulVec x := rfl

private theorem act_mul {N F : Type*} [Fintype N] [DecidableEq N] [CommRing F]
    (M T : Matrix.GeneralLinearGroup N F) (x : N → F) :
    act (M * T) x = act M (act T x) := by
  simp only [act_apply]
  exact (Matrix.mulVec_mulVec _ _ _).symm

private theorem act_map {N F L : Type*} [Fintype N] [DecidableEq N] [Field F] [Field L]
    (f : F →+* L) (M : Matrix.GeneralLinearGroup N F) (x : N → F) :
    act (Matrix.GeneralLinearGroup.map f M) (embedCoordinates f x) =
      embedCoordinates f (act M x) := by
  ext i
  exact (RingHom.map_mulVec f M.val x i).symm

private theorem continuous_act {X N F : Type*} [TopologicalSpace X]
    [Fintype N] [DecidableEq N] [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
    {M : X → Matrix.GeneralLinearGroup N F} {x : X → N → F}
    (hM : Continuous M) (hx : Continuous x) : Continuous fun a => act (M a) (x a) := by
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp (Matrix.GeneralLinearGroup.continuous_apply _ hM i)).mul
      ((continuous_apply j).comp hx)

private def inBasis {K N I : Type*} [Field K] [CharZero K] [Fintype N] [DecidableEq N]
    (b : Module.Basis N ℚ (I → K)) (M : Matrix.GeneralLinearGroup N ℚ) :
    (N → ℚ) ≃ₗ[ℚ] (I → K) :=
  (act M).trans b.equivFun.symm

private theorem inBasis_lattice {K N I : Type*} [Field K] [CharZero K]
    [Fintype N] [DecidableEq N]
    (b : Module.Basis N ℚ (I → K)) (L : Set (I → K)) (M : Matrix.GeneralLinearGroup N ℚ)
    (hM : IsBasisMatrix ℤ b L M) :
    L = Set.range fun z : N → ℤ => inBasis b M (fun j => (z j : ℚ)) := by
  have h := congrArg (fun s => b.equivFun.symm '' s) hM
  rw [IsBasisMatrix] at hM
  change b.equivFun.symm '' (b.equivFun '' L) =
    b.equivFun.symm '' Set.range (fun z : N → ℤ => M.val.mulVec (algebraMap ℤ ℚ ∘ z)) at h
  rw [← Set.range_comp, Set.image_image] at h
  simpa [inBasis, Function.comp_def] using h

private def eVec {F : Type*} (N : Type*) [DecidableEq N] [Zero F] [One F] (j : N) : N → F :=
  Pi.single j 1

@[simp] private theorem embed_eVec {N F L : Type*} [DecidableEq N] [CommRing F] [CommRing L]
    (f : F →+* L) (j : N) : f ∘ (eVec N j) = eVec N j := by
  ext i
  by_cases h : i = j <;> simp [eVec, h, Pi.single_eq_of_ne]

private theorem inBasis_eVec_mem {K N I : Type*} [Field K] [CharZero K]
    [Fintype N] [DecidableEq N] {b : Module.Basis N ℚ (I → K)}
    {L : Set (I → K)} {M : Matrix.GeneralLinearGroup N ℚ}
    (hM : IsBasisMatrix ℤ b L M) (j : N) : inBasis b M (eVec N j) ∈ L := by
  rw [inBasis_lattice b L M hM]
  refine ⟨eVec N j, congrArg (inBasis b M) ?_⟩
  exact embed_eVec (algebraMap ℤ ℚ) j

private theorem inBasis_integral {K N I : Type*} [Field K] [CharZero K]
    [Fintype N] [DecidableEq N] {b : Module.Basis N ℚ (I → K)}
    {L : Set (I → K)} {M : Matrix.GeneralLinearGroup N ℚ}
    (hM : IsBasisMatrix ℤ b L M) {x : I → K} (hx : x ∈ L) :
    ∃ z : N → ℤ, ∀ j, (inBasis b M).symm x j = (z j : ℚ) := by
  rw [inBasis_lattice b L M hM] at hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z, fun j => congrFun (LinearEquiv.symm_apply_apply _ _) j⟩

private theorem finite_rational_range {X T : Type*} [Finite T]
    (a : X → T → ℚ) (k : T → Set ℝ) (hk : ∀ t, IsCompact (k t))
    (hin : ∀ x t, (a x t : ℝ) ∈ k t)
    (hz : ∀ x t, ∃ z : ℤ, a x t = z) : (Set.range a).Finite := by
  let S (t : T) := (fun z : ℤ => (z : ℝ)) ⁻¹' k t
  have hS (t : T) : (S t).Finite :=
    (Real.isClosedEmbedding_intCast.isCompact_preimage (hk t)).finite_of_discrete
  have (t : T) : Finite (S t) := (hS t).to_subtype
  choose z hz using hz
  let z' (x : X) (t : T) : S t := ⟨z x t, by
    change (z x t : ℝ) ∈ k t
    have he := congrArg (fun q : ℚ => (q : ℝ)) (hz x t)
    push_cast at he
    rw [← he]
    exact hin x t⟩
  have hEq : a = (fun v : ∀ t, S t => fun t => ((v t).val : ℚ)) ∘ z' := by
    funext x t
    exact hz x t
  rw [hEq, Set.range_comp]
  exact (Set.toFinite (Set.univ : Set (∀ t, S t))).image _ |>.subset
    (Set.image_mono (Set.subset_univ _))

private theorem transport_bracket {R V W : Type*} [CommRing R] [AddCommGroup V]
    [AddCommGroup W] [Module R V] [Module R W] (e : V ≃ₗ[R] W)
    (b : W →ₗ[R] W →ₗ[R] W) :
    ∃ f : V →ₗ[R] V →ₗ[R] V, ∀ x y, f x y = e.symm (b (e x) (e y)) := by
  refine ⟨((b.comp e.toLinearMap).compl₂ e.toLinearMap).compr₂ e.symm.toLinearMap, ?_⟩
  intro x y
  rfl

private theorem comparison_preserves {K I N : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N ℚ (I → K)) (M M' : Matrix.GeneralLinearGroup N ℚ)
    (c : I → I → I → K)
    (hb : ∀ j k, (inBasis b M).symm
      (bracket c (RingHom.id K) (inBasis b M (eVec N j)) (inBasis b M (eVec N k))) =
      (inBasis b M').symm
      (bracket c (RingHom.id K) (inBasis b M' (eVec N j)) (inBasis b M' (eVec N k))))
    (hs : ∀ t j, (inBasis b M).symm (NumberField.integralBasis K t • inBasis b M (eVec N j)) =
      (inBasis b M').symm (NumberField.integralBasis K t • inBasis b M' (eVec N j))) :
    ∃ T : Matrix.GeneralLinearGroup I K, PreservesBracket c (RingHom.id K) T ∧
      ∀ z, act T (inBasis b M' z) = inBasis b M z := by
  let f := (inBasis b M').symm.trans (inBasis b M)
  let S (t : K) : (I → K) →ₗ[ℚ] (I → K) := t • LinearMap.id
  have hS (t : K) (x : I → K) : S t x = t • x := rfl
  have hcomm (t : _) : f.toLinearMap.comp (S (NumberField.integralBasis K t)) =
      (S (NumberField.integralBasis K t)).comp f.toLinearMap := by
    apply ((Pi.basisFun ℚ N).map (inBasis b M')).ext
    intro j
    apply (inBasis b M).symm.injective
    simpa [f, hS, Pi.basisFun_apply, eVec] using (hs t j).symm
  have hlin (t : K) (x : I → K) : f (t • x) = t • f x := by
    rw [← (NumberField.integralBasis K).sum_repr t, Finset.sum_smul, Finset.sum_smul,
      map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_assoc, smul_assoc, map_smul]
    exact congrArg ((NumberField.integralBasis K).repr t j • ·)
      (LinearMap.congr_fun (hcomm j) x)
  let F : (I → K) ≃ₗ[K] (I → K) :=
    { toEquiv := f.toEquiv
      map_add' := f.map_add
      map_smul' := hlin }
  let T := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv F)
  have hT : act T = F := by
    unfold act T
    rw [MulEquiv.apply_symm_apply]
    ext x
    rfl
  obtain ⟨B, hB⟩ := transport_bracket (inBasis b M) (bracketLinear (B := ℚ) c)
  obtain ⟨B', hB'⟩ := transport_bracket (inBasis b M') (bracketLinear (B := ℚ) c)
  have heq : B = B' := by
    apply (Pi.basisFun ℚ N).ext
    intro j
    apply (Pi.basisFun ℚ N).ext
    intro k
    simpa only [hB, hB', Pi.basisFun_apply, eVec] using
      (show (inBasis b M).symm (bracketLinear (B := ℚ) c (eVec N j |> inBasis b M)
        (eVec N k |> inBasis b M)) = (inBasis b M').symm
          (bracketLinear (B := ℚ) c (eVec N j |> inBasis b M')
            (eVec N k |> inBasis b M')) from hb j k)
  refine ⟨T, ?_, ?_⟩
  · intro x y
    change bracket c (RingHom.id K) (act T x) (act T y) =
      act T (bracket c (RingHom.id K) x y)
    rw [hT]
    apply (inBasis b M).symm.injective
    let x' := (inBasis b M').symm x
    let y' := (inBasis b M').symm y
    have h := congrArg (fun H : (N → ℚ) →ₗ[ℚ] (N → ℚ) →ₗ[ℚ] (N → ℚ) => H x' y') heq
    rw [hB, hB'] at h
    simpa [F, f, x', y', bracketLinear] using h
  · intro z
    rw [hT]
    change inBasis b M ((inBasis b M').symm (inBasis b M' z)) = _
    rw [LinearEquiv.symm_apply_apply]

private theorem preservesBracket_scale {I K L : Type*} [Fintype I] [DecidableEq I]
    [Field K] [Field L] (c : I → I → I → K) (f : K →+* L) (t : K) (ht : t ≠ 0)
    (g : Matrix.GeneralLinearGroup I L) :
    PreservesBracket (fun i j k => t * c i j k) f g ↔ PreservesBracket c f g := by
  unfold PreservesBracket
  simp only [bracket_scale, Matrix.mulVec_smul]
  constructor
  · intro h x y
    ext i
    exact mul_left_cancel₀ ((map_ne_zero f).mpr ht) (congrFun (h x y) i)
  · intro h x y
    rw [h]

private theorem bracket_lattice {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (c : I → I → I → K)
    (hc : ∀ i j k, c i j k ∈ (algebraMap (𝓞 K) K).range)
    (g : ∀ v : NumberFinitePlace K, Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (hpres : ∀ v, PreservesBracket c (algebraMap K (v.adicCompletion K)) (g v))
    {x y : I → K} (hx : x ∈ rationalLatticeIntersection (fun v => localLattice v (g v)))
    (hy : y ∈ rationalLatticeIntersection (fun v => localLattice v (g v))) :
    bracket c (RingHom.id K) x y ∈ rationalLatticeIntersection (fun v => localLattice v (g v)) := by
  intro v
  let f := algebraMap K (v.adicCompletion K)
  have hh (z : I → v.adicCompletion K) :
      z ∈ localLattice v (g v) ↔ ∀ i, (g v).val.mulVec z i ∈ v.adicCompletionIntegers K := by
    change z ∈ (g v)⁻¹.val.mulVec '' (completedLattice v
      (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)) : Set _) ↔ _
    rw [completedStandard]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [show (g v).val.mulVec ((g v)⁻¹.val.mulVec z) = z from mulVec_inv_cancel (g v)⁻¹ z]
      exact hz
    · exact fun hz => ⟨_, hz, mulVec_inv_cancel (g v) z⟩
  apply (hh _).mpr
  rw [bracket_map, ← hpres v]
  exact bracket_mem c f (v.adicCompletionIntegers K).toSubring
    (fun i j k => integral_image v (hc i j k)) ((hh _).mp (hx v)) ((hh _).mp (hy v))

private theorem completedLattice_image {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (v : NumberFinitePlace K)
    (T : Matrix.GeneralLinearGroup I K) (L L' : Submodule (𝓞 K) (I → K))
    (h : act T '' (L' : Set (I → K)) = L) :
    act (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) T) ''
      (completedLattice v L' : Set _) = (completedLattice v L : Set _) := by
  let f := algebraMap K (v.adicCompletion K)
  let e := (act (Matrix.GeneralLinearGroup.map f T)).toLinearMap.restrictScalars
    (v.adicCompletionIntegers K)
  change e '' (completedLattice v L' : Set _) = _
  rw [← Submodule.map_coe]
  unfold completedLattice
  rw [Submodule.map_span, Set.image_image]
  have he : e ∘ embedCoordinates f = embedCoordinates f ∘ act T :=
    funext (act_map f T)
  simp only [Function.comp_def] at he
  rw [he, ← Set.image_image, h]

private theorem comparison_lattice {K I N : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N ℚ (I → K)) (M M' : Matrix.GeneralLinearGroup N ℚ)
    (T : Matrix.GeneralLinearGroup I K) (L L' : Set (I → K))
    (hM : IsBasisMatrix ℤ b L M) (hM' : IsBasisMatrix ℤ b L' M')
    (hT : ∀ z, act T (inBasis b M' z) = inBasis b M z) :
    act T '' L' = L := by
  rw [inBasis_lattice b L M hM, inBasis_lattice b L' M' hM', ← Set.range_comp]
  apply congrArg Set.range
  funext z
  exact hT _

private abbrev ArchSpace (K I : Type*) [Field K] := ∀ w : NumberField.InfinitePlace K, I → w.Completion

section Archimedean

variable {K I N : Type*} [Field K] [NumberField K] [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N]
    [∀ w : NumberField.InfinitePlace K, Algebra ℝ w.Completion]


private theorem archimedean_basis_action
    (b : Module.Basis N ℚ (I → K)) (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    (hE : ∀ x w, E (embedCoordinates (algebraMap ℚ ℝ) (b.equivFun x)) w =
      embedCoordinates (algebraMap K w.Completion) x)
    (M : Matrix.GeneralLinearGroup N ℚ) (G : Matrix.GeneralLinearGroup N ℝ)
    (g : ∀ w : NumberField.InfinitePlace K, Matrix.GeneralLinearGroup I w.Completion)
    (hG : ∀ z w, E (act G z) w = act (g w) (E z w))
    (z : N → ℚ) (w : NumberField.InfinitePlace K) :
    E (act (G * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M)
        (embedCoordinates (algebraMap ℚ ℝ) z)) w =
      act (g w) (embedCoordinates (algebraMap K w.Completion) (inBasis b M z)) := by
  rw [act_mul, act_map, hG]
  apply congrArg (act (g w))
  have he : b.equivFun (inBasis b M z) = act M z := LinearEquiv.apply_symm_apply _ _
  simpa only [he] using hE (inBasis b M z) w

/-- Transport in real coordinates of a continuous operation on the completed factors. -/
private def realTransport (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    (F : (ArchSpace K I) → (ArchSpace K I) → (ArchSpace K I)) (H : Matrix.GeneralLinearGroup N ℝ) (x y : N → ℝ) : N → ℝ :=
  act H⁻¹ (E.symm (F (E (act H x)) (E (act H y))))

omit [NumberField K] [Fintype I] [DecidableEq I] in
private theorem continuous_realTransport (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    {F : (ArchSpace K I) → (ArchSpace K I) → (ArchSpace K I)} (hF : Continuous fun xy : (ArchSpace K I) × (ArchSpace K I) => F xy.1 xy.2)
    (x y : N → ℝ) : Continuous fun H : Matrix.GeneralLinearGroup N ℝ =>
        realTransport E F H x y := by
  exact continuous_act continuous_inv (E.symm.continuous.comp
    (hF.comp ((E.continuous.comp (continuous_act continuous_id continuous_const)).prodMk
      (E.continuous.comp (continuous_act continuous_id continuous_const)))))

private theorem realTransport_rational
    (b : Module.Basis N ℚ (I → K)) (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    (hE : ∀ x w, E (embedCoordinates (algebraMap ℚ ℝ) (b.equivFun x)) w =
      embedCoordinates (algebraMap K w.Completion) x)
    (M : Matrix.GeneralLinearGroup N ℚ) (G : Matrix.GeneralLinearGroup N ℝ)
    (g : ∀ w : NumberField.InfinitePlace K, Matrix.GeneralLinearGroup I w.Completion)
    (hG : ∀ z w, E (act G z) w = act (g w) (E z w))
    (A : (I → K) → (I → K) → (I → K)) (F : (ArchSpace K I) → (ArchSpace K I) → (ArchSpace K I))
    (hF : ∀ x y w, F (fun v => act (g v) (embedCoordinates (algebraMap K v.Completion) x))
        (fun v => act (g v) (embedCoordinates (algebraMap K v.Completion) y)) w =
      act (g w) (embedCoordinates (algebraMap K w.Completion) (A x y)))
    (j k : N) :
    realTransport E F (G * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M)
        (eVec N j) (eVec N k) =
      embedCoordinates (algebraMap ℚ ℝ)
        ((inBasis b M).symm (A (inBasis b M (eVec N j)) (inBasis b M (eVec N k)))) := by
  let H := G * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M
  have h (z : N → ℚ) : E (act H (embedCoordinates (algebraMap ℚ ℝ) z)) =
      fun w => act (g w) (embedCoordinates (algebraMap K w.Completion) (inBasis b M z)) :=
    funext (archimedean_basis_action b E hE M G g hG z)
  have hr (j : N) : E (act H (eVec N j)) =
      fun w => act (g w) (embedCoordinates (algebraMap K w.Completion) (inBasis b M (eVec N j))) := by
    have he : embedCoordinates (algebraMap ℚ ℝ) (eVec N j) = eVec N j :=
      embed_eVec _ _
    simpa only [he] using h (eVec N j)
  apply (act H).injective
  apply E.injective
  change E (act H (act H⁻¹ (E.symm (F (E (act H (eVec N j))) (E (act H (eVec N k))))))) = _
  rw [show ∀ x, act H (act H⁻¹ x) = x from mulVec_inv_cancel H⁻¹,
    ContinuousLinearEquiv.apply_symm_apply, h, LinearEquiv.apply_symm_apply, hr, hr]
  exact funext (hF _ _)

private theorem compact_detOne_preimage {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] [TopologicalSpace F] [T1Space F] [IsTopologicalRing F]
    (S : Set (Matrix I I F)) (hS : IsCompact S) :
    IsCompact {g : Matrix.GeneralLinearGroup I F | g.val ∈ S ∧ g.det = 1} := by
  let C : Set (Matrix.SpecialLinearGroup I F) := Subtype.val ⁻¹' S
  have hc : IsCompact C := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hS
  have hEq : Matrix.SpecialLinearGroup.toGL '' C =
      {g : Matrix.GeneralLinearGroup I F | g.val ∈ S ∧ g.det = 1} := by
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨hm, Units.ext m.property⟩
    · rintro ⟨hg, hd⟩
      exact ⟨⟨g.val, congrArg Units.val hd⟩, hg, Units.ext rfl⟩
  rw [← hEq]
  exact hc.image Matrix.SpecialLinearGroup.continuous_toGL

private def archimedeanMatrix
    (b : Module.Basis N ℚ (I → K)) (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    (M' : Matrix.GeneralLinearGroup N ℚ) (r : Matrix.GeneralLinearGroup I K)
    (w : NumberField.InfinitePlace K) (H : Matrix.GeneralLinearGroup N ℝ) :
    Matrix I I w.Completion :=
  Matrix.of fun i j => E (act H (embedCoordinates (algebraMap ℚ ℝ)
    ((inBasis b M').symm (act r⁻¹ (eVec I j))))) w i

private theorem continuous_archimedeanMatrix
    (b : Module.Basis N ℚ (I → K)) (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    (M' : Matrix.GeneralLinearGroup N ℚ) (r : Matrix.GeneralLinearGroup I K)
    (w : NumberField.InfinitePlace K) :
    Continuous (archimedeanMatrix b E M' r w) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply i).comp ((continuous_apply w).comp
    (E.continuous.comp (continuous_act continuous_id continuous_const)))

private theorem archimedeanMatrix_eq
    (b : Module.Basis N ℚ (I → K)) (E : (N → ℝ) ≃L[ℝ] (ArchSpace K I))
    (hE : ∀ x w, E (embedCoordinates (algebraMap ℚ ℝ) (b.equivFun x)) w =
      embedCoordinates (algebraMap K w.Completion) x)
    (M M' : Matrix.GeneralLinearGroup N ℚ) (G : Matrix.GeneralLinearGroup N ℝ)
    (g : ∀ w : NumberField.InfinitePlace K, Matrix.GeneralLinearGroup I w.Completion)
    (hG : ∀ z w, E (act G z) w = act (g w) (E z w))
    (T r : Matrix.GeneralLinearGroup I K) (hT : ∀ z, act T (inBasis b M' z) = inBasis b M z)
    (w : NumberField.InfinitePlace K) :
    archimedeanMatrix b E M' r w (G * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M) =
      (g w * Matrix.GeneralLinearGroup.map (algebraMap K w.Completion) (T * r⁻¹)).val := by
  apply Matrix.ext
  intro i j
  let z := (inBasis b M').symm (act r⁻¹ (eVec I j))
  change E (act (G * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M)
    (embedCoordinates (algebraMap ℚ ℝ) z)) w i = _
  let F := Matrix.GeneralLinearGroup.map (n := I) (algebraMap K w.Completion)
  have hz : embedCoordinates (algebraMap K w.Completion) (inBasis b M z) =
      act (F (T * r⁻¹)) (eVec I j) := by
    rw [← hT, show inBasis b M' z = act r⁻¹ (eVec I j) from LinearEquiv.apply_symm_apply _ _,
      ← act_mul, ← act_map]
    exact congrArg (act (F (T * r⁻¹))) (embed_eVec _ _)
  calc
    _ = act (g w) (embedCoordinates (algebraMap K w.Completion) (inBasis b M z)) i :=
      congrFun (archimedean_basis_action b E hE M G g hG z w) i
    _ = act (g w * F (T * r⁻¹)) (eVec I j) i := by rw [hz, act_mul]
    _ = _ := by rw [act_apply, eVec, Matrix.mulVec_single_one, Matrix.col_apply]


end Archimedean

section Operations

variable {K I N : Type*} [Field K] [NumberField K] [Fintype I] [DecidableEq I]
  [Fintype N] [DecidableEq N]

private abbrev OperationIndex (K : Type*) [Field K] [NumberField K] :=
  Option (Module.Free.ChooseBasisIndex ℤ (𝓞 K))

private def rationalOperation (c : I → I → I → K) (t : OperationIndex K) (x y : I → K) :
    I → K :=
  match t with
  | none => bracket c (RingHom.id K) x y
  | some j => NumberField.integralBasis K j • x

private def archimedeanOperation (c : I → I → I → K) (t : OperationIndex K)
    (x y : ArchSpace K I) : ArchSpace K I :=
  fun w => match t with
  | none => bracket c (algebraMap K w.Completion) (x w) (y w)
  | some j => algebraMap K w.Completion (NumberField.integralBasis K j) • x w

private theorem continuous_bracket {X I K F : Type*} [TopologicalSpace X]
    [Fintype I] [CommRing K] [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
    (c : I → I → I → K) (f : K →+* F) {x y : X → I → F}
    (hx : Continuous x) (hy : Continuous y) :
    Continuous fun a => bracket c f (x a) (y a) := by
  apply continuous_pi
  intro i
  change Continuous fun a : X => ∑ j, (∑ k, x a k * f (c k j i)) * y a j
  exact continuous_finsetSum _ fun j _ =>
    (continuous_finsetSum _ fun k _ => ((continuous_apply k).comp hx).mul
      continuous_const).mul ((continuous_apply j).comp hy)

omit [DecidableEq I] in
private theorem continuous_archimedeanOperation (c : I → I → I → K) (t : OperationIndex K) :
    Continuous fun xy : ArchSpace K I × ArchSpace K I => archimedeanOperation c t xy.1 xy.2 := by
  apply continuous_pi
  intro w
  let X := ArchSpace K I × ArchSpace K I
  have hfst : Continuous (fun xy : X => xy.1 w) := (continuous_apply w).comp continuous_fst
  have hsnd : Continuous (fun xy : X => xy.2 w) := (continuous_apply w).comp continuous_snd
  cases t with
  | none =>
    change Continuous (fun xy : X => bracket c (algebraMap K w.Completion) (xy.1 w) (xy.2 w))
    exact continuous_bracket (X := X) (I := I) (F := w.Completion) c
      (algebraMap K w.Completion) hfst hsnd
  | some j =>
    change Continuous (fun xy : X => algebraMap K w.Completion (NumberField.integralBasis K j) •
      xy.1 w)
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_apply i).comp hfst)

private theorem archimedeanOperation_equivariant (c : I → I → I → K)
    (g : ∀ w : NumberField.InfinitePlace K, Matrix.GeneralLinearGroup I w.Completion)
    (hg : ∀ w, PreservesBracket c (algebraMap K w.Completion) (g w))
    (t : OperationIndex K) (x y : I → K) (w : NumberField.InfinitePlace K) :
    archimedeanOperation c t
        (fun v => act (g v) (embedCoordinates (algebraMap K v.Completion) x))
        (fun v => act (g v) (embedCoordinates (algebraMap K v.Completion) y)) w =
      act (g w) (embedCoordinates (algebraMap K w.Completion) (rationalOperation c t x y)) := by
  cases t with
  | none =>
    exact (hg w _ _).trans (congrArg (act (g w)) (bracket_map c _ x y).symm)
  | some j =>
    have he : embedCoordinates (algebraMap K w.Completion) (NumberField.integralBasis K j • x) =
        algebraMap K w.Completion (NumberField.integralBasis K j) •
          embedCoordinates (algebraMap K w.Completion) x := by
      funext i
      exact map_mul _ _ _
    simp only [rationalOperation, archimedeanOperation, act_apply, he, Matrix.mulVec_smul]

private theorem operation_mem_lattice (c : I → I → I → K)
    (hc : ∀ i j k, c i j k ∈ (algebraMap (𝓞 K) K).range)
    (g : ∀ v : NumberFinitePlace K, Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (hg : ∀ v, PreservesBracket c (algebraMap K (v.adicCompletion K)) (g v))
    (t : OperationIndex K) {x y : I → K}
    (hx : x ∈ rationalLatticeIntersection (fun v => localLattice v (g v)))
    (hy : y ∈ rationalLatticeIntersection (fun v => localLattice v (g v))) :
    rationalOperation c t x y ∈ rationalLatticeIntersection (fun v => localLattice v (g v)) := by
  cases t with
  | none => exact bracket_lattice c hc g hg hx hy
  | some j =>
    rw [rationalOperation, NumberField.integralBasis_apply]
    exact Submodule.smul_mem _ (NumberField.RingOfIntegers.basis K j) hx

private def coefficients (b : Module.Basis N ℚ (I → K)) (c : I → I → I → K)
    (M : Matrix.GeneralLinearGroup N ℚ) (s : OperationIndex K × N × N × N) : ℚ :=
  (inBasis b M).symm (rationalOperation c s.1 (inBasis b M (eVec N s.2.1))
    (inBasis b M (eVec N s.2.2.1))) s.2.2.2

private theorem comparison_of_coefficients
    (b : Module.Basis N ℚ (I → K)) (c : I → I → I → K) (M M' : Matrix.GeneralLinearGroup N ℚ)
    (h : coefficients b c M = coefficients b c M') :
    ∃ T : Matrix.GeneralLinearGroup I K, PreservesBracket c (RingHom.id K) T ∧
      ∀ z, act T (inBasis b M' z) = inBasis b M z := by
  apply comparison_preserves b M M' c
  · intro j k
    ext l
    exact congrFun h (none, j, k, l)
  · intro t j
    ext l
    exact congrFun h (some t, j, j, l)

end Operations

private theorem finiteTransfer {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I]
    (v : NumberFinitePlace K) (g g' : Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (T : Matrix.GeneralLinearGroup I K) (L L' : Submodule (𝓞 K) (I → K))
    (h : act T '' (L' : Set (I → K)) = L)
    (hl : completedLattice v L = localLattice v g)
    (hl' : completedLattice v L' = localLattice v g') :
    g * Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) T * g'⁻¹ ∈
      (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype).range := by
  apply (integralMatrixIffPreservesBox (I := I) (v.adicCompletionIntegers K).toSubring _).mpr
  change act _ '' {x : I → v.adicCompletion K | ∀ i, x i ∈ v.adicCompletionIntegers K} =
    {x | ∀ i, x i ∈ v.adicCompletionIntegers K}
  rw [← completedStandard (I := I) v]
  simp only [act_mul, ← Set.image_image]
  change g.val.mulVec '' (act (Matrix.GeneralLinearGroup.map _ T) ''
    (localLattice v g' : Set _)) = _
  rw [← hl', completedLattice_image v T L L' h, hl, localLattice_image]

open private glIntegral_iff glIntegral_compactOpen eventually_outside
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups

private theorem matrix_eventually_integral {K : Type u} [Field K] (D : GlobalFieldData.{u, 0} K)
    {I : Type u} [Fintype I] [DecidableEq I] (r : Matrix.GeneralLinearGroup I K) :
    ∀ᶠ v : D.FinitePlace in cofinite,
      Matrix.GeneralLinearGroup.map (D.embedding (.inl v)) r ∈
        (Matrix.GeneralLinearGroup.map (D.integers v).subtype).range := by
  have h (x : K) : ∀ᶠ v : D.FinitePlace in cofinite, D.embedding (.inl v) x ∈ D.integers v :=
    eventually_cofinite.mpr (D.finite_nonintegral x)
  have h₁ : ∀ᶠ v : D.FinitePlace in cofinite, ∀ i j,
      D.embedding (.inl v) (r.val i j) ∈ D.integers v :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => h _
  have h₂ : ∀ᶠ v : D.FinitePlace in cofinite, ∀ i j,
      D.embedding (.inl v) (r⁻¹.val i j) ∈ D.integers v :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => h _
  filter_upwards [h₁, h₂] with v h₁ h₂
  exact (glIntegral_iff (D.integers v) _).mpr ⟨h₁, h₂⟩

private def pointMatrix {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q)
    (a : Adeles D i ∅) (w : D.Place) :
    Matrix.GeneralLinearGroup (Index.{u} i.size) (D.Completion w) :=
  asMatrix i (D.Completion w) (a ⟨w, Finset.notMem_empty w⟩)

private theorem eventually_integral {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q) (a : Adeles D i ∅) :
    ∀ᶠ v : D.FinitePlace in cofinite,
      pointMatrix D i a (.inl v) ∈ (Matrix.GeneralLinearGroup.map (D.integers v).subtype).range := by
  rw [eventually_cofinite]
  exact (eventually_cofinite.mp a.property).preimage
    (f := fun w => (⟨Sum.inl w, Finset.notMem_empty _⟩ : Outside D ∅))
    (fun _ _ _ _ h => Sum.inl.inj (congrArg Subtype.val h))

private def finiteMatrixBox {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q)
    (a₀ : Adeles D i ∅) (r : Matrix.GeneralLinearGroup (Index.{u} i.size) K)
    (v : D.FinitePlace) : Set (Matrix.GeneralLinearGroup (Index.{u} i.size) (D.Completion (.inl v))) :=
  (fun m => m * (pointMatrix D i a₀ (.inl v) *
    Matrix.GeneralLinearGroup.map (D.embedding (.inl v)) r⁻¹)) ''
    (Set.range (Matrix.GeneralLinearGroup.map (n := Index.{u} i.size) (D.integers v).subtype))

private theorem compact_finiteMatrixBox {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q)
    (a₀ : Adeles D i ∅) (r : Matrix.GeneralLinearGroup (Index.{u} i.size) K) (v : D.FinitePlace) :
    IsCompact (finiteMatrixBox D i a₀ r v) := by
  obtain ⟨hcompact, hopen, _⟩ := D.integers_properties v
  unfold finiteMatrixBox
  exact (glIntegral_compactOpen (ι := Index.{u} i.size) _ hcompact hopen).1.image
    (continuous_id.mul continuous_const)

private theorem compactAdelicBox {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q)
    (a₀ : Adeles D i ∅) (r : Matrix.GeneralLinearGroup (Index.{u} i.size) K)
    (CInf : ∀ w : D.InfinitePlace, Set (Matrix.GeneralLinearGroup (Index.{u} i.size)
      (D.Completion (.inr w))))
    (hc : ∀ w, IsCompact (CInf w)) :
    ∃ C : Set (Adeles D i ∅), IsCompact C ∧ ∀ a : Adeles D i ∅,
      (∀ v, pointMatrix D i a (.inl v) ∈ finiteMatrixBox D i a₀ r v) →
      (∀ w, pointMatrix D i a (.inr w) ∈ CInf w) → a ∈ C := by
  let M (w : D.Place) : Set (Matrix.GeneralLinearGroup (Index.{u} i.size) (D.Completion w)) :=
    match w with
    | .inl v => finiteMatrixBox D i a₀ r v
    | .inr w => CInf w
  let B (w : D.Place) : Set (LocalPoints D i w) := asMatrix i (D.Completion w) ⁻¹' M w
  have hB (w : D.Place) : IsCompact (B w) := by
    apply (localMatrixEmbedding D i w).isCompact_preimage
    cases w with
    | inl v => exact compact_finiteMatrixBox D i a₀ r v
    | inr w => exact hc w
  have hco : ∀ᶠ w : Outside D ∅ in cofinite, B w.1 ⊆ localSubgroup D i w.1 := by
    apply eventually_outside D ∅ (p := fun w => B w ⊆ localSubgroup D i w)
    · filter_upwards [eventually_integral D i a₀, matrix_eventually_integral D r⁻¹] with v ha hr
      rintro x (⟨m, hm, he⟩ : asMatrix i (D.Completion (.inl v)) x ∈ finiteMatrixBox D i a₀ r v)
      change asMatrix i (D.Completion (.inl v)) x ∈
        (Matrix.GeneralLinearGroup.map (D.integers v).subtype).range
      rw [← he]
      exact Subgroup.mul_mem _ hm (Subgroup.mul_mem _ ha hr)
    · intro w x _
      exact Subgroup.mem_top _
  let C := {a : Adeles D i ∅ | ∀ w : Outside D ∅, a w ∈ B w.1}
  have hC : IsCompact C := compactRestrictedProductBox _ _ (fun w => hB w.1) hco
  refine ⟨C, hC, fun a hf hi w => ?_⟩
  obtain ⟨w, hw⟩ := w
  cases w with
  | inl v => exact hf v
  | inr w => exact hi w

private theorem pointMatrix_mul_diagonal {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q) (a : Adeles D i ∅)
    (γ : RationalPoints Q) (w : D.Place) :
    pointMatrix D i (a * diagonal D i ∅ γ) w =
      pointMatrix D i a w * Matrix.GeneralLinearGroup.map (D.embedding w) (i.onPoints γ) := by
  change asMatrix i (D.Completion w) (_ * localPoint D i w γ) = _
  rw [map_mul, localPoint_matrix]
  rfl

private abbrev adelicSpace {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q) :
    TopologicalSpace (Adeles D i ∅) := inferInstance

/-- Bounded rational bases and the finite bracket comparison give compact representatives
in the original restricted product. -/
theorem latticeComparison : Specs.BracketLatticeCompactness.latticeComparison.{u, v, w} := by
  classical
  intro K _ hK Q i D I c P J _ _ p d r hdet hbr hp hpinv hpnonzero hcosets
  let A := Adeles D i ∅
  let (w : D.Place) : Field (D.Completion w) := GlobalFieldData.instFieldCompletion D w
  let _ : TopologicalSpace A := adelicSpace D i
  let N := Fin (Module.finrank ℚ (I → K))
  let L₀ := matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)
  let _ : Submodule.IsLattice K L₀ := isLattice_matrixLattice (R := 𝓞 K) _
  -- Scale the bracket and the invariants to be integral on the reference lattice.
  obtain ⟨t, ht, hc⟩ := clearDenominators (K := K) (Finset.univ : Finset (I × I × I))
    (fun s => c s.1 s.2.1 s.2.2)
  let c' (i j k : I) := t * c i j k
  have hc' (i j k : I) : c' i j k ∈ (algebraMap (𝓞 K) K).range :=
    hc (i, j, k) (Finset.mem_univ _)
  have hbr' : LocalBracketInvariant D i c' := by
    intro w x
    exact (preservesBracket_scale c (D.embedding w) t ht _).mpr (hbr w x)
  choose m hm hmint using fun j => normalizePolynomial (p j)
  let p' (j : P) := m j • p j
  have hphom (j : P) : 0 < d j ∧ (p' j).IsHomogeneous (d j) := by
    refine ⟨(hp j).1, ?_⟩
    rw [show p' j = MvPolynomial.C (m j) * p j from MvPolynomial.C_mul'.symm]
    exact (hp j).2.C_mul (m j)
  have hpint : IntegralOnReference L₀ p' := by
    intro j v y hy
    apply hmint j v y
    change y ∈ (completedLattice v L₀ : Set _) at hy
    exact (completedStandard (I := I) v ▸ hy : y ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers K})
  have hpinv' (j : P) : LocalPolynomialInvariant D i (p' j) := by
    intro w x y
    change (m j • p j).eval₂ (D.embedding w) _ = _
    simp only [eval₂_smul, p']
    rw [hpinv j w x]
  have hpnonzero' (x : I → K) (hx : x ≠ 0) : ∃ j, (p' j).eval x ≠ 0 := by
    obtain ⟨j, hj⟩ := hpnonzero x hx
    exact ⟨j, by rw [show p' j = m j • p j from rfl, MvPolynomial.smul_eval];
                 exact mul_ne_zero (hm j) hj⟩
  let g (a : A) (v : NumberFinitePlace K) :
      Matrix.GeneralLinearGroup I (v.adicCompletion K) := pointMatrix D i a (.inl v)
  let gInf (a : A) (w : NumberField.InfinitePlace K) :
      Matrix.GeneralLinearGroup I w.Completion := pointMatrix D i a (.inr w)
  let Qv (a : A) (v : NumberFinitePlace K) := localLattice v (g a v)
  let L (a : A) := rationalLatticeIntersection (Qv a)
  have hQv (a : A) : {v | Qv a v ≠ completedLattice v L₀}.Finite := by
    apply eventually_cofinite.mp
    filter_upwards [eventually_integral D i a] with v hv
    exact localLattice_eq_of_integral v (g a v) hv
  obtain ⟨b, alg, E, _, hE, _, _, C, _, _, hC, hbound⟩ :=
    numberAdelicLatticeBounds (I := I) L₀ p' d hphom hpint
  let := alg
  have obtainBasis (a : A) :
      ∃ (G : Matrix.GeneralLinearGroup N ℝ) (M : Matrix.GeneralLinearGroup N ℚ),
        LatticeIntersectionConclusion (B := ℤ) L₀ (Qv a) ∧
        (∀ z w, E (act G z) w = act (gInf a w) (E z w)) ∧
        IsBasisMatrix ℤ b (L a : Set _) M ∧
        G * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M ∈ Prod.snd '' C := by
    obtain ⟨hrecover, _, _, h⟩ := hbound (Qv a) (hQv a)
    obtain ⟨Gfin, G, M, hI, _, _, hact, hbasis, _, _, _, _, _, _, hmem⟩ :=
      h (g a) (gInf a)
        (fun v => hdet _ _) (fun v => localLattice_image v (g a v))
        (fun w => hdet _ _) (fun j v y => hpinv' j (.inl v) _ y)
        (fun j w y => hpinv' j (.inr w) _ y)
        (fun x _ hx => hpnonzero' x hx)
    exact ⟨G, M, hrecover, hact, hbasis, ⟨(finiteBasisRepresentative Gfin M hI, _), hmem, rfl⟩⟩
  choose G M hRec hAct hBas hComp using obtainBasis
  have hcompletion (a : A) (v : NumberFinitePlace K) :
      completedLattice v (L a) = localLattice v (g a v) := by
    obtain ⟨_, _, _, _, _, h⟩ := hRec a
    exact (h v).2.2.2
  let R : Set (Matrix.GeneralLinearGroup N ℝ) := Prod.snd '' C
  have hR : IsCompact R := hC.image continuous_snd
  let TIndex := OperationIndex K × N × N × N
  let evalReal (s : TIndex) (H : Matrix.GeneralLinearGroup N ℝ) : ℝ :=
    realTransport E (archimedeanOperation c' s.1) H (eVec N s.2.1) (eVec N s.2.2.1) s.2.2.2
  have evalContinuous (s : TIndex) : Continuous (evalReal s) :=
    (continuous_apply _).comp
      (continuous_realTransport E (continuous_archimedeanOperation c' s.1) _ _)
  -- Each rational coefficient lies in the integers and in a fixed compact real set.
  have hFinite : (Set.range fun a : A => coefficients b c' (M a)).Finite := by
    apply finite_rational_range _ (fun s => evalReal s '' R) (fun s => hR.image (evalContinuous s))
    · intro a s
      refine ⟨_, hComp a, ?_⟩
      exact congrFun (realTransport_rational b E hE (M a) (G a) (gInf a) (hAct a)
        (rationalOperation c' s.1) (archimedeanOperation c' s.1)
        (archimedeanOperation_equivariant c' (gInf a)
          (fun w => hbr' (.inr w) _) s.1) s.2.1 s.2.2.1) s.2.2.2
    · intro a s
      have hin := operation_mem_lattice c' hc' (g a) (fun v => hbr' (.inl v) _) s.1
        (inBasis_eVec_mem (hBas a) s.2.1) (inBasis_eVec_mem (hBas a) s.2.2.1)
      obtain ⟨z, hz⟩ := inBasis_integral (hBas a) hin
      exact ⟨z s.2.2.2, hz s.2.2.2⟩
  let S := Set.range fun a : A => coefficients b c' (M a)
  let _ : Finite S := hFinite.to_subtype
  let label (a : A) : S := ⟨coefficients b c' (M a), ⟨a, rfl⟩⟩
  let rep (s : S) : A := s.property.choose
  have hrep (a : A) : coefficients b c' (M a) = coefficients b c' (M (rep (label a))) :=
    (label a).property.choose_spec.symm
  -- Each pair gives a box in the original local groups.
  let B (s : S) (j : J) (w : NumberField.InfinitePlace K) :=
    {z : Matrix.GeneralLinearGroup I w.Completion |
      z.val ∈ archimedeanMatrix b E (M (rep s)) (r j) w '' R ∧ z.det = 1}
  have hB (s : S) (j : J) (w : D.InfinitePlace) : IsCompact (B s j w) :=
    compact_detOne_preimage _ (hR.image (continuous_archimedeanMatrix b E (M (rep s)) (r j) w))
  choose Cbox hCbox hmem using fun s j => compactAdelicBox D i (rep s) (r j) (B s j) (hB s j)
  let CC : Set A := ⋃ s, ⋃ j, Cbox s j
  refine ⟨CC, isCompact_iUnion (fun s => isCompact_iUnion (hCbox s)), ?_⟩
  intro a
  let s := label a
  let a₀ := rep s
  obtain ⟨T, hT, hTact⟩ := comparison_of_coefficients b c' (M a) (M a₀) (hrep a)
  obtain ⟨γ, j, hγ⟩ := hcosets T ((preservesBracket_scale c (RingHom.id K) t ht T).mp hT)
  have hTr : T * (r j)⁻¹ = i.onPoints γ := by rw [hγ, mul_inv_cancel_right]
  let a' := a * diagonal D i ∅ γ
  have hright (w : D.Place) :
      pointMatrix D i a' w =
        pointMatrix D i a w * Matrix.GeneralLinearGroup.map (D.embedding w) (T * (r j)⁻¹) := by
    rw [hTr]
    exact pointMatrix_mul_diagonal D i a γ w
  refine ⟨γ, a', mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨j, hmem s j a' ?_ ?_⟩⟩, ?_⟩
  · intro v
    let F := Matrix.GeneralLinearGroup.map (n := I) (algebraMap K (v.adicCompletion K))
    have hL := comparison_lattice b (M a) (M a₀) T _ _ (hBas a) (hBas a₀) hTact
    have hfin := finiteTransfer v (g a v) (g a₀ v) T (L a) (L a₀) hL
      (hcompletion a v) (hcompletion a₀ v)
    refine ⟨g a v * F T * (g a₀ v)⁻¹, hfin, ?_⟩
    rw [hright]
    change (g a v * F T * (g a₀ v)⁻¹) * (g a₀ v * F (r j)⁻¹) = g a v * F (T * (r j)⁻¹)
    rw [map_mul]
    group
  · intro w
    constructor
    · refine ⟨_, hComp a, ?_⟩
      rw [hright]
      exact archimedeanMatrix_eq b E hE (M a) (M a₀) (G a) (gInf a) (hAct a) T (r j) hTact w
    · exact hdet (.inr w) _
  · intro w
    exact congrArg (a w * ·) (diagonalCoordinates D i ∅ γ w)

end

end LinearAlgebraicGroups.Arithmetic.BracketLatticeCompactness
