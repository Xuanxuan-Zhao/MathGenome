import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyBasis
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactConjugation
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Basis.Submodule

open scoped ComplexConjugate BigOperators

namespace LieAlgebrasAndRepresentations.CompactConjugation

open Specs.LieAlgebrasAndRepresentations.CompactConjugation
open Specs.LieAlgebrasAndRepresentations.ChevalleyBasis (Root)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive simple)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Module

attribute [local instance] realLieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

private noncomputable def coordinateConjugation {ι : Type*} (b : Basis ι ℂ L) :
    ConjugateMap L :=
  b.repr.symm.toLinearMap.comp
    ((Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ)).toLinearMap.comp
      b.repr.toLinearMap)

private theorem repr_coordinateConjugation {ι : Type*} (b : Basis ι ℂ L) (v : L) (i : ι) :
    b.repr (coordinateConjugation b v) i = conj (b.repr v i) := by
  simp [coordinateConjugation, Finsupp.mapRange.linearMap_apply]

private theorem coordinateConjugation_basis {ι : Type*} (b : Basis ι ℂ L) (i : ι) :
    coordinateConjugation b (b i) = b i := by
  classical
  apply b.ext_elem
  intro j
  rw [repr_coordinateConjugation, b.repr_self_apply]
  split <;> simp

private theorem coordinateConjugation_lie {ι : Type*} (b : Basis ι ℂ L)
    (hb : ∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)) :
    PreservesBracket (coordinateConjugation b) := by
  let J := coordinateConjugation b
  let A := (LieAlgebra.ad ℂ L).toLinearMap
  have he : A.compr₂ₛₗ J = ((A.compl₂ J).flip.compl₂ J).flip := by
    apply LinearMap.ext_basis b b
    intro i j
    change J ⁅b i, b j⁆ = ⁅J (b i), J (b j)⁆
    rw [coordinateConjugation_basis, coordinateConjugation_basis]
    apply b.ext_elem
    intro k
    obtain ⟨z, hz⟩ := hb i j k
    rw [repr_coordinateConjugation, hz, map_intCast]
  intro v w
  exact congrArg (fun f : L →ₗ⋆[ℂ] L →ₗ⋆[ℂ] L => f v w) he

private theorem involutive_of_basis {ι : Type*} (b : Basis ι ℂ L) (τ : ConjugateMap L)
    (h : ∀ i, τ (τ (b i)) = b i) : Function.Involutive τ := by
  have he : τ.comp τ = (LinearMap.id : L →ₗ[ℂ] L) := b.ext h
  intro v
  exact congrArg (fun f : L →ₗ[ℂ] L => f v) he

private theorem opposite_involutive {H : LieSubalgebra ℂ L}
    (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H) :
    Function.Involutive (opposite negRoot) :=
  fun α => Subtype.ext (neg_neg α.val)

private noncomputable def rootPairs {H : LieSubalgebra ℂ L} {φ : Module.Dual ℂ H →ₗ[ℝ] ℝ}
    (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)
    (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H) :
    (PositiveRoot H φ ⊕ PositiveRoot H φ) ≃ Root H := by
  classical
  let f : (PositiveRoot H φ ⊕ PositiveRoot H φ) → Root H :=
    Sum.elim asRoot (opposite negRoot ∘ asRoot)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro (a | a) (b | b) h
    · have hab : a.val = b.val := congrArg (fun a : Root H => a.val) h
      exact congrArg Sum.inl (Subtype.ext hab)
    · have hab : a.val = -b.val := congrArg (fun a : Root H => a.val) h
      have ha := a.property.2
      rw [hab, map_neg, neg_pos] at ha
      exact (not_lt_of_gt b.property.2 ha).elim
    · have hab : b.val = -a.val := congrArg (fun a : Root H => a.val) h.symm
      have hb := b.property.2
      rw [hab, map_neg, neg_pos] at hb
      exact (not_lt_of_gt a.property.2 hb).elim
    · have hab : -a.val = -b.val := congrArg (fun a : Root H => a.val) h
      exact congrArg Sum.inr (Subtype.ext (neg_injective hab))
  · intro a
    by_cases ha : 0 < φ a.val
    · exact ⟨.inl ⟨a.val, a.property, ha⟩, rfl⟩
    · have hn : 0 < φ (-a.val) := by
        rw [map_neg, neg_pos]
        exact lt_of_le_of_ne (le_of_not_gt ha) (hφ a.val a.property)
      refine ⟨.inr ⟨-a.val, negRoot a, hn⟩, ?_⟩
      exact Subtype.ext (neg_neg a.val)

private theorem rootPairs_pos {H : LieSubalgebra ℂ L} {φ : Module.Dual ℂ H →ₗ[ℝ] ℝ}
    (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)
    (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H) (a : PositiveRoot H φ) :
    rootPairs hφ negRoot (.inl a) = asRoot a := rfl

private theorem rootPairs_neg {H : LieSubalgebra ℂ L} {φ : Module.Dual ℂ H →ₗ[ℝ] ℝ}
    (hφ : ∀ α ∈ rootSet_value H, φ α ≠ 0)
    (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H) (a : PositiveRoot H φ) :
    rootPairs hφ negRoot (.inr a) = opposite negRoot (asRoot a) := rfl

private noncomputable def compactComplexBasis {S P : Type*}
    (b : Basis (S ⊕ (P ⊕ P)) ℂ L) : Basis (S ⊕ (P ⊕ P)) ℂ L := by
  let v : S ⊕ (P ⊕ P) → L
    | .inl i => Complex.I • b (.inl i)
    | .inr (.inl a) => b (.inr (.inl a)) - b (.inr (.inr a))
    | .inr (.inr a) => Complex.I • (b (.inr (.inl a)) + b (.inr (.inr a)))
  let w : S ⊕ (P ⊕ P) → L
    | .inl i => (-Complex.I) • b (.inl i)
    | .inr (.inl a) => (2 : ℂ)⁻¹ • (b (.inr (.inl a)) - Complex.I • b (.inr (.inr a)))
    | .inr (.inr a) => (2 : ℂ)⁻¹ • (-b (.inr (.inl a)) - Complex.I • b (.inr (.inr a)))
  let f := b.constr ℂ v
  let g := b.constr ℂ w
  have hfg : f.comp g = LinearMap.id := by
    apply b.ext
    rintro (i | (a | a)) <;>
      simp only [f, g, LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply,
        v, w, map_smul, map_sub, map_neg] <;>
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
  have hgf : g.comp f = LinearMap.id := by
    apply b.ext
    rintro (i | (a | a)) <;>
      simp only [f, g, LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply,
        v, w, map_smul, map_add, map_sub] <;>
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
  exact b.map (LinearEquiv.ofLinearMap f g hfg hgf)

private theorem compactComplexBasis_cartan {S P : Type*}
    (b : Basis (S ⊕ (P ⊕ P)) ℂ L) (i : S) :
    compactComplexBasis b (.inl i) = Complex.I • b (.inl i) := by
  simp [compactComplexBasis, Basis.constr_basis]

private theorem compactComplexBasis_difference {S P : Type*}
    (b : Basis (S ⊕ (P ⊕ P)) ℂ L) (a : P) :
    compactComplexBasis b (.inr (.inl a)) = b (.inr (.inl a)) - b (.inr (.inr a)) := by
  simp [compactComplexBasis, Basis.constr_basis]

private theorem compactComplexBasis_sum {S P : Type*}
    (b : Basis (S ⊕ (P ⊕ P)) ℂ L) (a : P) :
    compactComplexBasis b (.inr (.inr a)) = Complex.I • (b (.inr (.inl a)) + b (.inr (.inr a))) := by
  simp [compactComplexBasis, Basis.constr_basis]

private theorem span_eq_fixed {ι : Type*} (b : Basis ι ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hb : ∀ i, τ (b i) = b i) :
    Submodule.span ℝ (Set.range b) = (fixed τ hτ).toSubmodule := by
  have he : coordinateConjugation b = τ :=
    b.ext (fun i => (coordinateConjugation_basis b i).trans (hb i).symm)
  ext v
  rw [b.mem_span_iff_repr_mem ℝ]
  change (∀ i, b.repr v i ∈ Set.range (algebraMap ℝ ℂ)) ↔ τ v = v
  rw [← he, b.ext_elem_iff]
  constructor
  · intro hv i
    obtain ⟨r, hr⟩ := hv i
    rw [repr_coordinateConjugation, ← hr, Complex.coe_algebraMap, Complex.conj_ofReal]
  · intro hv i
    have hi := hv i
    rw [repr_coordinateConjugation] at hi
    refine ⟨(b.repr v i).re, Complex.ext (by simp) ?_⟩
    have him := congrArg Complex.im hi
    simp only [Complex.conj_im] at him
    simp only [Complex.coe_algebraMap, Complex.ofReal_im]
    linarith

private noncomputable def fixedBasis {ι : Type*} (b : Basis ι ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hb : ∀ i, τ (b i) = b i) :
    Basis ι ℝ (fixed τ hτ) :=
  (b.restrictScalars ℝ).map (LinearEquiv.ofEq _ _ (span_eq_fixed b τ hτ hb))

private theorem fixedBasis_apply {ι : Type*} (b : Basis ι ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hb : ∀ i, τ (b i) = b i) (i : ι) :
    (fixedBasis b τ hτ hb i : L) = b i := by
  rw [fixedBasis, Basis.map_apply]
  exact b.restrictScalars_apply ℝ i

private theorem fixedBasis_repr {ι : Type*} (b : Basis ι ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hb : ∀ i, τ (b i) = b i)
    (v : fixed τ hτ) (i : ι) :
    ((fixedBasis b τ hτ hb).repr v i : ℂ) = b.repr (v : L) i := by
  let e := LinearEquiv.ofEq _ _ (span_eq_fixed b τ hτ hb)
  change (algebraMap ℝ ℂ) ((b.restrictScalars ℝ).repr (e.symm v) i) = b.repr (v : L) i
  exact b.restrictScalars_repr_apply ℝ (e.symm v) i

private theorem killing_fixed {ι : Type*} [Fintype ι] (b : Basis ι ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hb : ∀ i, τ (b i) = b i)
    (v w : fixed τ hτ) :
    _root_.killingForm ℂ L (v : L) (w : L) = (_root_.killingForm ℝ (fixed τ hτ) v w : ℂ) := by
  classical
  rw [killingForm_apply_apply, killingForm_apply_apply,
    LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.trace_eq_matrix_trace ℝ (fixedBasis b τ hτ hb)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    LieAlgebra.ad_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fixedBasis_repr]
  simp only [LieSubalgebra.coe_bracket, fixedBasis_apply]

private theorem hermitian_apply (τ : ConjugateMap L) (v w : L) :
    hermitian τ v w = -_root_.killingForm ℂ L v (τ w) := rfl

private theorem hermitian_symm {ι : Type*} [Fintype ι] (b : Basis ι ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hb : ∀ i, τ (b i) = b i) :
    ∀ v w, hermitian τ v w = conj (hermitian τ w v) := by
  let A := hermitian τ
  let J := (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ).toLinearMap
  have he : A = A.flip.compr₂ₛₗ J := by
    apply LinearMap.ext_basis b b
    intro i j
    change hermitian τ (b i) (b j) = conj (hermitian τ (b j) (b i))
    simp only [hermitian_apply, hb]
    let u : fixed τ hτ := ⟨b i, hb i⟩
    let v : fixed τ hτ := ⟨b j, hb j⟩
    change -_root_.killingForm ℂ L (u : L) (v : L) = conj (-_root_.killingForm ℂ L (v : L) (u : L))
    rw [killing_fixed b τ hτ hb u v, killing_fixed b τ hτ hb v u,
      map_neg, Complex.conj_ofReal, LieModule.traceForm_comm ℝ _ _ u v]
  intro v w
  exact congrArg (fun f : L →ₗ[ℂ] L →ₗ⋆[ℂ] ℂ => f v w) he

private theorem hermitian_positive (τ : ConjugateMap L) (hτ : PreservesBracket τ)
    (hi : Function.Involutive τ)
    (hB : ∀ v w : fixed τ hτ,
      _root_.killingForm ℂ L (v : L) (w : L) = (_root_.killingForm ℝ (fixed τ hτ) v w : ℂ))
    (hn : ∀ v : fixed τ hτ, v ≠ 0 → _root_.killingForm ℝ (fixed τ hτ) v v < 0)
    (v : L) (hv : v ≠ 0) :
    0 < (hermitian τ v v).re := by
  let ur := (2 : ℂ)⁻¹ • (v + τ v)
  let wr := (-Complex.I / 2) • (v - τ v)
  have hm (a : ℂ) (z : L) : τ (a • z) = conj a • τ z := map_smulₛₗ τ a z
  have hu : τ ur = ur := by
    simp [ur, hm, hi v, map_ofNat, add_comm]
  have hw : τ wr = wr := by
    simp only [wr, hm, map_sub, hi v, map_div₀, map_neg, Complex.conj_I, neg_neg,
      map_ofNat]
    module
  let u : fixed τ hτ := ⟨ur, hu⟩
  let w : fixed τ hτ := ⟨wr, hw⟩
  have hvw : v = (u : L) + Complex.I • (w : L) := by
    change v = ur + Complex.I • wr
    dsimp [ur, wr]
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
  have hdiag (a : fixed τ hτ) : _root_.killingForm ℝ (fixed τ hτ) a a ≤ 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hn a ha).le
  have hsum : _root_.killingForm ℝ (fixed τ hτ) u u + _root_.killingForm ℝ (fixed τ hτ) w w < 0 := by
    by_cases hz : u = 0
    · have hzw : w ≠ 0 := fun hw0 => hv (by simp [hvw, hz, hw0])
      linarith [hdiag u, hn w hzw]
    · linarith [hn u hz, hdiag w]
  have ht : τ v = (u : L) + (-Complex.I) • (w : L) := by
    rw [hvw, map_add, hm Complex.I, Complex.conj_I, show τ (u : L) = (u : L) from hu,
      show τ (w : L) = (w : L) from hw]
  rw [hermitian_apply, ht, hvw]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB, Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_im, Complex.add_im, Complex.mul_im]
  nlinarith

private theorem negative_of_blocks {S Q M : Type*} [Fintype S] [Fintype Q]
    [AddCommGroup M] [Module ℝ M] (b : Basis (S ⊕ Q) ℝ M)
    (B : LinearMap.BilinForm ℝ M)
    (hsym : ∀ v w, B v w = B w v)
    (hS : ∀ (a : S → ℝ), (∑ i, a i • b (.inl i)) ≠ 0 →
      B (∑ i, a i • b (.inl i)) (∑ i, a i • b (.inl i)) < 0)
    (hSQ : ∀ i j, B (b (.inl i)) (b (.inr j)) = 0)
    (hQ : ∀ i j, i ≠ j → B (b (.inr i)) (b (.inr j)) = 0)
    (hdiag : ∀ i, B (b (.inr i)) (b (.inr i)) < 0)
    (v : M) (hv : v ≠ 0) : B v v < 0 := by
  classical
  let a (i : S) := b.repr v (.inl i)
  let z (j : Q) := b.repr v (.inr j)
  let p := ∑ i, a i • b (.inl i)
  let q := ∑ j, z j • b (.inr j)
  have hsplit : v = p + q := by
    simpa only [Fintype.sum_sum_type, p, q, a, z] using (b.sum_repr v).symm
  have horth (j : Q) : B p (b (.inr j)) = 0 := by
    simp [p, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hSQ]
  have horthq : B p q = 0 := by
    simp [q, map_sum, map_smul, horth]
  have hqq : B q q = ∑ j, z j ^ 2 * B (b (.inr j)) (b (.inr j)) := by
    simp only [q, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · ring
    · intro j _ hj
      rw [hQ j i hj, mul_zero]
    · simp
  have hnonpos : ∀ j, z j ^ 2 * B (b (.inr j)) (b (.inr j)) ≤ 0 :=
    fun j => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hdiag j).le
  have hsum := Finset.sum_nonpos (fun j (_ : j ∈ (Finset.univ : Finset Q)) => hnonpos j)
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply, horthq, hsym q p, hqq, add_zero, zero_add]
  by_cases hp : p = 0
  · have hz : ∃ j, z j ≠ 0 := by
      by_contra! hz
      apply hv
      simpa [hp, q, hz] using hsplit
    obtain ⟨j, hj⟩ := hz
    have hj' : z j ^ 2 * B (b (.inr j)) (b (.inr j)) < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hj) (hdiag j)
    have hle := Finset.sum_le_sum_of_subset_of_nonpos
      (f := fun j => z j ^ 2 * B (b (.inr j)) (b (.inr j)))
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ j)) (fun j _ _ => hnonpos j)
    simpa [hp] using lt_of_le_of_lt hle (by simpa using hj')
  · exact add_neg_of_neg_of_nonpos (hS a hp) hsum

section RootCalculations

open Specs.LieAlgebrasAndRepresentations.RealRootSpace (Realization realCartan realKilling killing)

variable [FiniteDimensional ℂ L] {H : LieSubalgebra ℂ L}

private theorem coroot_in_realCartan (α : Root H) : coroot_value H α.val ∈ realCartan H :=
  Submodule.subset_span ⟨α.val, α.property, rfl⟩

private theorem positive_pairing (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (R : Realization H) (α : Root H) {e f : L}
    (hf : f ∈ rootSpace H (-α.val))
    (hef : ⁅e, f⁆ = (coroot_value H α.val : L)) :
    ∃ k : ℝ, 0 < k ∧ _root_.killingForm ℂ L e f = (k : ℂ) := by
  let h : realCartan H := ⟨coroot_value H α.val, coroot_in_realCartan α⟩
  have heval : α.val (h : H) = 2 := by
    change α.val (killingCoroot H α.val) = 2
    rw [killingCoroot_pairing hss H hH, mul_div_cancel_right₀ _ (rootForm_self_ne_zero hss H hH _ α.property)]
  have hn : h ≠ 0 := by
    intro hz
    rw [hz] at heval
    norm_num at heval
  have hbr : ⁅f, (h : H).val⁆ = (2 : ℂ) • f := by
    rw [← lie_skew, (mem_rootSpace H (-α.val) f).mp hf, LinearMap.neg_apply, heval,
      neg_smul, neg_neg]
  have hB : (realKilling H h h : ℂ) = (2 : ℂ) * _root_.killingForm ℂ L e f := by
    rw [← R.killing_restrict_real h h]
    change _root_.killingForm ℂ L (h : H).val (h : H).val = _
    conv_lhs => arg 1; rw [show (h : H).val = ⁅e, f⁆ from hef.symm]
    rw [LieModule.traceForm_apply_lie_apply, hbr, map_smul, smul_eq_mul]
  refine ⟨realKilling H h h / 2, div_pos (R.killing_positive h hn) (by norm_num), ?_⟩
  push_cast
  linear_combination -hB / 2

private theorem killing_cartan_root (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (h : H) (α : Root H) (x : L) (hx : x ∈ rootSpace H α.val) :
    _root_.killingForm ℂ L (h : L) x = 0 := by
  apply rootSpace_killing_orthogonal H 0 α.val (h : L) x _ hx
  · simpa using α.property.1
  · rw [rootSpace_zero hss H hH]
    exact h.property

set_option maxHeartbeats 800000 in
private theorem positiveRoot_pairing_blocks
    {φ : Module.Dual ℂ H →ₗ[ℝ] ℝ}
    (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H) (x : Root H → L)
    (hx : ∀ a, x a ∈ rootSpace H a.val) (k : PositiveRoot H φ → ℝ)
    (hk : ∀ a, _root_.killingForm ℂ L (x (asRoot a)) (x (opposite negRoot (asRoot a))) = (k a : ℂ)) :
    let B := _root_.killingForm ℂ L
    let e := fun a => x (asRoot a)
    let f := fun a => x (opposite negRoot (asRoot a))
    let d := fun a => e a - f a
    let s := fun a => Complex.I • (e a + f a)
    (∀ a b, B (d a) (s b) = 0) ∧
    (∀ a b, a ≠ b → B (d a) (d b) = 0 ∧ B (s a) (s b) = 0) ∧
    (∀ a, B (d a) (d a) = (-(2 * k a) : ℝ) ∧ B (s a) (s a) = (-(2 * k a) : ℝ)) := by
  classical
  dsimp only
  let B := _root_.killingForm ℂ L
  let e := fun a : PositiveRoot H φ => x (asRoot a)
  let f := fun a : PositiveRoot H φ => x (opposite negRoot (asRoot a))
  have hee (a b : PositiveRoot H φ) : B (e a) (e b) = 0 := by
    apply rootSpace_killing_orthogonal H a.val b.val (e a) (e b) (hx (asRoot a)) (hx (asRoot b))
    intro h
    have hh := congrArg φ h
    rw [map_add, map_zero] at hh
    linarith [a.property.2, b.property.2]
  have hff (a b : PositiveRoot H φ) : B (f a) (f b) = 0 := by
    apply rootSpace_killing_orthogonal H (-a.val) (-b.val) (f a) (f b)
      (hx (opposite negRoot (asRoot a))) (hx (opposite negRoot (asRoot b)))
    intro h
    have hh := congrArg φ h
    simp only [map_add, map_neg, map_zero] at hh
    linarith [a.property.2, b.property.2]
  have hef (a b : PositiveRoot H φ) (hab : a ≠ b) : B (e a) (f b) = 0 := by
    apply rootSpace_killing_orthogonal H a.val (-b.val) (e a) (f b) (hx (asRoot a)) (hx (opposite negRoot (asRoot b)))
    rw [← sub_eq_add_neg]
    exact sub_ne_zero.mpr (fun hh => hab (Subtype.ext hh))
  have hfe (a b : PositiveRoot H φ) : B (f a) (e b) = B (e b) (f a) :=
    LieModule.traceForm_comm ℂ L L _ _
  change (∀ a b, B (e a - f a) (Complex.I • (e b + f b)) = 0) ∧
    (∀ a b, a ≠ b → B (e a - f a) (e b - f b) = 0 ∧
      B (Complex.I • (e a + f a)) (Complex.I • (e b + f b)) = 0) ∧
    (∀ a, B (e a - f a) (e a - f a) = _ ∧
      B (Complex.I • (e a + f a)) (Complex.I • (e a + f a)) = _)
  have hdiag (a : PositiveRoot H φ) : B (e a) (f a) = (k a : ℂ) := hk a
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    by_cases hab : a = b
    · subst b
      simp [map_sub, map_add, map_smul, LinearMap.sub_apply, hee, hff, hfe, hdiag]
    · simp [map_sub, map_add, map_smul, LinearMap.sub_apply, hee, hff, hfe, hef a b hab, hef b a (fun h => hab h.symm)]
  · intro a b hab
    simp [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, hee, hff, hfe, hef a b hab, hef b a (fun h => hab h.symm)]
  · intro a
    constructor <;>
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hee, hff, hfe, hdiag, smul_eq_mul,
        Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat] <;>
      ring_nf
    norm_num [Complex.I_sq]

end RootCalculations

open Specs.LieAlgebrasAndRepresentations.RealRootSpace (Realization realCartan realKilling killing)

set_option maxHeartbeats 1000000 in
theorem construction :
    Specs.LieAlgebrasAndRepresentations.CompactConjugation.constructionType.{u} := by
  classical
  intro L _ _ _ hss H hH φ hφ
  obtain ⟨negRoot, x, N, σ, b, hx, hxf, hσ, hσH, hσx, _, _, hbH, hbx, hbInt, _⟩ :=
    @LieAlgebrasAndRepresentations.chevalley_basis L _ _ _ hss H hH φ hφ
  have R := RealRootSpace.realization_of_maximalToral hss H hH
  let τ : ConjugateMap L := σ.toLinearEquiv.toLinearMap.comp (coordinateConjugation b)
  have hτ : PreservesBracket τ := by
    intro v w
    change σ (coordinateConjugation b ⁅v, w⁆) =
      ⁅σ (coordinateConjugation b v), σ (coordinateConjugation b w)⁆
    rw [coordinateConjugation_lie b hbInt v w, σ.map_lie]
  have hτb (i : simple H φ ⊕ Root H) : τ (b i) = σ (b i) := by
    change σ (coordinateConjugation b (b i)) = σ (b i)
    rw [coordinateConjugation_basis]
  have hτH (i : simple H φ) : τ (coroot_value H i.val : L) = -(coroot_value H i.val : L) := by
    rw [← hbH i, hτb, hbH, hσH]
  have hτx (a : Root H) : τ (x a) = -x (opposite negRoot a) := by
    rw [← hbx a, hτb, hbx]
    exact hσx a
  have hττ : Function.Involutive τ := by
    apply involutive_of_basis b τ
    rintro (i | a)
    · rw [hbH, hτH, map_neg, hτH, neg_neg]
    · rw [hbx, hτx, map_neg, hτx, neg_neg, opposite_involutive]
  let E := Equiv.sumCongr (Equiv.refl (simple H φ)) (rootPairs hφ negRoot)
  let bp := b.reindex E.symm
  have hbpH (i : simple H φ) : bp (.inl i) = (coroot_value H i.val : L) := by
    simpa only [bp, Basis.reindex_apply, E, Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.refl_apply] using hbH i
  have hbpp (a : PositiveRoot H φ) : bp (.inr (.inl a)) = x (asRoot a) := by
    simpa only [bp, Basis.reindex_apply, E, Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inr,
      rootPairs_pos] using hbx (asRoot a)
  have hbpn (a : PositiveRoot H φ) : bp (.inr (.inr a)) = x (opposite negRoot (asRoot a)) := by
    simpa only [bp, Basis.reindex_apply, E, Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inr,
      rootPairs_neg] using hbx (opposite negRoot (asRoot a))
  let d := compactComplexBasis bp
  have hdH (i : simple H φ) : d (.inl i) = Complex.I • (coroot_value H i.val : L) := by
    rw [compactComplexBasis_cartan, hbpH]
  have hdd (a : PositiveRoot H φ) :
      d (.inr (.inl a)) = x (asRoot a) - x (opposite negRoot (asRoot a)) := by
    rw [compactComplexBasis_difference, hbpp, hbpn]
  have hds (a : PositiveRoot H φ) :
      d (.inr (.inr a)) = Complex.I • (x (asRoot a) + x (opposite negRoot (asRoot a))) := by
    rw [compactComplexBasis_sum, hbpp, hbpn]
  have hτd : ∀ i, τ (d i) = d i := by
    have hm (z : L) : τ (Complex.I • z) = (-Complex.I) • τ z :=
      (map_smulₛₗ τ Complex.I z).trans (by rw [Complex.conj_I])
    rintro (i | (a | a))
    · rw [hdH, hm, hτH, smul_neg, neg_smul, neg_neg]
    · rw [hdd, map_sub, hτx, hτx, opposite_involutive, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
    · rw [hds, hm, map_add, hτx, hτx, opposite_involutive, ← neg_add, smul_neg, neg_smul,
        neg_neg, add_comm]
  let U := fixed τ hτ
  let c := fixedBasis d τ hτ hτd
  have hc (i) : (c i : L) = d i := fixedBasis_apply d τ hτ hτd i
  let : Fintype (Root H) := (rootSet_finite H hH.1).fintype
  let : Fintype (PositiveRoot H φ) :=
    ((rootSet_finite H hH.1).subset (fun _ ha => ha.1)).fintype
  let : Fintype (simple H φ) :=
    ((rootSet_finite H hH.1).subset (fun _ ha => ha.1.1)).fintype
  let B := _root_.killingForm ℂ L
  let B₀ := _root_.killingForm ℝ U
  have hB (v w : U) : B (v : L) (w : L) = (B₀ v w : ℂ) := killing_fixed d τ hτ hτd v w
  have hsym (v w : U) : B₀ v w = B₀ w v := LieModule.traceForm_comm ℝ U U v w
  obtain ⟨k, hk⟩ := Classical.axiomOfChoice
    (fun a : PositiveRoot H φ => positive_pairing hss hH R (asRoot a)
      (hx (opposite negRoot (asRoot a))).1 (hxf (asRoot a)))
  obtain ⟨hds0, hrr, hrdiag⟩ := positiveRoot_pairing_blocks negRoot x (fun a => (hx a).1) k
    (fun a => (hk a).2)
  have hCartan (a : simple H φ → ℝ) (hp : (∑ i, a i • c (.inl i)) ≠ 0) :
      B₀ (∑ i, a i • c (.inl i)) (∑ i, a i • c (.inl i)) < 0 := by
    let t (i : simple H φ) : realCartan H :=
      ⟨coroot_value H i.val, coroot_in_realCartan ⟨i.val, i.property.1.1⟩⟩
    let u := ∑ i, a i • t i
    let p := ∑ i, a i • c (.inl i)
    let emb : realCartan H →ₗ[ℝ] L :=
      (H.incl.toLinearMap.restrictScalars ℝ).comp (realCartan H).subtype
    have hpv : (p : L) = Complex.I • emb u := by
      change U.incl p = _
      simp only [p, u, map_sum, map_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change a i • (c (.inl i) : L) = _
      rw [hc, hdH, smul_comm]
      rfl
    have hu : u ≠ 0 := by
      intro hz
      apply hp
      change p = 0
      apply Subtype.ext
      change (p : L) = 0
      rw [hpv, hz, map_zero, smul_zero]
    have hcomp : B (emb u) (emb u) = (realKilling H u u : ℂ) := R.killing_restrict_real u u
    have hbcomp := hB p p
    rw [hpv] at hbcomp
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hcomp,
      ← mul_assoc, ← pow_two, Complex.I_sq, neg_one_mul] at hbcomp
    have hbRe := congrArg Complex.re hbcomp
    simp only [Complex.neg_re, Complex.ofReal_re] at hbRe
    change B₀ p p < 0
    linarith [R.killing_positive u hu]
  have hMix (i : simple H φ) (a : PositiveRoot H φ ⊕ PositiveRoot H φ) :
      B₀ (c (.inl i)) (c (.inr a)) = 0 := by
    apply Complex.ofReal_injective
    rw [← hB, Complex.ofReal_zero, hc, hc, hdH]
    rcases a with a | a
    · rw [hdd]
      simp [B, map_smul, LinearMap.smul_apply, map_sub,
        killing_cartan_root hss hH _ _ _ (hx (asRoot a)).1,
        killing_cartan_root hss hH _ _ _ (hx (opposite negRoot (asRoot a))).1]
    · rw [hds]
      simp [B, map_smul, LinearMap.smul_apply, map_add,
        killing_cartan_root hss hH _ _ _ (hx (asRoot a)).1,
        killing_cartan_root hss hH _ _ _ (hx (opposite negRoot (asRoot a))).1]
  have hOff (a b : PositiveRoot H φ ⊕ PositiveRoot H φ) (hn : a ≠ b) :
      B₀ (c (.inr a)) (c (.inr b)) = 0 := by
    apply Complex.ofReal_injective
    rw [← hB, Complex.ofReal_zero, hc, hc]
    rcases a with a | a <;> rcases b with b | b
    · rw [hdd, hdd]
      exact (hrr a b (fun he => hn (congrArg Sum.inl he))).1
    · rw [hdd, hds]
      exact hds0 a b
    · rw [hds, hdd, LieModule.traceForm_comm ℂ L L]
      exact hds0 b a
    · rw [hds, hds]
      exact (hrr a b (fun he => hn (congrArg Sum.inr he))).2
  have hDiag (a : PositiveRoot H φ ⊕ PositiveRoot H φ) :
      B₀ (c (.inr a)) (c (.inr a)) < 0 := by
    rcases a with a | a
    · have he := hB (c (.inr (.inl a))) (c (.inr (.inl a)))
      rw [hc, hdd, (hrdiag a).1] at he
      have he' := Complex.ofReal_injective he
      linarith [(hk a).1]
    · have he := hB (c (.inr (.inr a))) (c (.inr (.inr a)))
      rw [hc, hds, (hrdiag a).2] at he
      have he' := Complex.ofReal_injective he
      linarith [(hk a).1]
  have hneg := negative_of_blocks c B₀ hsym hCartan hMix hOff hDiag
  -- The conjugation also works for any other choice of positive roots in this Cartan.
  have hsum (ψ : Module.Dual ℂ H →ₗ[ℝ] ℝ) (hψ : ∀ α ∈ rootSet_value H, ψ α ≠ 0) :
      U.toSubmodule ⊔ borelReal H ψ = ⊤ := by
    let T : Submodule ℂ L := H.toSubmodule ⊔ ⨆ a : PositiveRoot H ψ, rootSpace H a.val
    let V := U.toSubmodule ⊔ borelReal H ψ
    have hpos (a : PositiveRoot H ψ) : x (asRoot a) ∈ T :=
      Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (hx (asRoot a)).1)
    have hv (i : simple H φ ⊕ Root H) (z : ℂ) : z • b i ∈ V := by
      rcases i with i | a
      · rw [hbH]
        exact Submodule.mem_sup_right
          (show z • (coroot_value H i.val : L) ∈ T from
            T.smul_mem z (Submodule.mem_sup_left (coroot_value H i.val).property))
      · rw [hbx]
        obtain ⟨a | a, rfl⟩ := (rootPairs hψ negRoot).surjective a
        · rw [rootPairs_pos]
          exact Submodule.mem_sup_right (show z • x (asRoot a) ∈ T from T.smul_mem z (hpos a))
        · rw [rootPairs_neg]
          let e := x (asRoot a)
          let f := x (opposite negRoot (asRoot a))
          have hte : τ e = -f := hτx _
          have htf : τ f = -e := (hτx _).trans (by rw [opposite_involutive])
          have hd : e - f ∈ U := by
            change τ (e - f) = e - f
            rw [map_sub, hte, htf]
            abel
          have hs : Complex.I • (e + f) ∈ U := by
            change τ (Complex.I • (e + f)) = Complex.I • (e + f)
            rw [map_smulₛₗ, Complex.conj_I, map_add, hte, htf, ← neg_add, smul_neg,
              neg_smul, neg_neg, add_comm]
          have hf : f ∈ V := by
            have heq : f = e - (e - f) := by abel
            rw [heq]
            exact V.sub_mem (Submodule.mem_sup_right (hpos a)) (Submodule.mem_sup_left hd)
          have hfI : Complex.I • f ∈ V := by
            have heq : Complex.I • f = Complex.I • (e + f) - Complex.I • e := by
              rw [smul_add]
              abel
            rw [heq]
            exact V.sub_mem (Submodule.mem_sup_left hs)
              (Submodule.mem_sup_right (show Complex.I • e ∈ T from T.smul_mem _ (hpos a)))
          change z • f ∈ V
          have hz : z • f = z.re • f + z.im • (Complex.I • f) := by
            conv_lhs => rw [← Complex.re_add_im z]
            rw [add_smul, mul_smul]
            rfl
          rw [hz]
          exact V.add_mem (V.smul_mem _ hf) (V.smul_mem _ hfI)
    apply top_unique
    intro v _
    rw [← b.sum_repr v]
    exact V.sum_mem (fun i _ => hv i _)
  exact ⟨negRoot, x, b, τ, hτ, c, hx, hxf, hbH, hbx, hbInt, hττ, hτH, hτx,
    fun i => (hc _).trans (hdH i), fun a => (hc _).trans (hdd a), fun a => (hc _).trans (hds a),
    hB, hneg, hermitian_symm d τ hτ hτd, hermitian_positive τ hτ hττ hB hneg, hsum⟩

theorem exists_compact_conjugation :
    Specs.LieAlgebrasAndRepresentations.CompactConjugation.existsCompactConjugationType.{u} := by
  intro L _ _ _ hss
  obtain ⟨H, hH⟩ := exists_maximal_toral L hss
  let : Finite (Root H) := (rootSet_finite H hH.1).to_subtype
  obtain ⟨φ, hφ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun a : Root H => a.val) (fun a => a.property.1)
  obtain ⟨_, _, _, τ, hτ, _, _, _, _, _, _, hi, _, _, _, _, _, _, hn, hs, hp, hsum⟩ :=
    @construction L _ _ _ hss H hH φ (fun a ha => hφ ⟨a, ha⟩)
  exact ⟨H, hH, τ, hτ, hi, hn, hs, hp, hsum⟩

end LieAlgebrasAndRepresentations.CompactConjugation
