import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Spectrum
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.CompactSpectral
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.ClassicalEigenfunctionBridge
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.SuccPred.LinearLocallyFinite

noncomputable section
open Set MeasureTheory Filter Module
open scoped Topology ComplexConjugate
namespace D13Unified.Ch10.Spectrum
open RegularProblem

/-- Continuous polynomial evaluation defines a class in the actual weighted space. -/
def polynomialClass (P : Problem) : Polynomial ℂ →ₗ[ℂ] Hilbert P where
  toFun f := toHilbert P (fun x => f.eval (x : ℂ))
    (continuous_memLp P _ (f.continuous.comp Complex.continuous_ofReal).continuousOn)
  map_add' f g := by
    simp only [Polynomial.eval_add]
    exact MemLp.toLp_add _ _
  map_smul' z f := by
    simp only [Polynomial.eval_smul]
    exact MemLp.toLp_const_smul z _

/-- Equality of continuous classes gives equality at every point of [a,b],
so infinitely many polynomial evaluations agree. -/
theorem polynomialClass_injective (P : Problem) : Function.Injective (polynomialClass P) := by
  intro f g h
  have he : EqOn (fun x : ℝ => f.eval (x : ℂ)) (fun x : ℝ => g.eval (x : ℂ))
      (interval P) :=
    (continuous_equality P _ _ (f.continuous.comp Complex.continuous_ofReal).continuousOn
      (g.continuous.comp Complex.continuous_ofReal).continuousOn
      (continuous_memLp P _ (f.continuous.comp Complex.continuous_ofReal).continuousOn)
      (continuous_memLp P _ (g.continuous.comp Complex.continuous_ofReal).continuousOn)).mp h
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Icc_infinite P.a_lt_b).image Complex.ofReal_injective.injOn).mono
  rintro _ ⟨x, hx, rfl⟩
  exact he hx

/-- This does not infer infinite dimension merely from an abstract spectral list. -/
theorem infinite_dimension : Specs.D13Unified.Ch10.Spectrum.InfiniteDimension := by
  intro P hfin
  letI := hfin
  letI : FiniteDimensional ℂ (Polynomial ℂ) :=
    FiniteDimensional.of_injective (polynomialClass P) (polynomialClass_injective P)
  have : Finite ℕ := (Polynomial.basisMonomials ℂ).linearIndependent.finite
  exact not_finite ℕ

/-- The continuous linear version of the supplied, actual Green integral operator. -/
def greenMap (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) : Hilbert P →L[ℂ] Hilbert P :=
  ⟨GreenOperator.linearOperator P c hc hQ,
    (GreenOperator.linearOperator_symmetric P c hc hQ).continuous⟩

@[simp] lemma greenMap_apply (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (f : Hilbert P) :
    greenMap P c hc hQ f = GreenWeakInverse.operator P c f := rfl

lemma greenMap_compact (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    IsCompactOperator (greenMap P c hc hQ) := GreenOperator.compact P c hc hQ

lemma greenMap_symmetric (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    (greenMap P c hc hQ).IsSymmetric := GreenOperator.linearOperator_symmetric P c hc hQ

lemma greenMap_nonnegative (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    ∀ f : Hilbert P, 0 ≤ (inner ℂ (greenMap P c hc hQ f) f).re := by
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · have h := (GreenOperator.strictlyPositive P c hc hQ f hf).1
    change 0 < (inner ℂ f (greenMap P c hc hQ f)).re at h
    rw [← inner_conj_symm] at h
    exact h.le

lemma greenMap_ker (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    (greenMap P c hc hQ).ker = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  exact GreenOperator.injective P c hc hQ

/-- The index set contains exactly the strictly positive Green eigenvalues. -/
abbrev PositiveEigenvalues (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :=
  {mu : ℝ // 0 < mu ∧ End.HasEigenvalue (greenMap P c hc hQ).toLinearMap (mu : ℂ)}

/-- A normalized real representative in every positive eigenspace. -/
lemma real_eigenvectors (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    ∀ mu : PositiveEigenvalues P c hc hQ,
    ∃ (r : ℝ → ℝ) (hr : MemLp (fun x => (r x : ℂ)) 2 (weightedMeasure P)),
      IsClassicalEigenfunction P dirichlet ((mu.val⁻¹ - c : ℝ) : ℂ) (fun x => (r x : ℂ)) ∧
      ‖toHilbert P (fun x => (r x : ℂ)) hr‖ = 1 ∧
      greenMap P c hc hQ (toHilbert P (fun x => (r x : ℂ)) hr) =
        (mu.val : ℂ) • toHilbert P (fun x => (r x : ℂ)) hr := by
  intro mu
  obtain ⟨f, hf, hf0⟩ := mu.property.2.exists_hasEigenvector
  obtain ⟨y, hym, hy, _, _⟩ := ClassicalEigenfunctionBridge.forward P c hc hQ mu.val
    mu.property.1 f hf0 (End.mem_eigenspace_iff.mp hf)
  obtain ⟨r, hr, hrc, hrn⟩ := ClassicalEigenfunctionBridge.real_normalized P _ ⟨y, hy⟩
  refine ⟨r, hr, hrc, hrn, ?_⟩
  have he := (ClassicalEigenfunctionBridge.converse P c hc hQ _ _ hrc hr).2.2.2
  have hz : (((mu.val⁻¹ - c : ℝ) : ℂ) + (c : ℂ))⁻¹ = (mu.val : ℂ) := by
    push_cast; simp
  rw [hz] at he
  exact he

/-- A real normalized mode spans its entire Green eigenspace. -/
lemma eigenspace_eq_span (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x)
    (mu : PositiveEigenvalues P c hc hQ) (r : ℝ → ℝ)
    (hr : MemLp (fun x => (r x : ℂ)) 2 (weightedMeasure P))
    (hrc : IsClassicalEigenfunction P dirichlet ((mu.val⁻¹ - c : ℝ) : ℂ)
      (fun x => (r x : ℂ))) :
    End.eigenspace (greenMap P c hc hQ).toLinearMap (mu.val : ℂ) =
      ℂ ∙ toHilbert P (fun x => (r x : ℂ)) hr := by
  apply le_antisymm
  · intro f hf
    by_cases hf0 : f = 0
    · simp [hf0]
    obtain ⟨y, hym, hy, hclass, _⟩ := ClassicalEigenfunctionBridge.forward P c hc hQ mu.val
      mu.property.1 f hf0 (End.mem_eigenspace_iff.mp hf)
    obtain ⟨z, heq⟩ := ClassicalEigenfunctionBridge.classical_proportional P _ _ _ hrc hy
    apply Submodule.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    rw [← ClassicalEigenfunctionBridge.toHilbert_smul, ← hclass]
    exact (continuous_equality P _ _ (continuousOn_const.mul hrc.1.continuousOn)
      hy.1.continuousOn _ _).mpr heq.symm
  · rw [Submodule.span_singleton_le_iff_mem]
    apply End.mem_eigenspace_iff.mpr
    have he := (ClassicalEigenfunctionBridge.converse P c hc hQ _ _ hrc hr).2.2.2
    have hz : (((mu.val⁻¹ - c : ℝ) : ℂ) + (c : ℂ))⁻¹ = (mu.val : ℂ) := by
      push_cast; simp
    rw [hz] at he
    exact he

/-- Real normalized modes are a Hilbert basis, indexed for now by their positive
Green eigenvalues. This is also a complete classical-representative construction. -/
theorem positive_basis (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    ∃ (r : PositiveEigenvalues P c hc hQ → ℝ → ℝ)
      (hr : ∀ mu, MemLp (fun x => (r mu x : ℂ)) 2 (weightedMeasure P))
      (B : HilbertBasis (PositiveEigenvalues P c hc hQ) ℂ (Hilbert P)),
      (∀ mu, IsClassicalEigenfunction P dirichlet ((mu.val⁻¹ - c : ℝ) : ℂ)
        (fun x => (r mu x : ℂ))) ∧
      (∀ mu, B mu = toHilbert P (fun x => (r mu x : ℂ)) (hr mu)) ∧
      (∀ mu, End.eigenspace (greenMap P c hc hQ).toLinearMap (mu.val : ℂ) = ℂ ∙ B mu) := by
  classical
  choose r hr hrc hn he using real_eigenvectors P c hc hQ
  let v := fun mu => toHilbert P (fun x => (r mu x : ℂ)) (hr mu)
  have hspan (mu) : End.eigenspace (greenMap P c hc hQ).toLinearMap (mu.val : ℂ) = ℂ ∙ v mu :=
    eigenspace_eq_span P c hc hQ mu (r mu) (hr mu) (hrc mu)
  have hv : Orthonormal ℂ v := by
    refine ⟨hn, ?_⟩
    intro mu nu hne
    apply (greenMap_symmetric P c hc hQ).orthogonalFamily_eigenspaces
      (show (mu.val : ℂ) ≠ (nu.val : ℂ) from fun h =>
        hne (Subtype.ext (Complex.ofReal_injective h)))
      ⟨v mu, End.mem_eigenspace_iff.mpr (he mu)⟩
      ⟨v nu, End.mem_eigenspace_iff.mpr (he nu)⟩
  have hs : Specs.D13Unified.Ch10.CompactSpectral.positiveSpan (greenMap P c hc hQ) =
      Submodule.span ℂ (Set.range v) := by
    apply le_antisymm
    · apply iSup_le
      intro mu f hf
      by_cases hf0 : f = 0
      · simp [hf0]
      let i : PositiveEigenvalues P c hc hQ :=
        ⟨mu.val, mu.property, End.hasEigenvalue_of_hasEigenvector ⟨hf, hf0⟩⟩
      have hi : f ∈ ℂ ∙ v i := by rwa [← hspan i]
      apply (show ℂ ∙ v i ≤ Submodule.span ℂ (Set.range v) from ?_) hi
      rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (le_iSup_of_le (⟨i.val, i.property.1⟩ : {t : ℝ // 0 < t}) le_rfl :
        End.eigenspace (greenMap P c hc hQ).toLinearMap (i.val : ℂ) ≤
          Specs.D13Unified.Ch10.CompactSpectral.positiveSpan (greenMap P c hc hQ))
      exact End.mem_eigenspace_iff.mpr (he i)
  have hcsp : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
    rw [← hs, CompactSpectral.positiveSpan_closure (greenMap_compact P c hc hQ)
      (greenMap_symmetric P c hc hQ) (greenMap_nonnegative P c hc hQ),
      greenMap_ker]
    simp
  let B := HilbertBasis.mk hv hcsp.ge
  refine ⟨r, hr, B, hrc, ?_, ?_⟩
  · intro mu
    exact congrFun (HilbertBasis.coe_mk hv hcsp.ge) mu
  · intro mu
    simpa only [B, HilbertBasis.coe_mk] using hspan mu

/-- Every linear order with finite initial segments and infinitely many elements
can be listed increasingly by all natural numbers. -/
lemma orderIso_nat_of_finite_initial {α : Type*} [LinearOrder α] [Infinite α]
    (hfin : ∀ a : α, (Set.Iic a).Finite) : Nonempty (ℕ ≃o α) := by
  classical
  letI : LocallyFiniteOrder α := LocallyFiniteOrder.ofFiniteIcc
    (fun a b => (hfin b).subset (fun _ h => h.2))
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image (Set.Iic a) id (hfin a) ⟨a, le_rfl⟩
  have hbot : ∀ x : α, m ≤ x := by
    intro x
    rcases le_total x a with h | h
    · exact hmin x h
    · exact hm.trans h
  letI : OrderBot α := { bot := m, bot_le := hbot }
  letI : NoMaxOrder α := ⟨fun x => by
    by_contra! h
    have hh : (Set.univ : Set α).Finite := (hfin x).subset (fun y _ => h y)
    exact Set.infinite_univ hh⟩
  letI := LinearLocallyFiniteOrder.succOrder α
  letI := LinearLocallyFiniteOrder.predOrder α
  exact ⟨(orderIsoNatOfLinearSuccPredArch (ι := α)).symm⟩

/-- The actual infinite dimension and injectivity of K force infinitely many
positive eigenspaces: if the basis index were finite, H would be finite dimensional. -/
lemma positive_eigenvalues_infinite (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    Infinite (PositiveEigenvalues P c hc hQ) := by
  classical
  rw [← not_finite_iff_infinite]
  intro hfin
  letI := hfin
  letI := Fintype.ofFinite (PositiveEigenvalues P c hc hQ)
  obtain ⟨_, _, B, _⟩ := positive_basis P c hc hQ
  exact infinite_dimension P B.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Compactness gives finite upper segments in the positive Green spectrum. -/
lemma positive_eigenvalues_finite_above (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (eps : ℝ) (heps : 0 < eps) :
    {mu : PositiveEigenvalues P c hc hQ | eps ≤ mu.val}.Finite := by
  have hf := CompactSpectral.finite_eigenvalues_above (greenMap_compact P c hc hQ)
    (greenMap_symmetric P c hc hQ) heps
  have hi : Function.Injective (fun mu : PositiveEigenvalues P c hc hQ => (mu.val : ℂ)) :=
    fun _ _ h => Subtype.ext (Complex.ofReal_injective h)
  apply (hf.preimage hi.injOn).subset
  intro mu hmu
  exact ⟨mu.property.2, by simpa [abs_of_pos mu.property.1] using hmu⟩

/-- Decreasing enumeration with no repetitions and no omitted Green eigenvalues. -/
lemma positive_eigenvalues_ordered (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) :
    Nonempty (ℕ ≃o (PositiveEigenvalues P c hc hQ)ᵒᵈ) := by
  letI : Infinite (PositiveEigenvalues P c hc hQ)ᵒᵈ := positive_eigenvalues_infinite P c hc hQ
  apply orderIso_nat_of_finite_initial
  intro mu
  exact positive_eigenvalues_finite_above P c hc hQ mu.val mu.property.1

/-- The enumeration converges to zero, using compactness on the actual operator. -/
lemma positive_eigenvalues_tendsto_zero (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x)
    (e : ℕ ≃ (PositiveEigenvalues P c hc hQ)) :
    Tendsto (fun n => (e n).val) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hf := (positive_eigenvalues_finite_above P c hc hQ eps heps).preimage e.injective.injOn
  have hh : ∀ᶠ n in atTop, n ∉ e ⁻¹' {mu | eps ≤ mu.val} := by
    rw [← Nat.cofinite_eq_atTop]
    exact hf.eventually_cofinite_notMem
  filter_upwards [hh] with n hn
  change ¬ eps ≤ (e n).val at hn
  simpa [Real.dist_eq, abs_of_pos (e n).property.1] using not_le.mp hn

/-- The paper's linear-first coefficients are exactly native Hilbert coordinates;
Parseval is obtained by taking real parts of the Hilbert inner-product sum. -/
lemma hilbert_sums {ι : Type*} (P : Problem) (B : HilbertBasis ι ℂ (Hilbert P))
    (f : Hilbert P) :
    HasSum (fun n => paperInner P f (B n) • B n) f ∧
    HasSum (fun n => ‖paperInner P f (B n)‖ ^ 2) (‖f‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · simpa only [paperInner, Specs.D13Unified.Ch10.RegularProblem.paperInnerValue,
      B.repr_apply_apply] using B.hasSum_repr f
  · have h := (B.hasSum_inner_mul_inner f f).mapL Complex.reCLM
    convert h using 1
    · funext n
      change ‖inner ℂ (B n) f‖ ^ 2 = (inner ℂ f (B n) * inner ℂ (B n) f).re
      rw [← inner_conj_symm (B n) f, Complex.mul_conj' (inner ℂ f (B n))]
      simp only [RCLike.norm_conj, ← Complex.ofReal_pow, Complex.ofReal_re]
    · change ‖f‖ ^ 2 = (inner ℂ f f).re
      exact norm_sq_eq_re_inner (𝕜 := ℂ) f

/-- The full sequence, with natural index n representing j = n+1 in the paper. -/
theorem spectrum : Specs.D13Unified.Ch10.Spectrum.Expansion := by
  classical
  intro P
  obtain ⟨c, hc, hQ⟩ := GreenKernel.shift_exists P
  obtain ⟨r, hr, B, hrc, hrep, hsp⟩ := positive_basis P c hc hQ
  obtain ⟨e⟩ := positive_eigenvalues_ordered P c hc hQ
  let v : ℕ → Hilbert P := fun n => B (e n)
  have hv : Orthonormal ℂ v := B.orthonormal.comp e e.injective
  have hrange : Set.range v = Set.range B := by
    ext f
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨n, rfl⟩ := e.surjective i
      exact ⟨n, rfl⟩
  have hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
    rw [hrange, B.dense_span]
  let C := HilbertBasis.mk hv hd.ge
  have hC (n : ℕ) : C n = B (e n) := congrFun (HilbertBasis.coe_mk hv hd.ge) n
  let lam : ℕ → ℝ := fun n => (e n).val⁻¹ - c
  let phi : ℕ → ℝ → ℝ := fun n => r (e n)
  let hphi := fun n => hr (e n)
  refine ⟨lam, phi, hphi, C, ?_, ?_, ?_, ?_, ?_, ?_, hilbert_sums P C⟩
  · intro i j hij
    apply sub_lt_sub_right
    apply (inv_lt_inv₀ (e i).property.1 (e j).property.1).mpr
    exact e.strictMono hij
  · have hz := positive_eigenvalues_tendsto_zero P c hc hQ e.toEquiv
    have hp : Tendsto (fun n => (e n).val) atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall (fun n => (e n).property.1)⟩
    have hi := hp.inv_tendsto_nhdsGT_zero
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [tendsto_atTop.mp hi (a + c)] with n hn
    change a ≤ (e n).val⁻¹ - c
    change a + c ≤ (e n).val⁻¹ at hn
    linarith
  · intro n; exact hrc (e n)
  · intro n; exact (hC n).trans (hrep (e n))
  · intro z y hy
    let hym := continuous_memLp P y hy.1.continuousOn
    let f := toHilbert P y hym
    have hf : f ≠ 0 := (continuous_nonzero P y hy.1.continuousOn hym).mpr hy.2.1
    obtain ⟨hz, hpos, _, he⟩ := ClassicalEigenfunctionBridge.converse P c hc hQ z y hy hym
    have hre : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hz])
    let mu : PositiveEigenvalues P c hc hQ := ⟨(z.re + c)⁻¹, inv_pos.mpr hpos, by
      apply End.hasEigenvalue_of_hasEigenvector
      refine ⟨End.mem_eigenspace_iff.mpr ?_, hf⟩
      change greenMap P c hc hQ f = (((z.re + c)⁻¹ : ℝ) : ℂ) • f
      change greenMap P c hc hQ f = (z + (c : ℂ))⁻¹ • f at he
      simpa only [Complex.ofReal_inv, Complex.ofReal_add, hre] using he⟩
    obtain ⟨n, hn⟩ := e.surjective mu
    refine ⟨n, ?_⟩
    change z = (((e n).val⁻¹ - c : ℝ) : ℂ)
    rw [hn]
    dsimp [mu]
    rw [inv_inv]
    simpa only [add_sub_cancel_right] using hre.symm
  · intro n
    have hset : Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.classicalEigenspace P
        ((e n).val⁻¹ - c : ℝ) =
        (End.eigenspace (greenMap P c hc hQ).toLinearMap ((e n).val : ℂ) : Set (Hilbert P)) := by
      rw [ClassicalEigenfunctionBridge.eigenspaces P c hc hQ (e n).val (e n).property.1]
      ext f
      change (greenMap P c hc hQ).toLinearMap f = ((e n).val : ℂ) • f ↔
        f ∈ End.eigenspace (greenMap P c hc hQ).toLinearMap ((e n).val : ℂ)
      exact End.mem_eigenspace_iff.symm
    constructor
    · change Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.classicalEigenspace P
        ((e n).val⁻¹ - c : ℝ) = _
      rw [hset, hsp (e n), hC]
    · exact finrank_span_singleton (C.orthonormal.ne_zero n)

end D13Unified.Ch10.Spectrum
