import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.SimpleRootBranches
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Finite

/-!
Holomorphic variation of simple polynomial roots (paper.tex:3536–3564).

Weak holomorphy of each coefficient gives complex C¹ regularity locally by
Cauchy's theorem. The complex implicit function theorem then produces the local
zero graph. For the simultaneous statement, degree bounds make the given `d`
distinct roots simple. A finite intersection and Hausdorff separation give the
common disk and disjoint root neighborhoods. The same degree bound proves that
no root remains outside the constructed branches.
-/
noncomputable section
open Set Polynomial Filter
open scoped Topology

namespace D12Complex.SimpleRootBranches

lemma familyPolynomial_eval (d : ℕ) (A : ℕ → ℂ → ℂ) (z w : ℂ) :
    (familyPolynomial d A z).eval w = ∑ j ∈ Finset.range (d + 1), A j z * w ^ j := by
  simp [familyPolynomial, Polynomial.eval_finsetSum]

lemma familyPolynomial_contDiffAt (d : ℕ) (A : ℕ → ℂ → ℂ) (Ω : Set ℂ)
    (a b : ℂ) (hΩ : IsOpen Ω) (ha : a ∈ Ω)
    (hA : ∀ j ≤ d, HolomorphicOn Ω (A j)) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => (familyPolynomial d A p.1).eval p.2) (a,b) := by
  simp_rw [familyPolynomial_eval]
  apply ContDiffAt.sum
  intro j hj
  have hjd : j ≤ d := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hc : ContDiffAt ℂ 1 (A j) a := by
    have hd : DifferentiableOn ℂ (A j) Ω :=
      fun z hz => ((hA j hjd).2 z hz).differentiableWithinAt
    exact (hd.contDiffOn hΩ).contDiffAt (hΩ.mem_nhds ha)
  exact (hc.comp (a,b) contDiffAt_fst).mul (contDiffAt_snd.pow j)

lemma scalar_linear_invertible {L : ℂ →L[ℂ] ℂ} (h : L 1 ≠ 0) : L.IsInvertible := by
  have hL : L = (L 1) • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext_ring
    simp
  rw [hL]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · ext
    simp [h]
  · ext
    simp [h]

lemma local_simple_root_invertible
    {P : ℂ × ℂ → ℂ} {a b : ℂ}
    (hP : ContDiffAt ℂ 1 P (a,b)) (hzero : P (a,b) = 0)
    (hw : (fderiv ℂ P (a,b) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∃ U V : Set ℂ, ∃ f : ℂ → ℂ,
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      (∀ z ∈ U, DifferentiableAt ℂ f z) ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, P (z,w) = 0 ↔ w = f z := by
  let f := hP.implicitFunction (by simp) hw
  have hf : ContDiffAt ℂ 1 f a := hP.contDiffAt_implicitFunction (by simp) hw
  have hfa : f a = b := hP.implicitFunction_apply_self (by simp) hw
  have heq : ∀ᶠ v in 𝓝 (a,b), P v = 0 ↔ f v.1 = v.2 := by
    simpa only [hzero] using hP.eventually_apply_eq_iff_implicitFunction (by simp) hw
  rcases mem_nhds_prod_iff.mp heq with ⟨U₀, hU₀, V₀, hV₀, hrect⟩
  rcases mem_nhds_iff.mp hV₀ with ⟨V, hVV, hV, hbV⟩
  have hdiff : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ f z :=
    (hf.eventually (by simp)).mono fun _ hz => hz.differentiableAt (by simp)
  have hmap : f ⁻¹' V ∈ 𝓝 a := hf.continuousAt.preimage_mem_nhds (by simpa [hfa] using hV.mem_nhds hbV)
  rcases mem_nhds_iff.mp (inter_mem (inter_mem hU₀ hdiff) hmap) with
    ⟨U, hUsub, hU, haU⟩
  refine ⟨U, V, f, hU, hV, haU, hbV, ?_, hfa, ?_, ?_⟩
  · intro z hz
    exact (hUsub hz).1.2
  · intro z hz
    exact (hUsub hz).2
  · intro z hz w hwV
    exact (hrect ⟨(hUsub hz).1.1, hVV hwV⟩).trans eq_comm

lemma local_simple_root
    {P : ℂ × ℂ → ℂ} {a b : ℂ}
    (hP : ContDiffAt ℂ 1 P (a,b)) (hzero : P (a,b) = 0)
    (hw : fderiv ℂ P (a,b) (0,1) ≠ 0) :
    ∃ U V : Set ℂ, ∃ f : ℂ → ℂ,
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      (∀ z ∈ U, DifferentiableAt ℂ f z) ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, P (z,w) = 0 ↔ w = f z := by
  apply local_simple_root_invertible hP hzero
  apply scalar_linear_invertible
  simpa using hw
lemma local_simple_root_hasDerivAt
    {P : ℂ × ℂ → ℂ} {a b D : ℂ}
    (hP : ContDiffAt ℂ 1 P (a,b)) (hzero : P (a,b) = 0)
    (hD : HasDerivAt (fun w => P (a,w)) D b) (hw : D ≠ 0) :
    ∃ U V : Set ℂ, ∃ f : ℂ → ℂ,
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      (∀ z ∈ U, DifferentiableAt ℂ f z) ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, P (z,w) = 0 ↔ w = f z := by
  apply local_simple_root hP hzero
  have hslice : HasFDerivAt (fun w => P (a,w))
      (fderiv ℂ P (a,b) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) b := by
    convert (hP.differentiableAt (by simp)).hasFDerivAt.comp b
      ((hasFDerivAt_const a b).prodMk (hasFDerivAt_id b)) using 1 <;> rfl
  have heq := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (hslice.unique hD.hasFDerivAt)
  have heq' : fderiv ℂ P (a,b) (0,1) = D := by simpa using heq
  exact heq'.trans_ne hw


/-- The implicit function theorem applied to the finite coefficient family.
The C¹ hypothesis of the library theorem is derived from weak holomorphy above. -/
theorem simple_root_branch :
    Specs.D12Complex.Ch21.SimpleRootBranches.simple_root_branch_type := by
  intro d A Ω a b hΩ ha hA hroot hsimple
  obtain ⟨U, V, f, hU, hV, haU, hbV, hf, hfa, hmap, hgraph⟩ :=
    local_simple_root_hasDerivAt
      (familyPolynomial_contDiffAt d A Ω a b hΩ ha hA) hroot
      ((familyPolynomial d A a).hasDerivAt b) hsimple
  refine ⟨U ∩ Ω, V, f, hU.inter hΩ, ⟨haU, ha⟩, inter_subset_right,
    hV, hbV, ⟨hU.inter hΩ, fun z hz => hf z hz.1⟩, hfa,
    fun z hz => hmap hz.1, fun z hz w hw => hgraph z hz.1 w hw⟩


namespace RootCounting

lemma roots_eq_image {d : ℕ} {p : Polynomial ℂ} (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ d) {b : Fin d → ℂ} (hb : Function.Injective b)
    (hroot : ∀ i, p.eval (b i) = 0) :
    p.roots = (Finset.univ.image b).val := by
  classical
  apply roots_eq_of_natDegree_le_card_of_ne_zero _ _ hp
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hroot i
  · simpa [Finset.card_image_of_injective _ hb] using hdegree

lemma all_roots {d : ℕ} {p : Polynomial ℂ} (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ d) {b : Fin d → ℂ} (hb : Function.Injective b)
    (hroot : ∀ i, p.eval (b i) = 0) (w : ℂ) :
    p.eval w = 0 ↔ ∃ i, w = b i := by
  classical
  change p.IsRoot w ↔ _
  rw [← mem_roots hp, roots_eq_image hp hdegree hb hroot]
  simp [eq_comm]

lemma derivative_ne_zero {d : ℕ} {p : Polynomial ℂ} (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ d) {b : Fin d → ℂ} (hb : Function.Injective b)
    (hroot : ∀ i, p.eval (b i) = 0) (i : Fin d) :
    p.derivative.eval (b i) ≠ 0 := by
  classical
  intro hi
  have hmult : 1 < p.rootMultiplicity (b i) :=
    (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot i, hi⟩
  have hn : p.roots.Nodup := by
    rw [roots_eq_image hp hdegree hb hroot]
    exact (Finset.univ.image b).nodup
  have hle : p.rootMultiplicity (b i) ≤ 1 := by
    rw [← count_roots]
    exact Multiset.nodup_iff_count_le_one.mp hn (b i)
  omega

end RootCounting

lemma familyPolynomial_coeff (d : ℕ) (A : ℕ → ℂ → ℂ) (z : ℂ) (j : ℕ)
    (hj : j ≤ d) : (familyPolynomial d A z).coeff j = A j z := by
  classical
  simp [familyPolynomial, finsetSum_coeff, coeff_monomial, hj]

lemma familyPolynomial_natDegree_le (d : ℕ) (A : ℕ → ℂ → ℂ) (z : ℂ) :
    (familyPolynomial d A z).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le (A j z)).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

lemma familyPolynomial_ne_zero (d : ℕ) (A : ℕ → ℂ → ℂ) (z : ℂ) (h : A d z ≠ 0) :
    familyPolynomial d A z ≠ 0 := by
  intro hp
  apply h
  simpa [familyPolynomial_coeff d A z d le_rfl] using congrArg (fun p : Polynomial ℂ => p.coeff d) hp

lemma familyPolynomial_natDegree (d : ℕ) (A : ℕ → ℂ → ℂ) (z : ℂ) (h : A d z ≠ 0) :
    (familyPolynomial d A z).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (familyPolynomial_natDegree_le d A z)
  simpa [familyPolynomial_coeff d A z d le_rfl] using h


open Set Filter
open scoped Topology
open D12Complex

theorem all_simple_root_branches :
    Specs.D12Complex.Ch21.SimpleRootBranches.all_simple_root_branches_type := by
  classical
  intro d A Ω a b hd hΩ ha hA hlead hb hroot
  have hp : familyPolynomial d A a ≠ 0 := familyPolynomial_ne_zero d A a hlead
  have hderiv : ∀ i, (familyPolynomial d A a).derivative.eval (b i) ≠ 0 :=
    RootCounting.derivative_ne_zero hp (familyPolynomial_natDegree_le d A a) hb hroot
  have hbranch := fun i => simple_root_branch d A Ω a (b i) hΩ ha hA (hroot i) (hderiv i)
  choose U V₀ f hU hUa hUΩ hV₀ hbV₀ hf hfa hfV₀ hzero using hbranch
  obtain ⟨W, hW, hWdisj⟩ := (Set.finite_range b).t2_separation
  let V : Fin d → Set ℂ := fun i => V₀ i ∩ W (b i)
  have hV : ∀ i, IsOpen (V i) ∧ b i ∈ V i := by
    intro i
    exact ⟨(hV₀ i).inter (hW (b i)).2, ⟨hbV₀ i, (hW (b i)).1⟩⟩
  have hVdisj : Pairwise (fun i j => Disjoint (V i) (V j)) := by
    intro i j hij
    apply (hWdisj (Set.mem_range_self i) (Set.mem_range_self j) (fun h => hij (hb h))).mono
    · exact inter_subset_right
    · exact inter_subset_right
  have hleading : ∀ᶠ z in 𝓝 a, A d z ≠ 0 :=
    ((hA d le_rfl).2 a ha).continuousAt.eventually_ne hlead
  have hnear : ∀ᶠ z in 𝓝 a, ∀ i, z ∈ U i ∧ f i z ∈ W (b i) := by
    apply eventually_all.mpr
    intro i
    have hcont : ContinuousAt (f i) a := ((hf i).2 a (hUa i)).continuousAt
    have hpre : ∀ᶠ z in 𝓝 a, f i z ∈ W (b i) := by
      apply hcont.preimage_mem_nhds
      rw [hfa i]
      exact (hW (b i)).2.mem_nhds (hW (b i)).1
    exact Filter.inter_mem ((hU i).mem_nhds (hUa i)) hpre
  have hgood : {z | (z ∈ Ω ∧ A d z ≠ 0) ∧ ∀ i, z ∈ U i ∧ f i z ∈ W (b i)} ∈ 𝓝 a :=
    Filter.inter_mem (Filter.inter_mem (hΩ.mem_nhds ha) hleading) hnear
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hgood
  have hrΩ : Metric.ball a r ⊆ Ω := fun z hz => (hrs hz).1.1
  have hrlead : ∀ z ∈ Metric.ball a r, A d z ≠ 0 := fun z hz => (hrs hz).1.2
  have hrU : ∀ z ∈ Metric.ball a r, ∀ i, z ∈ U i := fun z hz i => ((hrs hz).2 i).1
  have hrW : ∀ z ∈ Metric.ball a r, ∀ i, f i z ∈ W (b i) := fun z hz i => ((hrs hz).2 i).2
  have hmap : ∀ i, MapsTo (f i) (Metric.ball a r) (V i) := by
    intro i z hz
    exact ⟨hfV₀ i (hrU z hz i), hrW z hz i⟩
  have hrootnear : ∀ z ∈ Metric.ball a r, ∀ i, (familyPolynomial d A z).eval (f i z) = 0 := by
    intro z hz i
    exact (hzero i z (hrU z hz i) (f i z) (hfV₀ i (hrU z hz i))).mpr rfl
  have hinj : ∀ z ∈ Metric.ball a r, Function.Injective (fun i => f i z) := by
    intro z hz i j heq
    by_contra hij
    have hmj : f i z ∈ V j := by
      rw [show f i z = f j z from heq]
      exact hmap j hz
    exact Set.disjoint_left.mp (hVdisj hij) (hmap i hz) hmj
  refine ⟨r, f, V, hr, hrΩ, hV, hVdisj, ?_, ?_, ?_⟩
  · intro i
    refine ⟨⟨Metric.isOpen_ball, fun z hz => (hf i).2 z (hrU z hz i)⟩, hfa i, hmap i⟩
  · intro z hz i w hw
    exact hzero i z (hrU z hz i) w hw.1
  · intro z hz
    exact ⟨familyPolynomial_natDegree d A z (hrlead z hz), hinj z hz,
      RootCounting.all_roots (familyPolynomial_ne_zero d A z (hrlead z hz))
        (familyPolynomial_natDegree_le d A z) (hinj z hz) (hrootnear z hz)⟩


end D12Complex.SimpleRootBranches
