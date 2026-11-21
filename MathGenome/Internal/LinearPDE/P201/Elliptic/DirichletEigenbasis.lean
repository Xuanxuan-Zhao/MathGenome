import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.DirichletEigenbasis
import MathGenome.Internal.LinearPDE.P201.Elliptic.DirichletResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.PositiveMinMax
import Mathlib.Topology.NatEmbedding
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace P201.DirichletEigenbasis

/-- The lower-set index supplied by the compact spectral theorem exhausts ℕ
when its operator is injective on an infinite-dimensional space. -/
theorem spectral_index_univ {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (hH : ¬FiniteDimensional ℝ H) (S : H →L[ℝ] H) (hinj : Function.Injective S)
    (I : Set ℕ) (e : I → H) (μ : I → ℝ)
    (hd : ExpandedFA.CompactSpectral.PositiveMinMax.Spec.PositiveSpectralList S I e μ) :
    I = Set.univ := by
  rcases hd.1.eq_univ_or_Iio with h | ⟨r, hr⟩
  · exact h
  · have hfin : FiniteDimensional ℝ S.range := (hd.2.2.2.2.2.2.2.2.1 r).mpr hr |>.1
    letI := hfin
    exact (hH (FiniteDimensional.of_injective S.toLinearMap.rangeRestrict
      (fun x y h => hinj (congrArg Subtype.val h)))).elim

/-- Decay follows from finiteness of every positive threshold set. -/
theorem tendsto_zero_of_finite_thresholds (μ : ℕ → ℝ) (hp : ∀ j, 0 < μ j)
    (hf : ∀ ε : ℝ, 0 < ε → {j | ε ≤ μ j}.Finite) :
    Tendsto μ atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (hf ε hε).bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  have hsmall : μ n < ε := lt_of_not_ge (fun hc => by
    have hnN : n ≤ N := hN hc
    omega)
  simpa [Real.dist_eq, abs_of_pos (hp n)] using hsmall

/-- A normalized, exhaustive, multiplicity-preserving ℕ spectral basis,
constructed from the pinned positive compact spectral theorem. -/
theorem compact_basis : P201Specs.DirichletEigenbasis.CompactBasisStatement := by
  intro H _ _ _ hH S hc hp hinj
  have hcompact :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator S.toLinearMap).mpr hc
  obtain ⟨I, e, μ, hd⟩ :=
    ExpandedFA.CompactSpectral.PositiveMinMax.ordered_positive_spectrum ℝ H S hp hcompact
  have hI := spectral_index_univ hH S hinj I e μ hd
  subst I
  let b : ℕ ≃ (Set.univ : Set ℕ) := (Equiv.Set.univ ℕ).symm
  rcases hd with ⟨_, he, hμ, hanti, heig, hsum, hspan, hfinite, _, hspace⟩
  let en : ℕ → H := e ∘ b
  let μn : ℕ → ℝ := μ ∘ b
  have hen : Orthonormal ℝ en := he.comp b b.injective
  have hspan' : (Submodule.span ℝ (Set.range en)).topologicalClosure = ⊤ := by
    have hr : Set.range en = Set.range e := by
      dsimp [en]
      rw [Set.range_comp, b.surjective.range_eq, Set.image_univ]
    rw [hr, hspan, LinearMap.ker_eq_bot.mpr hinj, Submodule.bot_orthogonal_eq_top]
  let basis : HilbertBasis ℕ ℝ H := HilbertBasis.mk hen hspan'.ge
  have hb : (basis : ℕ → H) = en := HilbertBasis.coe_mk hen hspan'.ge
  have hpos : ∀ j, 0 < μn j := fun j => hμ (b j)
  have hfin : ∀ ε : ℝ, 0 < ε → {j | ε ≤ μn j}.Finite := by
    intro ε hε
    exact Set.Finite.preimage (f := b) b.injective.injOn (hfinite ε hε)
  have hz : Tendsto μn atTop (𝓝 0) := tendsto_zero_of_finite_thresholds μn hpos hfin
  refine ⟨basis, μn, hpos, ?_, ?_, ?_, hfin, ?_, hz, ?_, ?_⟩
  · intro i j hij
    exact hanti (show b i ≤ b j from hij)
  · intro j
    rw [hb]
    exact heig (b j)
  · intro u
    simp only [hb]
    exact b.hasSum_iff.mpr (hsum u)
  · intro r hr
    have hspaceR := hspace r hr
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hspaceR
    rw [hspaceR]
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨b.symm i, ?_, ?_⟩
      · simpa [μn] using hi
      · rw [hb]
        simp [en]
    · rintro ⟨j, hj, rfl⟩
      exact ⟨b j, hj, by rw [hb]; rfl⟩
  · intro i j hij
    exact (inv_le_inv₀ (hpos i) (hpos j)).mpr (hanti (show b i ≤ b j from hij))
  · exact tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall hpos⟩)

/-- Disjoint nonempty open subsets of a ball give infinitely many nonzero
orthogonal L² vectors. No regularity or boundedness of Ω is needed here. -/
theorem infinite_dimension : P201Specs.DirichletEigenbasis.InfiniteDimensionStatement := by
  intro m Ω hne hfd
  letI := hfd
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  let B : Set (Space (m + 1)) := Metric.ball x r
  have hBpos : 0 < volume B := Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self hr⟩
  have hBinf : B.Infinite := by
    intro hf
    exact (ne_of_gt hBpos) (hf.measure_zero volume)
  letI : Infinite B := hBinf.to_subtype
  obtain ⟨U, hUne, hUopen, hUdisj⟩ := exists_seq_infinite_isOpen_pairwise_disjoint B
  let E : ℕ → Set (Space (m + 1)) := fun j => Subtype.val '' U j
  have heopen (j : ℕ) : IsOpen (E j) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ (hUopen j)
  have hesub (j : ℕ) : E j ⊆ (Ω : Set (Space (m + 1))) := by
    rintro y ⟨z, _, rfl⟩
    exact hball z.property
  have hemeasure (j : ℕ) : domainMeasure Ω (E j) = volume (E j) := by
    rw [Measure.restrict_apply (heopen j).measurableSet, Set.inter_eq_left.mpr (hesub j)]
  have hefinite (j : ℕ) : domainMeasure Ω (E j) ≠ ∞ := by
    rw [hemeasure]
    exact (measure_mono (Set.image_subset_iff.mpr (fun z _ => z.property))).trans_lt
      (Metric.isBounded_ball.measure_lt_top (μ := volume)) |>.ne
  have hepos (j : ℕ) : 0 < domainMeasure Ω (E j) := by
    rw [hemeasure]
    exact (heopen j).measure_pos volume ((hUne j).nonempty.image Subtype.val)
  let f : ℕ → Lp ℝ Ω 2 := fun j =>
    indicatorConstLp 2 (heopen j).measurableSet (hefinite j) (1 : ℝ)
  have hfzero (j : ℕ) : f j ≠ 0 := by
    intro hzero
    have hn := congrArg norm hzero
    have hp : 0 < ‖f j‖ := by
      dsimp [f]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos
        (ENNReal.toReal_pos (hepos j).ne' (hefinite j)) _)
    rw [hzero, norm_zero] at hp
    exact (lt_irrefl 0) hp
  have horth : Pairwise (fun i j => inner ℝ (f i) (f j) = 0) := by
    intro i j hij
    have hd : Disjoint (E i) (E j) :=
      Set.disjoint_image_of_injective Subtype.val_injective (hUdisj hij)
    change inner ℝ (indicatorConstLp 2 (heopen i).measurableSet (hefinite i) (1 : ℝ))
      (indicatorConstLp 2 (heopen j).measurableSet (hefinite j) (1 : ℝ)) = 0
    rw [L2.inner_indicatorConstLp_indicatorConstLp
      (heopen i).measurableSet (heopen j).measurableSet (hefinite i) (hefinite j),
      hd.inter_eq]
    simp
  have hlin := linearIndependent_of_ne_zero_of_inner_eq_zero hfzero horth
  haveI : Finite ℕ := hlin.finite
  exact (Finite.false (α := ℕ) inferInstance)

/-- Symmetry gives the coefficient action from the eigenvector equations. -/
theorem diagonal_coefficient {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (S : H →L[ℝ] H) (hs : S.IsSymmetric)
    (e : ℕ → H) (μ : ℕ → ℝ) (he : ∀ j, S (e j) = μ j • e j)
    (f : H) (j : ℕ) : inner ℝ (e j) (S f) = μ j * inner ℝ (e j) f := by
  have h := hs (e j) f
  change inner ℝ (S (e j)) f = inner ℝ (e j) (S f) at h
  rw [← h, he, real_inner_smul_left]

/-- Parseval supplies square summability in the original Hilbert space. -/
theorem summable_sq_coefficients {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e : HilbertBasis ℕ ℝ H) (f : H) :
    Summable (fun j => (inner ℝ (e j) f) ^ 2) := by
  simpa only [real_inner_comm f, ← pow_two] using e.summable_inner_mul_inner f f

/-- The converse is constructive: synthesize the preimage using the ℓ²
coefficients μ⁻¹(u,e), then compare all coefficients of its image. -/
theorem range_iff_weighted_summable {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : H →L[ℝ] H) (hs : S.IsSymmetric) (e : HilbertBasis ℕ ℝ H)
    (μ : ℕ → ℝ) (hμ : ∀ j, μ j ≠ 0) (he : ∀ j, S (e j) = μ j • e j)
    (u : H) :
    u ∈ Set.range S ↔
      Summable (fun j => (μ j)⁻¹ ^ 2 * (inner ℝ (e j) u) ^ 2) := by
  constructor
  · rintro ⟨f, rfl⟩
    have hc (j : ℕ) : (μ j)⁻¹ * inner ℝ (e j) (S f) = inner ℝ (e j) f := by
      rw [diagonal_coefficient S hs e μ he, ← mul_assoc, inv_mul_cancel₀ (hμ j), one_mul]
    simpa only [← mul_pow, hc] using summable_sq_coefficients e f
  · intro hu
    have hc : Memℓp (fun j => (μ j)⁻¹ * inner ℝ (e j) u) 2 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_pow]
        using hu
    let c : lp (fun _ : ℕ => ℝ) 2 := ⟨fun j => (μ j)⁻¹ * inner ℝ (e j) u, hc⟩
    let f : H := e.repr.symm c
    refine ⟨f, ?_⟩
    apply e.repr.injective
    apply lp.ext
    funext j
    simp only [e.repr_apply_apply]
    rw [diagonal_coefficient S hs e μ he]
    have hf : inner ℝ (e j) f = (μ j)⁻¹ * inner ℝ (e j) u := by
      rw [← e.repr_apply_apply]
      change e.repr (e.repr.symm c) j = _
      rw [e.repr.apply_symm_apply]
    rw [hf, ← mul_assoc, mul_inv_cancel₀ (hμ j), one_mul]

/-- Exact inverse operator domain and its convergent diagonal action. -/
theorem diagonal_inverse : P201Specs.DirichletEigenbasis.DiagonalInverseStatement := by
  intro H _ _ _ S L e μ hs hμ he hg
  have hd (u : H) : u ∈ L.domain ↔ u ∈ Set.range S := by
    rw [LinearPMap.mem_domain_iff]
    exact exists_congr (fun f => hg u f)
  refine ⟨fun u => (hd u).trans (range_iff_weighted_summable S hs e μ hμ he u), ?_⟩
  intro u
  have hu : S (L u) = (u : H) := (hg _ _).mp (L.mem_graph u)
  have hc (j : ℕ) : (μ j)⁻¹ * inner ℝ (e j) (u : H) = inner ℝ (e j) (L u) := by
    rw [← hu, diagonal_coefficient S hs e μ he, ← mul_assoc,
      inv_mul_cancel₀ (hμ j), one_mul]
  simpa only [hc, e.repr_apply_apply] using e.hasSum_repr (L u)

open P201Specs.Dirichlet P201Specs.DirichletEigenbasis
open scoped Matrix.Norms.Elementwise

/-- The energy-domain interface determines the same full graph as the
upstream concrete coefficient form. -/
theorem coefficient_graph {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2)) (ha : IsCoefficientForm Ω A a)
    (u f : Lp ℝ Ω 2) :
    (u, f) ∈ a.associatedOperator.graph ↔
      ∃ v : H10 ℝ Ω, hZeroUnderlying Ω v = u ∧ Solves Ω A (pivot Ω f) v.val := by
  rw [a.mem_associated_graph]
  constructor
  · rintro ⟨hu, huf⟩
    rw [ha.1] at hu
    obtain ⟨v, rfl⟩ := hu
    refine ⟨v, rfl, fun w => ?_⟩
    have hw : hZeroUnderlying Ω w ∈ a.domain := by rw [ha.1]; exact ⟨w, rfl⟩
    have hv : hZeroUnderlying Ω v ∈ a.domain := by rw [ha.1]; exact ⟨v, rfl⟩
    have he := huf ⟨hZeroUnderlying Ω w, hw⟩
    calc
      ellipticEnergyForm Ω A v.val w.val =
        a.form ⟨hZeroUnderlying Ω v, hv⟩ ⟨hZeroUnderlying Ω w, hw⟩ :=
          (ha.2 v w hv hw).symm
      _ = inner ℝ (hZeroUnderlying Ω w) f := he
      _ = inner ℝ f (hZeroUnderlying Ω w) := real_inner_comm _ _
  · rintro ⟨v, rfl, hv⟩
    have hmem : hZeroUnderlying Ω v ∈ a.domain := by rw [ha.1]; exact ⟨v, rfl⟩
    refine ⟨hmem, fun w => ?_⟩
    have hw : (w : Lp ℝ Ω 2) ∈ (hZeroUnderlying Ω).range := ha.1 ▸ w.property
    obtain ⟨z, hz⟩ := hw
    have he : w = ⟨hZeroUnderlying Ω z, by rw [ha.1]; exact ⟨z, rfl⟩⟩ :=
      Subtype.ext hz.symm
    rw [he]
    apply (ha.2 v z _ _).trans
    change ellipticEnergyForm Ω A v.val z.val = inner ℝ (hZeroUnderlying Ω z) f
    have hvz := hv z
    change ellipticEnergyForm Ω A v.val z.val = inner ℝ f (hZeroUnderlying Ω z) at hvz
    exact hvz.trans (real_inner_comm _ _)

/-- Positive inverse eigenvalues correspond exactly to partial-operator
eigenspaces; the graph enforces membership in the operator domain. -/
theorem inverse_eigenspace {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (S : H →L[ℝ] H)
    (L : ExpandedFA.Unbounded.Operator ℝ H H)
    (hg : ∀ u f : H, (u, f) ∈ L.graph ↔ S f = u)
    (r : ℝ) (hr : r ≠ 0) :
    operatorEigenspace L r = Module.End.eigenspace S.toLinearMap r⁻¹ := by
  ext u
  change (u, r • u) ∈ L.graph ↔ _
  rw [hg, Module.End.mem_eigenspace_iff]
  change S (r • u) = u ↔ S u = r⁻¹ • u
  rw [map_smul]
  constructor
  · intro h
    have hh := congrArg (fun z : H => r⁻¹ • z) h
    simpa only [inv_smul_smul₀ hr] using hh
  · intro h
    rw [h, smul_inv_smul₀ hr]

/-- Physical eigenvectors, finite multiplicities, increasing divergent
reciprocals, and the exact operator domain and action. -/
theorem operator_resolution : OperatorStatement := by
  intro m Ω hΩ hne A hA lam hlam hEll hsym a ha
  obtain ⟨T, hT, huniq, hc, hs, hp, hinj, _⟩ :=
    DirichletResolvent.inverse m Ω hΩ A hA lam hlam hEll hsym
  let S := (hZeroUnderlying Ω).comp T
  have hpositive : S.IsPositive := (ContinuousLinearMap.isPositive_iff S).mpr
    ⟨(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hs)), fun f =>
        (real_inner_comm (S f) f) ▸ hp f⟩
  have hg (u f : Lp ℝ Ω 2) : (u, f) ∈ a.associatedOperator.graph ↔ S f = u := by
    rw [coefficient_graph Ω A a ha]
    constructor
    · rintro ⟨v, hv, hsol⟩
      rw [(huniq f v).mp hsol] at hv
      exact hv
    · intro hu
      exact ⟨T f, hu, (huniq f (T f)).mpr rfl⟩
  obtain ⟨e, μ, hμ, hanti, heig, _, hfinite, hspace, _, hmono, htend⟩ :=
    compact_basis (Lp ℝ Ω 2) (infinite_dimension m Ω hne) S hc hpositive hinj
  let ev : ℕ → ℝ := fun j => (μ j)⁻¹
  let v : ℕ → H10 ℝ Ω := fun j => T (ev j • e j)
  have hv (j : ℕ) : hZeroUnderlying Ω (v j) = e j := by
    change S ((μ j)⁻¹ • e j) = e j
    rw [map_smul, heig, inv_smul_smul₀ (hμ j).ne']
  obtain ⟨hdom, hdiag⟩ := diagonal_inverse (Lp ℝ Ω 2) S a.associatedOperator
    e μ hpositive.isSymmetric (fun j => (hμ j).ne') heig hg
  refine ⟨e, ev, v, (fun j => inv_pos.mpr (hμ j)), hmono, htend,
    (fun j => ⟨hv j, (hg _ _).mpr (hv j)⟩), ?_, hdom, hdiag⟩
  intro r hr
  have hfiber : {j | ev j = r} = {j | μ j = r⁻¹} := by
    ext j
    simp only [Set.mem_ofPred_eq, ev, inv_eq_iff_eq_inv]
  refine ⟨?_, ?_⟩
  · rw [hfiber]
    exact (hfinite r⁻¹ (inv_pos.mpr hr)).subset (fun j hj => hj.ge)
  · rw [inverse_eigenspace S a.associatedOperator hg r hr.ne', hspace r⁻¹ (inv_pos.mpr hr)]
    rw [hfiber]

namespace EnergyGeometry
variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous strictly positive symmetric form on the original Banach space. -/
structure PositiveForm where
  form : V →L[ℝ] V →L[ℝ] ℝ
  symmetric : ∀ u v, form u v = form v u
  positive : ∀ u, u ≠ 0 → 0 < form u u

namespace PositiveForm
variable {V} (q : PositiveForm V)
def EnergySpace (_q : PositiveForm V) := V
instance : AddCommGroup q.EnergySpace := inferInstanceAs (AddCommGroup V)
instance : Module ℝ q.EnergySpace := inferInstanceAs (Module ℝ V)

def toOriginal : q.EnergySpace ≃ₗ[ℝ] V :=
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[instance_reducible] def energyCore : InnerProductSpace.Core ℝ q.EnergySpace where
  inner x y := q.form (q.toOriginal x) (q.toOriginal y)
  conj_inner_symm x y := q.symmetric _ _
  re_inner_nonneg x := by
    by_cases hx : q.toOriginal x = 0
    · simp [hx]
    · exact (q.positive _ hx).le
  add_left x y z := by
    change q.form (q.toOriginal x + q.toOriginal y) (q.toOriginal z) = _
    simp
  smul_left x y c := by
    change q.form (c • q.toOriginal x) (q.toOriginal y) = _
    simp
  definite x hx := by
    apply q.toOriginal.injective
    change q.toOriginal x = 0
    by_contra hn
    exact (q.positive _ hn).ne' hx

instance : NormedAddCommGroup q.EnergySpace :=
  letI : InnerProductSpace.Core ℝ q.EnergySpace := q.energyCore
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ q.EnergySpace :=
  InnerProductSpace.ofCore { q.energyCore with }

theorem inner_eq (x y : q.EnergySpace) :
    inner ℝ x y = q.form (q.toOriginal x) (q.toOriginal y) := rfl

theorem norm_sq (x : q.EnergySpace) :
    ‖x‖ ^ 2 = q.form (q.toOriginal x) (q.toOriginal x) := by
  exact (real_inner_self_eq_norm_sq (x := x)).symm

/-- Norm equivalence is proved in both directions, retaining the original
full norm and its topology. -/
def energyEquiv (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlo : ∀ x, c * ‖x‖ ^ 2 ≤ q.form x x)
    (hhi : ∀ x, q.form x x ≤ M * ‖x‖ ^ 2) : q.EnergySpace ≃L[ℝ] V :=
  q.toOriginal.toContinuousLinearEquivOfBounds (Real.sqrt c)⁻¹ (Real.sqrt M)
    (by
      intro x
      have hn : Real.sqrt c * ‖q.toOriginal x‖ ≤ ‖x‖ := by
        apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
        rw [mul_pow, Real.sq_sqrt hc.le, q.norm_sq]
        exact hlo _
      calc
        ‖q.toOriginal x‖ = (Real.sqrt c)⁻¹ * (Real.sqrt c * ‖q.toOriginal x‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_mul]
        _ ≤ (Real.sqrt c)⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hn (by positivity))
    (by
      intro x
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw [q.norm_sq, mul_pow, Real.sq_sqrt hM]
      exact hhi x)

theorem complete_energy [CompleteSpace V] (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlo : ∀ x, c * ‖x‖ ^ 2 ≤ q.form x x)
    (hhi : ∀ x, q.form x x ≤ M * ‖x‖ ^ 2) : CompleteSpace q.EnergySpace := by
  let e := q.energyEquiv c M hc hM hlo hhi
  let u : q.EnergySpace ≃ᵤ V :=
    { toEquiv := e.toLinearEquiv.toEquiv
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  exact u.completeSpace_iff.mpr inferInstance

end PositiveForm
end EnergyGeometry

/-- The normalized lifts form a Hilbert basis for the energy inner product.
Their coefficients simultaneously identify the entire image of the inclusion. -/
theorem energy_spectral_basis {E H : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (J : E →L[ℝ] H) (hJ : Function.Injective J)
    (e : HilbertBasis ℕ ℝ H) (ev : ℕ → ℝ) (hp : ∀ j, 0 < ev j)
    (v : ℕ → E) (hv : ∀ j, J (v j) = e j)
    (he : ∀ j u, inner ℝ (v j) u = ev j * inner ℝ (e j) (J u)) :
    ∃ b : HilbertBasis ℕ ℝ E,
      (∀ j, b j = (Real.sqrt (ev j))⁻¹ • v j) ∧
      (∀ u j, inner ℝ (b j) u = Real.sqrt (ev j) * inner ℝ (e j) (J u)) ∧
      (∀ u, HasSum (fun j => ev j * (inner ℝ (e j) (J u)) ^ 2) (inner ℝ u u)) ∧
      (∀ u : H, u ∈ Set.range J ↔ Summable (fun j => ev j * (inner ℝ (e j) u) ^ 2)) := by
  classical
  let w : ℕ → E := fun j => (Real.sqrt (ev j))⁻¹ • v j
  have hroot (j : ℕ) : Real.sqrt (ev j) ≠ 0 := (Real.sqrt_pos.mpr (hp j)).ne'
  have hc (u : E) (j : ℕ) : inner ℝ (w j) u =
      Real.sqrt (ev j) * inner ℝ (e j) (J u) := by
    dsimp [w]
    rw [real_inner_smul_left, he]
    have hval : (Real.sqrt (ev j))⁻¹ * ev j = Real.sqrt (ev j) := by
      apply (inv_mul_eq_iff_eq_mul₀ (hroot j)).mpr
      nlinarith [Real.sq_sqrt (hp j).le]
    rw [← mul_assoc, hval]
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [w]
    rw [real_inner_smul_left, real_inner_smul_right, he, hv,
      orthonormal_iff_ite.mp e.orthonormal i j]
    split_ifs with hij
    · subst j
      have hs := Real.sq_sqrt (hp i).le
      field_simp [hroot i]
      nlinarith
    · simp
  have hcomp : (Submodule.span ℝ (Set.range w)).orthogonal = ⊥ := by
    apply le_antisymm _ bot_le
    intro u hu
    have hcoef (j : ℕ) : inner ℝ (e j) (J u) = 0 := by
      have hz := hu (w j) (Submodule.subset_span ⟨j, rfl⟩)
      rw [hc] at hz
      exact (mul_eq_zero.mp hz).resolve_left (hroot j)
    have hzero : J u = J 0 := by
      rw [map_zero]
      apply e.repr.injective
      apply lp.ext
      funext j
      simp [e.repr_apply_apply, hcoef]
    exact hJ hzero
  let b : HilbertBasis ℕ ℝ E := HilbertBasis.mkOfOrthogonalEqBot hw hcomp
  have hb : (b : ℕ → E) = w := HilbertBasis.coe_mkOfOrthogonalEqBot hw hcomp
  have hcoeff (u : E) (j : ℕ) : inner ℝ (b j) u =
      Real.sqrt (ev j) * inner ℝ (e j) (J u) := by rw [hb]; exact hc u j
  have hsum (u : E) : HasSum (fun j => ev j * (inner ℝ (e j) (J u)) ^ 2)
      (inner ℝ u u) := by
    convert b.hasSum_inner_mul_inner u u using 1
    funext j
    rw [real_inner_comm (b j) u, hcoeff, ← pow_two, mul_pow, Real.sq_sqrt (hp j).le]
  refine ⟨b, fun j => congrFun hb j, hcoeff, hsum, ?_⟩
  intro u
  constructor
  · rintro ⟨x, rfl⟩
    exact (hsum x).summable
  · intro hu
    have hcℓ : Memℓp (fun j => Real.sqrt (ev j) * inner ℝ (e j) u) 2 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_pow,
        Real.sq_sqrt (hp _).le] using hu
    let c : lp (fun _ : ℕ => ℝ) 2 := ⟨fun j => Real.sqrt (ev j) * inner ℝ (e j) u, hcℓ⟩
    let x : E := b.repr.symm c
    refine ⟨x, ?_⟩
    apply e.repr.injective
    apply lp.ext
    funext j
    simp only [e.repr_apply_apply]
    apply mul_left_cancel₀ (hroot j)
    rw [← hcoeff, ← b.repr_apply_apply]
    change b.repr (b.repr.symm c) j = _
    rw [b.repr.apply_symm_apply]

/-- Density of a Hilbert basis is preserved by a continuous linear equivalence. -/
theorem dense_span_image {E V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ee : E ≃L[ℝ] V)
    (b : HilbertBasis ℕ ℝ E) :
    (Submodule.span ℝ (Set.range (fun j => ee (b j)))).topologicalClosure = ⊤ := by
  have hf : DenseRange ee.toContinuousLinearMap := ee.surjective.denseRange
  have hs := hf.topologicalClosure_map_submodule b.dense_span
  rw [Submodule.map_span, ← Set.range_comp] at hs
  exact hs

/-- Transfer the normalized energy basis and its weighted ℓ² image back to
the actual H¹₀ space, using the proved full-norm equivalence. -/
theorem form_resolution (m : ℕ) (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (A : MatrixField (m + 1))
    (hA : MemLp A ∞ (domainMeasure Ω)) (lam : ℝ) (hlam : 0 < lam)
    (hEll : Elliptic Ω A lam) (hsym : Symmetric Ω A)
    (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2)) (ha : IsCoefficientForm Ω A a)
    (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω)
    (hd : OperatorData Ω a e ev v) : FormData Ω A e ev v := by
  letI : NormedAddCommGroup (H ℝ Ω 1) := inferInstance
  letI : NormedSpace ℝ (H ℝ Ω 1) := inferInstance
  letI : NormedAddCommGroup (H10 ℝ Ω) := inferInstance
  letI : NormedSpace ℝ (H10 ℝ Ω) := inferInstance
  letI : InnerProductSpace ℝ (H10 ℝ Ω) := inferInstance
  letI : CompleteSpace (H10 ℝ Ω) := inferInstance
  obtain ⟨C, hC, _, hbridge⟩ := Dirichlet.form_bridge (by omega) Ω
    (Dirichlet.lipschitz_isBounded Ω hΩ)
  obtain ⟨B, hB, _, hco⟩ := hbridge A hA
  let B0 : H10 ℝ Ω →L[ℝ] H10 ℝ Ω →L[ℝ] ℝ :=
    B.bilinearComp (zeroInclusion Ω) (zeroInclusion Ω)
  have hB0 (u w : H10 ℝ Ω) : B0 u w = ellipticEnergyForm Ω A u.val w.val := hB u.val w.val
  have hsymB (u w : H10 ℝ Ω) : B0 u w = B0 w u := by
    rw [hB0, hB0, ← Dirichlet.form_apply Ω A hA, ← Dirichlet.form_apply Ω A hA]
    exact Dirichlet.form_symmetric Ω A hA hsym u.val w.val
  let c := lam / C ^ 2
  have hc : 0 < c := div_pos hlam (sq_pos_of_pos hC)
  have hlo (u : H10 ℝ Ω) : c * ‖u‖ ^ 2 ≤ B0 u u := hco lam hlam hEll u
  have hhi (u : H10 ℝ Ω) : B0 u u ≤ ‖B0‖ * ‖u‖ ^ 2 := by
    calc
      B0 u u ≤ ‖B0 u u‖ := le_abs_self _
      _ ≤ ‖B0‖ * ‖u‖ * ‖u‖ := B0.le_opNorm₂ u u
      _ = ‖B0‖ * ‖u‖ ^ 2 := by ring
  have hBnorm : 0 ≤ ‖B0‖ := norm_nonneg B0
  let q : EnergyGeometry.PositiveForm (H10 ℝ Ω) :=
    { form := B0
      symmetric := hsymB
      positive := fun u hu => (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hu))).trans_le (hlo u) }
  letI : CompleteSpace q.EnergySpace :=
    q.complete_energy c ‖B0‖ hc hBnorm hlo hhi
  let ee : q.EnergySpace ≃L[ℝ] H10 ℝ Ω := q.energyEquiv c ‖B0‖ hc hBnorm hlo hhi
  let J : q.EnergySpace →L[ℝ] Lp ℝ Ω 2 := (hZeroUnderlying Ω).comp ee.toContinuousLinearMap
  let ve : ℕ → q.EnergySpace := fun j => ee.symm (v j)
  have hJ : Function.Injective J := (DirichletResolvent.inclusion_injective Ω).comp ee.injective
  have hve (j : ℕ) : J (ve j) = e j := by
    change hZeroUnderlying Ω (ee (ee.symm (v j))) = e j
    rw [ee.apply_symm_apply]
    exact (hd.2.2.2.1 j).1
  have he (j : ℕ) (u : q.EnergySpace) : inner ℝ (ve j) u =
      ev j * inner ℝ (e j) (J u) := by
    have hv := (hd.2.2.2.1 j).1
    have hg : (hZeroUnderlying Ω (v j), ev j • e j) ∈ a.associatedOperator.graph :=
      hv ▸ (hd.2.2.2.1 j).2
    obtain ⟨hm, hrep⟩ := (a.mem_associated_graph _ _).mp hg
    have hu : hZeroUnderlying Ω (ee u) ∈ a.domain := by rw [ha.1]; exact ⟨ee u, rfl⟩
    calc
      inner ℝ (ve j) u = B0 (v j) (ee u) := by
        rw [q.inner_eq]
        change B0 (ee (ve j)) (ee u) = _
        rw [show ee (ve j) = v j from ee.apply_symm_apply _]
      _ = ellipticEnergyForm Ω A (v j).val (ee u).val := hB0 _ _
      _ = a.form ⟨hZeroUnderlying Ω (v j), hm⟩ ⟨hZeroUnderlying Ω (ee u), hu⟩ :=
        (ha.2 _ _ _ _).symm
      _ = inner ℝ (hZeroUnderlying Ω (ee u)) (ev j • e j) := hrep _
      _ = ev j * inner ℝ (e j) (J u) := by
        rw [inner_smul_right, real_inner_comm (e j) (hZeroUnderlying Ω (ee u))]
        rfl
  obtain ⟨b, hb, hcoeff, hsum, hrange⟩ := energy_spectral_basis J hJ e ev hd.1 ve hve he
  have hbV (j : ℕ) : ee (b j) = (Real.sqrt (ev j))⁻¹ • v j := by
    rw [hb, map_smul]
    exact congrArg ((Real.sqrt (ev j))⁻¹ • ·) (ee.apply_symm_apply _)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j
    change ellipticEnergyForm Ω A ((Real.sqrt (ev i))⁻¹ • v i).val
      ((Real.sqrt (ev j))⁻¹ • v j).val = _
    rw [← hbV i, ← hbV j, ← hB0]
    change inner ℝ (b i) (b j) = _
    exact orthonormal_iff_ite.mp b.orthonormal i j
  · have hs := dense_span_image ee b
    simpa only [hbV] using hs
  · intro u
    have hs := hsum (ee.symm u)
    change HasSum (fun j => ev j * (inner ℝ (e j) (hZeroUnderlying Ω (ee (ee.symm u)) )) ^ 2)
      (B0 (ee (ee.symm u)) (ee (ee.symm u))) at hs
    simpa only [ee.apply_symm_apply, hB0] using hs
  · intro u
    have hr : Set.range J = Set.range (hZeroUnderlying (𝕜 := ℝ) Ω) := by
      change Set.range ((hZeroUnderlying Ω) ∘ ee) = _
      rw [Set.range_comp, ee.surjective.range_eq, Set.image_univ]
    change u ∈ Set.range (hZeroUnderlying (𝕜 := ℝ) Ω) ↔ _
    rw [← hr]
    exact hrange u

/-- Dirichlet eigenbasis with both exact spectral domains and the complete
energy expansion, under precisely the manuscript's coefficient hypotheses. -/
theorem dirichlet_eigenbasis : Statement := by
  intro m Ω hΩ hne A hA lam hlam hEll hsym a ha
  obtain ⟨e, ev, v, hd⟩ := operator_resolution m Ω hΩ hne A hA lam hlam hEll hsym a ha
  exact ⟨e, ev, v, hd, form_resolution m Ω hΩ A hA lam hlam hEll hsym a ha e ev v hd⟩

end P201.DirichletEigenbasis
