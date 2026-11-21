import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OrderedSpectral.StrongKreinRutman
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OrderedSpectral.KreinRutmanExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace ExpandedFA.OrderedSpectral.StrongKreinRutman
open Set
open scoped ENNReal NNReal
open KreinRutmanExistence
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A boundary comparison rules out a Jordan chain directly. This proof uses
neither an order norm nor a norm bound on order intervals. -/
theorem no_jordan_chain : Spec.NoJordanChain.{u} := by
  intro X _ _ P hP hproper T hT μ u hμ hu heu
  rintro ⟨w, hw⟩
  have h0 : (0 : X) ∈ P :=
    ConvexCone.Pointed.of_nonempty_of_isClosed ⟨u, interior_subset hu⟩ hP
  obtain ⟨t, ht, hx⟩ := exists_pos_sub_smul_mem P hu w
  obtain ⟨s, _, hy, hboundary, _⟩ :=
    exists_boundary_ray P hP hx (neg_not_mem_of_interior P hproper hu)
  have hTy : T (u - t • w - s • u) ∈ P := positive_map_mem P h0 T hT hy
  have hi := interior_add_mem P (pos_smul_interior P ht hu) hTy
  have hTw : T w = μ • w + u := by simpa [add_comm] using (sub_eq_iff_eq_add.mp hw)
  have heq : t • u + T (u - t • w - s • u) =
      μ • (u - t • w - s • u) := by
    simp only [map_sub, map_smul, heu, hTw]
    module
  rw [heq] at hi
  apply hboundary
  simpa [smul_smul, hμ.ne'] using pos_smul_interior P (inv_pos.mpr hμ) hi

/-- Shifting a real eigenvector a short distance from the positive eigenvector
puts it in the cone, where the accepted uniqueness theorem applies. -/
lemma real_eigenvector_mem_line (P : ConvexCone ℝ X)
    (hP : IsClosed (P : Set X)) (hproper : (P : Set X) ≠ univ)
    (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {μ : ℝ} {u : X} (hμ : 0 < μ) (hu : u ∈ interior (P : Set X))
    (hu0 : u ≠ 0) (heu : T u = μ • u) {w : X} (hw : T w = μ • w) :
    w ∈ Submodule.span ℝ {u} := by
  obtain ⟨t, ht, hx⟩ := exists_pos_sub_smul_mem P hu w
  have hx0 : u - t • w ≠ 0 := by
    intro hz
    exact zero_not_mem_interior P hproper (hz ▸ hx)
  have he : T (u - t • w) = μ • (u - t • w) := by
    simp only [map_sub, map_smul, heu, hw]
    module
  obtain ⟨_, a, _, ha⟩ := cone_eigenvector_uniqueness X P hP hproper T hT μ u
    hμ hu hu0 heu μ (u - t • w) (interior_subset hx) hx0 he
  apply Submodule.mem_span_singleton.mpr
  refine ⟨(1 - a) / t, ?_⟩
  have heq : t • w = (1 - a) • u := by
    have := ha
    rw [sub_eq_iff_eq_add] at this
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq (by simpa [add_comm] using this.symm)
  calc
    ((1 - a) / t) • u = t⁻¹ • ((1 - a) • u) := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]
    _ = t⁻¹ • (t • w) := by rw [heq]
    _ = w := by simp [smul_smul, ht.ne']

/-- The no-chain statement together with the eigenline description eliminates
all higher generalized vectors, without a finite-dimensionality hypothesis. -/
theorem real_generalized_simplicity : Spec.RealGeneralizedSimplicity.{u} := by
  intro X _ _ P hP hproper T hT μ u hμ hu hu0 heu n hn
  let A : X →ₗ[ℝ] X := T - μ • LinearMap.id
  have hAu : A u = 0 := by simp [A, heu]
  have hstep : ∀ w : X, A w ∈ Submodule.span ℝ {u} → A w = 0 := by
    intro w hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    by_cases ha0 : a = 0
    · simpa [ha0] using ha.symm
    · exfalso
      apply no_jordan_chain X P hP hproper T hT μ u hμ hu heu
      refine ⟨a⁻¹ • w, ?_⟩
      change A (a⁻¹ • w) = u
      rw [map_smul, ← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hpow : ∀ k : ℕ, ∀ w : X, (A ^ k) w = 0 → w ∈ Submodule.span ℝ {u} := by
    intro k
    induction k with
    | zero =>
      intro w hw
      have hw0 : w = 0 := by simpa using hw
      simp [hw0]
    | succ k ih =>
      intro w hw
      have hAw : A w = 0 := hstep w (ih (A w) (by
        simpa only [pow_succ, Module.End.mul_apply] using hw))
      apply real_eigenvector_mem_line P hP hproper T hT hμ hu hu0 heu
      exact sub_eq_zero.mp hAw
  apply le_antisymm
  · intro w hw
    exact hpow n w hw
  · apply Submodule.span_le.mpr
    intro w hw
    have hwu : w = u := Set.mem_singleton_iff.mp hw
    subst w
    change (A ^ n) u = 0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Module.End.mul_apply, hAu]

/-- Each real coordinate of the complex unit ball lies in the real unit ball.
The complexified image therefore has closure in the product of two compact
real image closures. -/
theorem complexification_compact : Spec.ComplexificationCompact.{u} := by
  intro X _ _ T hT
  let K : Set X := closure (T '' Metric.closedBall (0 : X) 1)
  let e := Complexification.equivRealProd (X := X)
  have hK : IsCompact K := hT
  have hC : IsCompact (e.symm '' (K ×ˢ K)) := (hK.prod hK).image e.symm.continuous
  apply hC.of_isClosed_subset isClosed_closure
  apply hC.isClosed.closure_subset_iff.mpr
  rintro _ ⟨f, hf, rfl⟩
  have hf1 : ‖f‖ ≤ 1 := by simpa using hf
  have hcoord : ∀ z : ℂ, ‖z‖ = 1 → T (f z) ∈ K := by
    intro z hz
    apply subset_closure
    refine ⟨f z, ?_, rfl⟩
    have hn := ContinuousLinearMap.le_opNorm (show ℂ →L[ℝ] X from f) z
    change ‖f z‖ ≤ ‖f‖ * ‖z‖ at hn
    simpa using hn.trans (by simpa [hz] using hf1)
  refine ⟨(T (f 1), T (f Complex.I)), ⟨hcoord 1 norm_one, hcoord Complex.I Complex.norm_I⟩, ?_⟩
  exact e.symm_apply_apply (Complexification.extend T f)

/-- Power kernels commute with taking real coordinates. At the real eigenvalue
μ, both real and imaginary coordinates lie on the already proved eigenline. -/
theorem complex_generalized_simplicity : Spec.ComplexGeneralizedSimplicity.{u} := by
  intro X _ _ P hP hproper T hT μ u hμ hu hu0 heu n hn
  let A : X →ₗ[ℝ] X := T.toLinearMap - μ • LinearMap.id
  let B : Complexification X →ₗ[ℂ] Complexification X :=
    (Complexification.extend T).toLinearMap - (μ : ℂ) • LinearMap.id
  have heval : ∀ (f : Complexification X) (z : ℂ), (B f) z = A (f z) := by
    intro f z
    change (Complexification.extend T f - (μ : ℂ) • f) z = T (f z) - μ • f z
    rw [Complexification.sub_apply, Complexification.extend_apply,
      Complexification.ofReal_smul_apply]
  have hpow : ∀ k : ℕ, ∀ (f : Complexification X) (z : ℂ),
      ((B ^ k) f) z = (A ^ k) (f z) := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro f z
      simp only [pow_succ', Module.End.mul_apply, heval, ih]
  have hker := real_generalized_simplicity X P hP hproper T.toLinearMap hT
    μ u hμ hu hu0 heu n hn
  have hBu : B (Complexification.ofReal u) = 0 := by
    apply Complexification.ext
    intro z
    rw [heval]
    change T (z.re • u) - μ • (z.re • u) = 0
    rw [map_smul, heu]
    module
  apply le_antisymm
  · intro f hf
    have hcoord : ∀ z : ℂ, f z ∈ Submodule.span ℝ {u} := by
      intro z
      rw [← hker]
      change (A ^ n) (f z) = 0
      rw [← hpow n f z]
      have hf' : (B ^ n) f = 0 := hf
      rw [hf']
      rfl
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hcoord 1)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hcoord Complex.I)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(⟨a, b⟩ : ℂ), ?_⟩
    apply (Complexification.equivRealProd (X := X)).injective
    apply Prod.ext
    · change (((⟨a, b⟩ : ℂ) • Complexification.ofReal u) : Complexification X) 1 = f 1
      simp [Complexification.complex_smul_apply, Complexification.ofReal_apply, ha]
    · change (((⟨a, b⟩ : ℂ) • Complexification.ofReal u) : Complexification X) Complex.I = f Complex.I
      simp [Complexification.complex_smul_apply, Complexification.ofReal_apply, hb]
  · apply Submodule.span_le.mpr
    intro f hf
    have hfu : f = Complexification.ofReal u := Set.mem_singleton_iff.mp hf
    subst f
    change (B ^ n) (Complexification.ofReal u) = 0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Module.End.mul_apply, hBu]


/-- Positivity and an interior μ-eigenvector bound every real eigenvalue from
above. A maximal ray parameter is used instead of an order-norm estimate. -/
lemma real_eigenvalue_le (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (hproper : (P : Set X) ≠ univ) (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {μ ν : ℝ} {u w : X} (hμ : 0 < μ) (hu : u ∈ interior (P : Set X))
    (heu : T u = μ • u) (hw0 : w ≠ 0) (hew : T w = ν • w) : ν ≤ μ := by
  by_cases hν : 0 ≤ ν
  swap
  · linarith
  have hsali := forced_pointedness X P hproper T hT
  obtain ⟨x, hneg, hex⟩ : ∃ x : X, -x ∉ P ∧ T x = ν • x := by
    by_cases hn : -w ∈ P
    · refine ⟨-w, ?_, ?_⟩
      · simpa using (show w ∉ P from fun hp => hsali w hp hw0 hn)
      · simpa [map_neg, smul_neg] using congrArg Neg.neg hew
    · exact ⟨w, hn, hew⟩
  obtain ⟨s, hs, hy, _, hmax⟩ := exists_boundary_ray P hP hu hneg
  have h0 : (0 : X) ∈ P :=
    ConvexCone.Pointed.of_nonempty_of_isClosed ⟨u, interior_subset hu⟩ hP
  have hTy := positive_map_mem P h0 T hT hy
  have heq : μ • (u - (s * ν / μ) • x) = T (u - s • x) := by
    rw [map_sub, map_smul, heu, hex, smul_sub, smul_smul, smul_smul]
    congr 1
    congr 1
    field_simp
  have hmem : u - (s * ν / μ) • x ∈ P := by
    have hm := P.smul_mem (inv_pos.mpr hμ) hTy
    rw [← heq, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul] at hm
    exact hm
  have hb := hmax (s * ν / μ) (by positivity) hmem
  have hb' := (div_le_iff₀ hμ).mp hb
  nlinarith

/-- Applying the real comparison to T², and using simplicity to exclude
ν=-μ, gives the full strict comparison for real eigenvalues. -/
lemma real_eigenvalue_strict (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (hproper : (P : Set X) ≠ univ) (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {μ ν : ℝ} {u w : X} (hμ : 0 < μ) (hu : u ∈ interior (P : Set X))
    (hu0 : u ≠ 0) (heu : T u = μ • u) (hw0 : w ≠ 0)
    (hew : T w = ν • w) (hne : ν ≠ μ) : |ν| < μ := by
  let S := T.comp T
  have hS : ∀ x ∈ P, x ≠ 0 → S x ∈ interior (P : Set X) := by
    intro x hx hx0
    have hxi := hT x hx hx0
    exact hT (T x) (interior_subset hxi) (fun hz =>
      zero_not_mem_interior P hproper (hz ▸ hxi))
  have hSu : S u = (μ * μ) • u := by
    change T (T u) = _
    rw [heu, map_smul, heu, smul_smul]
  have hSw : S w = (ν * ν) • w := by
    change T (T w) = _
    rw [hew, map_smul, hew, smul_smul]
  have hμ2 : 0 < μ * μ := mul_pos hμ hμ
  have hle := real_eigenvalue_le P hP hproper S hS hμ2 hu hSu hw0 hSw
  have hneq : ν * ν ≠ μ * μ := by
    intro heq
    have hmem := real_eigenvector_mem_line P hP hproper S hS hμ2 hu hu0 hSu
      (show S w = (μ * μ) • w by rw [hSw, heq])
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have he : ν • w = μ • w := by
      rw [← hew, ← ha, map_smul, heu]
      module
    exact hne ((smul_left_injective ℝ hw0) he)
  have hlt := lt_of_le_of_ne hle hneq
  have hsq := sq_abs ν
  nlinarith [abs_nonneg ν]
/-- Expansion in real coordinates for the concrete complexification. -/
lemma complexification_apply_coordinates (f : Complexification X) (z : ℂ) :
    f z = z.re • f 1 + z.im • f Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by simp
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz
    _ = _ := by rw [Complexification.apply_add,
      Complexification.apply_real_smul, Complexification.apply_real_smul]

/-- Scalar multiplication has the usual real 2-by-2 rotation/dilation matrix. -/
lemma complexification_smul_coordinates (c : ℂ) (f : Complexification X) :
    (c • f : Complexification X) 1 = c.re • f 1 - c.im • f Complex.I ∧
    (c • f : Complexification X) Complex.I = c.im • f 1 + c.re • f Complex.I := by
  constructor
  · rw [Complexification.complex_smul_apply, complexification_apply_coordinates]
    simp [sub_eq_add_neg]
  · rw [Complexification.complex_smul_apply, complexification_apply_coordinates]
    simp

/-- The real-coordinate comparison suffices for the entire unchanged source
conclusion. The coordinate comparison is the explicit antecedent of this assembly
theorem and is discharged below in `coordinate_spectral_gap`. -/
theorem gap_implies_full_theorem : Spec.GapImpliesFullTheorem.{u} := by
  intro hgap X _ _ _ P hP hsolid hproper T hcompact hT
  let Tb : X →L[ℝ] X :=
    ⟨T, ((Compactness.compact_iff_isCompactOperator T).mp hcompact).continuous⟩
  have hTb : Compactness.DefinitionsSpec.IsCompactLinearMapValue Tb.toLinearMap := hcompact
  have hTc := complexification_compact X Tb hTb
  let Tc := Complexification.extend Tb
  obtain ⟨μ, u, hμ, hu, hu0, heu⟩ :=
    positive_eigenpair X P hP hsolid hproper T hcompact hT
  have huC0 : Complexification.ofReal u ≠ 0 := by
    intro hz
    have hz1 := congrArg (fun f : Complexification X => f 1) hz
    apply hu0
    simpa using hz1
  have heuC : Tc (Complexification.ofReal u) = (μ : ℂ) • Complexification.ofReal u := by
    apply Complexification.ext
    intro z
    change Tb (z.re • u) = ((μ : ℂ) • Complexification.ofReal u) z
    have heu' : Tb u = μ • u := heu
    rw [Complexification.ofReal_smul_apply, Complexification.ofReal_apply, map_smul, heu']
    module
  have hgapC : ∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ (μ : ℂ) →
      (∃ z : Complexification X, z ≠ 0 ∧ Tc z = ζ • z) → ‖ζ‖ < μ := by
    intro ζ hζ0 hζμ
    rintro ⟨z, hz0, hz⟩
    have hcoords := complexification_smul_coordinates ζ z
    have hx : Tb (z 1) = ζ.re • z 1 - ζ.im • z Complex.I := by
      have he := congrArg (fun f : Complexification X => f 1) hz
      exact he.trans hcoords.1
    have hy : Tb (z Complex.I) = ζ.im • z 1 + ζ.re • z Complex.I := by
      have he := congrArg (fun f : Complexification X => f Complex.I) hz
      exact he.trans hcoords.2
    have hxy : z 1 ≠ 0 ∨ z Complex.I ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hz0
      apply (Complexification.equivRealProd (X := X)).injective
      exact Prod.ext hn.1 hn.2
    exact hgap X P hP hproper Tb hTb hT μ u hμ hu hu0 heu ζ (z 1) (z Complex.I)
      hxy hx hy hζ0 hζμ
  have hspec : (μ : ℂ) ∈ spectrum ℂ Tc :=
    (Fredholm.compact_nonzero_spectrum_iff_eigenvalue Tc hTc (μ : ℂ)
      (by exact_mod_cast hμ.ne')).mpr ⟨Complexification.ofReal u, huC0, heuC⟩
  have hradius : spectralRadius ℂ Tc = ENNReal.ofReal μ := by
    rw [spectralRadius_eq_of_unital]
    apply le_antisymm
    · refine iSup₂_le fun ζ hζ => ?_
      have hbound : ‖ζ‖ ≤ μ := by
        by_cases hζ0 : ζ = 0
        · simpa [hζ0] using hμ.le
        by_cases hζμ : ζ = (μ : ℂ)
        · simp [hζμ, abs_of_pos hμ]
        exact (hgapC ζ hζ0 hζμ
          ((Fredholm.compact_nonzero_spectrum_iff_eigenvalue Tc hTc ζ hζ0).mp hζ)).le
      rw [ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_le_ofReal hbound
    · have heq : (‖(μ : ℂ)‖₊ : ℝ≥0∞) = ENNReal.ofReal μ := by
        rw [ENNReal.coe_nnreal_eq]
        congr 1
        exact Complex.norm_of_nonneg hμ.le
      rw [← heq]
      exact le_iSup_of_le (μ : ℂ) (le_iSup_of_le hspec le_rfl)
  refine ⟨Tb, rfl, hTc, μ, u, hμ, hu, hu0, heu, ?_, ?_, hgapC, hradius⟩
  · exact cone_eigenvector_uniqueness X P hP hproper T hT μ u hμ hu hu0 heu
  · exact complex_generalized_simplicity X P hP hproper Tb hT μ u hμ hu hu0 heu

/-- The two real coordinate equations separate all real-eigenvalue cases
without any independence assumption on the coordinates. -/
theorem nonreal_gap_implies_gap : Spec.NonrealGapImpliesGap.{u} := by
  intro hgap X _ _ _ P hP hproper T hcompact hT μ u hμ hu hu0 heu ζ x y hxy hx hy hζ0 hζμ
  by_cases him : ζ.im = 0
  · have hζ : ζ = (ζ.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hne : ζ.re ≠ μ := by
      intro he
      exact hζμ (hζ.trans (congrArg (fun a : ℝ => (a : ℂ)) he))
    have hx' : T x = ζ.re • x := by simpa [him] using hx
    have hy' : T y = ζ.re • y := by simpa [him] using hy
    have hbound : |ζ.re| < μ := by
      rcases hxy with hx0 | hy0
      · exact real_eigenvalue_strict P hP hproper T.toLinearMap hT hμ hu hu0 heu hx0 hx' hne
      · exact real_eigenvalue_strict P hP hproper T.toLinearMap hT hμ hu hu0 heu hy0 hy' hne
    rw [hζ, Complex.norm_real, Real.norm_eq_abs]
    exact hbound
  · exact hgap X P hP hproper T hcompact hT μ u hμ hu hu0 heu ζ x y him hxy hx hy

/-- Assembly of the full theorem from nonreal comparison; all real eigenvalues
are handled by the preceding reduction. -/
theorem nonreal_gap_implies_full_theorem : Spec.NonrealGapImpliesFullTheorem.{u} := by
  intro hgap
  exact gap_implies_full_theorem (nonreal_gap_implies_gap hgap)

/-- A real linear intertwiner with a genuinely nonreal scalar is either zero
or injective. In particular the two real coordinates of an eigenvector are
independent. -/
lemma nonreal_intertwiner_injective (A : ℂ →L[ℝ] X) (T : X →L[ℝ] X)
    (ζ : ℂ) (hb : ζ.im ≠ 0)
    (hA : ∀ c, T (A c) = A (star ζ * c))
    (hne : A 1 ≠ 0 ∨ A Complex.I ≠ 0) : Function.Injective A := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  change A c = 0 at hc
  by_contra hc0
  have hIc : A (Complex.I * c) = 0 := by
    have he : star ζ * c = ζ.re • c - ζ.im • (Complex.I * c) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
    have ht := hA c
    rw [hc, map_zero, he, map_sub, map_smul, map_smul, hc, smul_zero,
      zero_sub] at ht
    have hz : ζ.im • A (Complex.I * c) = 0 := neg_eq_zero.mp ht.symm
    exact (smul_eq_zero.mp hz).resolve_left hb
  have hall : ∀ d : ℂ, A (d * c) = 0 := by
    intro d
    have he : d * c = d.re • c + d.im • (Complex.I * c) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
    rw [he, map_add, map_smul, map_smul, hc, hIc, smul_zero, smul_zero, add_zero]
  rcases hne with h1 | hI
  · exact h1 (by simpa [hc0] using hall c⁻¹)
  · exact hI (by simpa [mul_assoc, hc0] using hall (Complex.I * c⁻¹))

/-- A nonreal invariant plane has no nonzero vector in the cone. Pulling the
cone back to the scalar plane permits use of finite-dimensional compactness
and the already proved positive-eigenpair theorem. -/
lemma nonreal_plane_disjoint (P : ConvexCone ℝ X)
    (hP : IsClosed (P : Set X)) (hproper : (P : Set X) ≠ univ)
    (T : X →L[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    (A : ℂ →L[ℝ] X) (hAi : Function.Injective A)
    (ζ : ℂ) (hb : ζ.im ≠ 0) (hA : ∀ c, T (A c) = A (star ζ * c)) :
    ∀ c : ℂ, A c ∈ P → c = 0 := by
  intro c hc
  by_contra hc0
  let Q : ConvexCone ℝ ℂ := P.comap A.toLinearMap
  let S : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ (star ζ)
  have hQclosed : IsClosed (Q : Set ℂ) := hP.preimage A.continuous
  have hpre : A ⁻¹' interior (P : Set X) ⊆ interior (Q : Set ℂ) :=
    (A.continuous.isOpen_preimage _ isOpen_interior).subset_interior_iff.mpr
      (preimage_mono interior_subset)
  have hAc0 : A c ≠ 0 := by simpa using hAi.ne hc0
  have hsolid : (interior (Q : Set ℂ)).Nonempty :=
    ⟨S c, hpre (by change A (star ζ * c) ∈ interior (P : Set X); rw [← hA]; exact hT _ hc hAc0)⟩
  have hQproper : (Q : Set ℂ) ≠ univ := by
    intro hQ
    have hs := forced_pointedness X P hproper T.toLinearMap hT
    have h1 : A 1 ∈ P := by change (1 : ℂ) ∈ (Q : Set ℂ); rw [hQ]; trivial
    have hn : -(A 1) ∈ P := by
      rw [← map_neg]; change (-1 : ℂ) ∈ (Q : Set ℂ); rw [hQ]; trivial
    exact hs _ h1 (by simpa using hAi.ne (one_ne_zero : (1 : ℂ) ≠ 0)) hn
  have hScompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue S.toLinearMap :=
    ((isCompact_closedBall (0 : ℂ) 1).image S.continuous).closure
  have hS : ∀ z ∈ Q, z ≠ 0 → S z ∈ interior (Q : Set ℂ) := by
    intro z hz hz0
    apply hpre
    change A (star ζ * z) ∈ interior (P : Set X)
    rw [← hA]
    exact hT _ hz (by simpa using hAi.ne hz0)
  obtain ⟨ρ, z, _, _, hz0, he⟩ :=
    positive_eigenpair ℂ Q hQclosed hsolid hQproper S.toLinearMap hScompact hS
  have he' : star ζ * z = (ρ : ℂ) * z := by simpa [S, Complex.real_smul] using he
  have heζ : star ζ = (ρ : ℂ) := mul_right_cancel₀ hz0 he'
  have hi := congrArg Complex.im heζ
  simp only [Complex.star_def, Complex.conj_im, Complex.ofReal_im] at hi
  exact hb (neg_eq_zero.mp hi)


/-- An affine section in a scalar plane disjoint from the cone is compact.
Only the scalar unit circle is used for the bound: its image has uniformly
positive distance from the closed cone. Ambient order intervals need not be
bounded in the original norm. -/
lemma compact_affine_section (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    {u : X} (hu : u ∈ interior (P : Set X)) (A : ℂ →L[ℝ] X)
    (hdis : ∀ c : ℂ, A c ∈ P → c = 0) :
    IsCompact {c : ℂ | u + A c ∈ P} := by
  have hPne : (P : Set X).Nonempty := ⟨u, interior_subset hu⟩
  have hdistpos : ∀ c ∈ Metric.sphere (0 : ℂ) 1,
      0 < Metric.infDist (A c) (P : Set X) := by
    intro c hc
    apply (hP.notMem_iff_infDist_pos hPne).mp
    intro hm
    have hc0 := hdis c hm
    simp [hc0] at hc
  obtain ⟨δ, hδ, hbound⟩ := (isCompact_sphere (0 : ℂ) 1).exists_forall_le'
    ((Metric.continuous_infDist_pt (s := (P : Set X))).comp A.continuous).continuousOn hdistpos
  have hb : Bornology.IsBounded {c : ℂ | u + A c ∈ P} := by
    apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨‖u‖ / δ, ?_⟩
    intro c hc
    by_cases hc0 : c = 0
    · simp [hc0, div_nonneg (norm_nonneg u) hδ.le]
    have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    have hn' : 0 < ‖c‖⁻¹ := inv_pos.mpr hn
    have hsphere : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : ℂ) 1 := by
      simp [hn.ne']
    have hmem : ‖c‖⁻¹ • u + A (‖c‖⁻¹ • c) ∈ P := by
      simpa only [map_smul, smul_add] using P.smul_mem hn' hc
    have hd : δ ≤ ‖c‖⁻¹ * ‖u‖ := by
      calc
        δ ≤ Metric.infDist (A (‖c‖⁻¹ • c)) (P : Set X) := hbound _ hsphere
        _ ≤ dist (A (‖c‖⁻¹ • c)) (‖c‖⁻¹ • u + A (‖c‖⁻¹ • c)) :=
          Metric.infDist_le_dist_of_mem hmem
        _ = ‖c‖⁻¹ * ‖u‖ := by
          rw [dist_eq_norm]
          have he : A (‖c‖⁻¹ • c) - (‖c‖⁻¹ • u + A (‖c‖⁻¹ • c)) = -(‖c‖⁻¹ • u) := by abel
          rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hn']
    apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_right hd hn.le
    have he : (‖c‖⁻¹ * ‖u‖) * ‖c‖ = ‖u‖ := by field_simp
    rw [he] at hh
    simpa [mul_comm] using hh
  exact Metric.isCompact_of_isClosed_isBounded
    (hP.preimage (continuous_const.add A.continuous)) hb

/-- The affine section of a nonreal eigenplane is compact, and strong positivity
sends a point of maximal scalar radius into its interior. This forces strict
contraction of the scalar radius after dividing by the principal eigenvalue. -/
theorem nonreal_coordinate_spectral_gap : Spec.NonrealCoordinateSpectralGap.{u} := by
  intro X _ _ _ P hP hproper T _hcompact hT μ u hμ hu hu0 heu ζ x y hb hxy hx hy
  let A : ℂ →L[ℝ] X := Complex.reCLM.smulRight x + Complex.imCLM.smulRight y
  have hA : ∀ c, T (A c) = A (star ζ * c) := by
    intro c
    simp only [A, add_apply, ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      map_add, map_smul, hx, hy, Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    module
  have hAi : Function.Injective A := nonreal_intertwiner_injective A T ζ hb hA (by
    simpa [A] using hxy)
  have hdis : ∀ c : ℂ, A c ∈ P → c = 0 :=
    nonreal_plane_disjoint P hP hproper T hT A hAi ζ hb hA
  let S : Set ℂ := {c : ℂ | u + A c ∈ P}
  have hS : IsCompact S := compact_affine_section P hP hu A hdis
  have h0S : (0 : ℂ) ∈ S := by simpa [S] using interior_subset hu
  obtain ⟨c, hc, hmax⟩ := hS.exists_isMaxOn ⟨0, h0S⟩ continuous_norm.continuousOn
  have hc0 : c ≠ 0 := by
    obtain ⟨t, ht, hmem⟩ := exists_pos_sub_smul_mem P hu (A 1)
    have hmem' : (-t : ℂ) ∈ S := by
      change u + A (-t : ℂ) ∈ P
      have he : (-t : ℂ) = -t • (1 : ℂ) := by simp
      rw [he, map_smul, neg_smul, ← sub_eq_add_neg]
      exact interior_subset hmem
    intro he
    have hn : ‖(-t : ℂ)‖ ≤ ‖c‖ := hmax hmem'
    rw [he, norm_zero] at hn
    have hz : (-t : ℂ) = 0 := norm_le_zero_iff.mp hn
    have ht0 : t = 0 := Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hz)
    exact ht.ne' ht0
  have hv0 : u + A c ≠ 0 := by
    intro he
    have he' : A (-c) = u := by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left he).symm
    have hh := hdis (-c) (he' ▸ interior_subset hu)
    exact hc0 (neg_eq_zero.mp hh)
  let d : ℂ := μ⁻¹ • (star ζ * c)
  have hdint : u + A d ∈ interior (P : Set X) := by
    have hpos := pos_smul_interior P (inv_pos.mpr hμ) (hT _ hc hv0)
    have he : μ⁻¹ • T (u + A c) = u + A d := by
      rw [map_add, heu, hA, smul_add, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
      simp only [d, map_smul]
    exact he ▸ hpos
  obtain ⟨t, ht, hmem⟩ := exists_pos_sub_smul_mem P hdint (-(A d))
  have hmem' : (1 + t) • d ∈ S := by
    change u + A ((1 + t) • d) ∈ P
    have he : u + A ((1 + t) • d) = u + A d - t • (-A d) := by
      rw [map_smul, add_smul, one_smul, smul_neg]
      abel
    exact he ▸ interior_subset hmem
  have hbound : ‖(1 + t) • d‖ ≤ ‖c‖ := hmax hmem'
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)] at hbound
  have hdc : ‖d‖ < ‖c‖ := by
    have hdn := norm_nonneg d
    have hcn := norm_pos_iff.mpr hc0
    nlinarith
  have hnorm : ‖d‖ = μ⁻¹ * ‖ζ‖ * ‖c‖ := by
    simp [d, Real.norm_eq_abs, hμ.le, mul_assoc]
  rw [hnorm] at hdc
  have hh : μ⁻¹ * ‖ζ‖ < 1 := by
    exact (mul_lt_mul_iff_left₀ (norm_pos_iff.mpr hc0)).mp (by simpa using hdc)
  have hh' := (mul_lt_mul_iff_right₀ hμ).mpr hh
  simpa [mul_assoc, hμ.ne', mul_comm, mul_left_comm] using hh'

/-- Strict modulus comparison for every other nonzero eigenvalue, including
all real and genuinely nonreal coordinate configurations. -/
theorem coordinate_spectral_gap : Spec.CoordinateSpectralGap.{u} :=
  nonreal_gap_implies_gap nonreal_coordinate_spectral_gap

/-- Strong Krein--Rutman on a closed solid proper cone, with complex algebraic
simplicity, a strict spectral gap, and the complex spectral-radius identity.
All compactness and norm statements use the original Banach-space topology. -/
theorem strong_krein_rutman : Spec.FullTheorem.{u} :=
  gap_implies_full_theorem coordinate_spectral_gap

end ExpandedFA.OrderedSpectral.StrongKreinRutman
