import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
LA-solvable-projective-fixed, source lines 2953–2981.

The spectral limit uses generalized eigenspaces and a finite exponential
polynomial on each component, allowing arbitrary eigenvalue multiplicities.
The fixed-point argument inducts through a codimension-one ideal. Its fixed
locus is invariant because ideal weight spaces are ambient Lie submodules.
-/

universe u v

namespace LieAlgebrasAndRepresentations.SolvableProjectiveFixed

open scoped LinearAlgebra.Projectivization Topology
open Filter

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The quotient map from nonzero vectors has the usual continuity. -/
theorem continuous_projective_mk :
    Continuous (Projectivization.mk' ℂ : {v : V // v ≠ 0} → Projectivization ℂ V) :=
  continuous_quotient_mk'

/-- Scaling by a nonzero scalar is a homeomorphism of the nonzero vectors. -/
private def nonzeroScale (a : ℂˣ) : {v : V // v ≠ 0} ≃ₜ {v : V // v ≠ 0} :=
  (Homeomorph.smul a : V ≃ₜ V).subtype (fun _ => (smul_ne_zero_iff_ne a).symm)

/-- The projection onto projective space is open. -/
theorem isOpenMap_projective_mk :
    IsOpenMap (Projectivization.mk' ℂ : {v : V // v ≠ 0} → Projectivization ℂ V) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  have he : Projectivization.mk' ℂ ⁻¹' (Projectivization.mk' ℂ '' U) =
      ⋃ a : ℂˣ, nonzeroScale a '' U := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, he⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ w.property v.property).mp he
      refine ⟨a⁻¹, w, hw, Subtype.ext ?_⟩
      change a⁻¹ • w.val = v.val
      rw [← ha, inv_smul_smul]
    · rintro ⟨a, w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      exact ⟨a⁻¹, inv_smul_smul a w.val⟩
  change IsOpen (Projectivization.mk' ℂ ⁻¹' (Projectivization.mk' ℂ '' U))
  rw [he]
  exact isOpen_iUnion fun a => (nonzeroScale a).isOpenMap _ hU

/-- Proportionality can be checked by the two-by-two minors in any basis. -/
theorem projective_eq_iff_minors {ι : Type*} (b : Module.Basis ι ℂ V)
    (v w : {v : V // v ≠ 0}) :
    Projectivization.mk' ℂ v = Projectivization.mk' ℂ w ↔
      ∀ i j, b.repr v.val i * b.repr w.val j = b.repr v.val j * b.repr w.val i := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ v.property w.property).mp h
    intro i j
    rw [← ha]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, b.repr w.val i ≠ 0 := by
      by_contra! hh
      apply w.property
      apply b.repr.injective
      ext i
      simpa using hh i
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ v.property w.property).mpr
    refine ⟨b.repr v.val i / b.repr w.val i, b.repr.injective ?_⟩
    ext j
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (div_mul_eq_mul_div _ _ _).trans ((div_eq_iff hi).mpr (h i j))

/-- The usual complex projective space is Hausdorff, also in dimension zero. -/
instance projectiveT2Space : T2Space (Projectivization ℂ V) := by
  have hq : IsOpenQuotientMap
      (Projectivization.mk' ℂ : {v : V // v ≠ 0} → Projectivization ℂ V) :=
    .of_isOpenMap_isQuotientMap isOpenMap_projective_mk isQuotientMap_quotient_mk'
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  let b := Module.finBasis ℂ V
  have he : {q : {v : V // v ≠ 0} × {v : V // v ≠ 0} |
      Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} =
      ⋂ i, ⋂ j, {q | b.repr q.1.val i * b.repr q.2.val j =
        b.repr q.1.val j * b.repr q.2.val i} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, projective_eq_iff_minors b]
  rw [he]
  have hc (i) : Continuous (fun v : {v : V // v ≠ 0} => b.repr v.val i) :=
    (b.coord i).continuous_of_finiteDimensional.comp continuous_subtype_val
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((hc i).comp continuous_fst |>.mul ((hc j).comp continuous_snd))
      ((hc j).comp continuous_fst |>.mul ((hc i).comp continuous_snd))

/-- Convergent nonzero representatives give convergent projective points. -/
theorem tendsto_projective_mk {α : Type*} {l : Filter α} {f : α → V}
    {w : V} (hf : ∀ t, f t ≠ 0) (hw : w ≠ 0) (h : Tendsto f l (𝓝 w)) :
    Tendsto (fun t => Projectivization.mk ℂ (f t) (hf t)) l
      (𝓝 (Projectivization.mk ℂ w hw)) := by
  exact (continuous_projective_mk.tendsto ⟨w, hw⟩).comp (tendsto_subtype_rng.mpr h)

/-- A single complex scaling separates the real parts of every distinct
member of a finite spectrum. Repeated eigenvalues require no separation. -/
theorem exists_spectral_rotation (S : Finset ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (c * a).re ≠ (c * b).re := by
  classical
  let F : Finset ℝ := (S.product S).image
    (fun q : ℂ × ℂ => (q.1.re - q.2.re) / (q.1.im - q.2.im))
  obtain ⟨t, ht⟩ := F.exists_notMem
  refine ⟨1 + (t : ℂ) * Complex.I, ?_, ?_⟩
  · intro hc
    have := congrArg Complex.re hc
    simpa using this
  · intro a ha b hb hab heq
    have hreal : a.re - t * a.im = b.re - t * b.im := by
      simpa [Complex.mul_re, Complex.add_re, Complex.mul_im] using heq
    have him : a.im - b.im ≠ 0 := by
      intro hi
      apply hab
      apply Complex.ext
      · have him' : a.im = b.im := sub_eq_zero.mp hi
        rw [him'] at hreal
        linarith
      · exact sub_eq_zero.mp hi
    apply ht
    apply Finset.mem_image.mpr
    refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
    apply (div_eq_iff him).mpr
    dsimp
    linarith

/-- Every vector on an invariant projective line is an eigenvector with one scalar. -/
theorem isEigenline_iff (A : Module.End ℂ V) (p : Projectivization ℂ V) :
    IsEigenline A p ↔ ∃ μ : ℂ, A p.rep = μ • p.rep := by
  unfold IsEigenline
  rw [p.submodule_eq]
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp
      (h p.rep (Submodule.mem_span_singleton_self _))
    exact ⟨μ, hμ.symm⟩
  · rintro ⟨μ, hμ⟩ v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hμ, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The definition is independent of the chosen representative. -/
theorem isEigenline_mk_iff (A : Module.End ℂ V) (v : V) (hv : v ≠ 0) :
    IsEigenline A (Projectivization.mk ℂ v hv) ↔ ∃ μ : ℂ, A v = μ • v := by
  change (∀ w ∈ ℂ ∙ v, A w ∈ ℂ ∙ v) ↔ _
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp
      (h v (Submodule.mem_span_singleton_self _))
    exact ⟨μ, hμ.symm⟩
  · rintro ⟨μ, hμ⟩ w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hμ, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- For a nonzero second vector, vanishing minors characterize its span,
including when the first vector is zero. -/
theorem exists_smul_iff_minors {ι : Type*} (b : Module.Basis ι ℂ V)
    (v w : V) (hw : w ≠ 0) :
    (∃ a : ℂ, v = a • w) ↔
      ∀ i j, b.repr v i * b.repr w j = b.repr v j * b.repr w i := by
  constructor
  · rintro ⟨a, rfl⟩ i j
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, b.repr w i ≠ 0 := by
      by_contra! hh
      apply hw
      apply b.repr.injective
      ext i
      simpa using hh i
    refine ⟨b.repr v i / b.repr w i, (b.repr.injective ?_).symm⟩
    ext j
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (div_mul_eq_mul_div _ _ _).trans ((div_eq_iff hi).mpr (h i j))

/-- Infinitesimal fixed lines form a closed subset of projective space. -/
theorem isClosed_eigenlines (A : Module.End ℂ V) :
    IsClosed {p : Projectivization ℂ V | IsEigenline A p} := by
  have hq : Topology.IsQuotientMap
      (Projectivization.mk' ℂ : {v : V // v ≠ 0} → Projectivization ℂ V) :=
    isQuotientMap_quotient_mk'
  apply hq.isClosed_preimage.mp
  let b := Module.finBasis ℂ V
  have he : Projectivization.mk' ℂ ⁻¹' {p | IsEigenline A p} =
      ⋂ i, ⋂ j, {v : {v : V // v ≠ 0} |
        b.repr (A v.val) i * b.repr v.val j = b.repr (A v.val) j * b.repr v.val i} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Projectivization.mk'_eq_mk,
      isEigenline_mk_iff, Set.mem_iInter, ← exists_smul_iff_minors b _ _ v.property]
  rw [he]
  have hc (i) : Continuous (fun v : {v : V // v ≠ 0} => b.repr v.val i) :=
    (b.coord i).continuous_of_finiteDimensional.comp continuous_subtype_val
  have hA (i) : Continuous (fun v : {v : V // v ≠ 0} => b.repr (A v.val) i) :=
    (b.coord i).continuous_of_finiteDimensional.comp
      (A.continuous_of_finiteDimensional.comp continuous_subtype_val)
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((hA i).mul (hc j)) ((hA j).mul (hc i))

/-- The action agrees with applying the actual operator exponential to a vector. -/
theorem projectiveFlow_mk (A : Module.End ℂ V) (z : ℂ) (v : V) (hv : v ≠ 0) :
    projectiveFlow A z (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (exponential A z v)
        (fun h => hv (exponential_injective A z (by simpa using h))) := rfl

/-- A nonzero normalized vector limit stays in every closed invariant
projective set. Normalization is allowed to vanish at exceptional times. -/
theorem mem_of_tendsto_scaled_exponential {α : Type*} {l : Filter α} [l.NeBot]
    (A : Module.End ℂ V) (p : Projectivization ℂ V)
    (X : Set (Projectivization ℂ V)) (hX : IsClosed X)
    (z r : α → ℂ) (horbit : ∀ t, projectiveFlow A (z t) p ∈ X)
    (w : V) (hw : w ≠ 0)
    (hlim : Tendsto (fun t => r t • exponential A (z t) p.rep) l (𝓝 w)) :
    Projectivization.mk ℂ w hw ∈ X := by
  classical
  let f := fun t => r t • exponential A (z t) p.rep
  have hne : ∀ᶠ t in l, f t ≠ 0 :=
    hlim.eventually (isOpen_compl_singleton.mem_nhds hw)
  let g : α → {v : V // v ≠ 0} :=
    fun t => if h : f t ≠ 0 then ⟨f t, h⟩ else ⟨w, hw⟩
  have hgf : (fun t => (g t).val) =ᶠ[l] f := by
    filter_upwards [hne] with t ht
    simp [g, ht]
  have hg : Tendsto g l (𝓝 ⟨w, hw⟩) :=
    tendsto_subtype_rng.mpr (hlim.congr' hgf.symm)
  apply hX.mem_of_tendsto ((continuous_projective_mk.tendsto ⟨w, hw⟩).comp hg)
  filter_upwards [hne] with t ht
  change Projectivization.mk' ℂ (g t) ∈ X
  simp only [g, dite_eq_left ht]
  have heq : Projectivization.mk ℂ (f t) ht = projectiveFlow A (z t) p := by
    rw [← p.mk_rep, projectiveFlow_mk]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨r t, rfl⟩
  change Projectivization.mk ℂ (f t) ht ∈ X
  rw [heq]
  exact horbit t

/-- The only analytic input needed by the one-operator fixed-point argument
is the explicitly specified normalized spectral limit. This is a reduction,
not an assumption in the final fixed-point specification. -/
theorem eigenline_in_compact_of_spectral_limit
    (hlimit : Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed.spectral_jordan_limit_type.{v})
    (A : Module.End ℂ V) (X : Set (Projectivization ℂ V))
    (hne : X.Nonempty) (hX : IsCompact X)
    (hflow : ∀ z p, p ∈ X → projectiveFlow A z p ∈ X) :
    ∃ p ∈ X, IsEigenline A p := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨c, μ, m, w, _, hw, heigen, hlim⟩ := hlimit A p.rep p.rep_nonzero
  refine ⟨Projectivization.mk ℂ w hw, ?_, (isEigenline_mk_iff A w hw).mpr ⟨μ, heigen⟩⟩
  exact mem_of_tendsto_scaled_exponential A p X hX.isClosed
    (fun t : ℝ => (t : ℂ) * c)
    (fun t : ℝ => Complex.exp (-(t : ℂ) * c * μ) / (t : ℂ) ^ m)
    (fun t => hflow _ _ hp) w hw hlim

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- Infinitesimal fixed points are precisely common eigenlines, with scalars
allowed to depend on the Lie algebra element. -/
theorem isFixed_iff (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (p : Projectivization ℂ V) :
    IsFixed ρ p ↔ ∀ x, ∃ μ : ℂ, ρ x p.rep = μ • p.rep := by
  simp only [IsFixed, isEigenline_iff]

/-- The simultaneous infinitesimal fixed-point set is closed. -/
theorem isClosed_fixedPoints (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) :
    IsClosed {p : Projectivization ℂ V | IsFixed ρ p} := by
  have he : {p : Projectivization ℂ V | IsFixed ρ p} =
      ⋂ x : L, {p | IsEigenline (ρ x) p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, IsFixed]
  rw [he]
  exact isClosed_iInter fun x => isClosed_eigenlines (ρ x)

/-- The induction base: a zero Lie algebra fixes every projective point. -/
theorem isFixed_of_subsingleton [Subsingleton L]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (p : Projectivization ℂ V) : IsFixed ρ p := by
  intro x v hv
  have hx : x = 0 := Subsingleton.elim _ _
  simp only [hx, map_zero, LinearMap.zero_apply]
  exact p.submodule.zero_mem

/-- The fixed-point conclusion in the zero-dimensional-algebra base case. -/
theorem fixed_point_of_subsingleton [Subsingleton L]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (X : Set (Projectivization ℂ V))
    (hX : X.Nonempty) : ∃ p ∈ X, IsFixed ρ p := by
  obtain ⟨p, hp⟩ := hX
  exact ⟨p, hp, isFixed_of_subsingleton ρ p⟩

/-- Exponentiating an operator preserves every invariant linear subspace.
Closedness is automatic in finite dimension. -/
theorem exponential_mem_submodule (A : Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ v ∈ W, A v ∈ W) (z : ℂ) {v : V} (hv : v ∈ W) :
    exponential A z v ∈ W := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let T := z • LinearMap.toContinuousLinearMap A
  have hpow (n : ℕ) : (T ^ n) v ∈ W := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp, T,
        smul_apply, LinearMap.coe_toContinuousLinearMap'] using
        W.smul_mem z (hW _ ih)
  have hs := (ContinuousLinearMap.apply ℂ V v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T)
  change ((ContinuousLinearMap.apply ℂ V v) (NormedSpace.exp T)) ∈ W
  rw [← hs.tsum_eq]
  exact tsum_mem W.closed_of_finiteDimensional fun n =>
    W.smul_mem _ (hpow n)

/-- The fixed lines of an ideal are preserved by every ambient exponential.
The weight-space stability theorem supplies the infinitesimal invariance. -/
theorem fixed_ideal_flow (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (I : LieIdeal ℂ L)
    (p : Projectivization ℂ V) (hp : IsFixed (ρ.comp I.incl) p) (x : L) (z : ℂ) :
    IsFixed (ρ.comp I.incl) (projectiveFlow (ρ x) z p) := by
  classical
  letI := LieRingModule.compLieHom V ρ
  letI := LieModule.compLieHom V ρ
  obtain ⟨χ, hχ⟩ := Classical.axiomOfChoice ((isFixed_iff _ _).mp hp)
  let W : LieSubmodule ℂ L V := LieModule.weightSpaceOfIsLieTower ℂ V χ
  have hv : p.rep ∈ W := by
    change p.rep ∈ LieModule.weightSpace V χ
    rw [LieModule.mem_weightSpace]
    exact hχ
  have he : exponential (ρ x) z p.rep ∈ W :=
    exponential_mem_submodule (ρ x) W.toSubmodule (fun v hv => W.lie_mem hv) z hv
  rw [← p.mk_rep, projectiveFlow_mk]
  intro a
  apply (isEigenline_mk_iff _ _ _).mpr
  refine ⟨χ a, ?_⟩
  exact (LieModule.mem_weightSpace χ _).mp he a

/-- Induction on the solvable algebra, with the one-operator compact result
as its only analytic input. -/
theorem fixed_point_of_single_operator
    (hsingle : ∀ (A : Module.End ℂ V) (Y : Set (Projectivization ℂ V)),
      Y.Nonempty → IsCompact Y →
      (∀ z p, p ∈ Y → projectiveFlow A z p ∈ Y) → ∃ p ∈ Y, IsEigenline A p)
    (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsSolvable L]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (X : Set (Projectivization ℂ V))
    (hne : X.Nonempty) (hX : IsCompact X) (hInv : IsInvariant ρ X) :
    ∃ p ∈ X, IsFixed ρ p := by
  classical
  obtain H | ⟨I, hI, hIL⟩ :=
    eq_top_or_exists_le_coatom (LieAlgebra.derivedSeries ℂ L 1).toSubmodule
  · obtain h | h := subsingleton_or_nontrivial L
    · exact fixed_point_of_subsingleton ρ X hne
    · rw [LieSubmodule.toSubmodule_eq_top] at H
      exact ((LieAlgebra.derivedSeries_lt_top_of_solvable ℂ L).ne H).elim
  lift I to LieIdeal ℂ L
  · intros
    exact hIL <| LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  obtain ⟨p, hpX, hpI⟩ := fixed_point_of_single_operator hsingle I (ρ.comp I.incl)
    X hne hX (fun a z q hq => hInv a z q hq)
  let Y := X ∩ {q | IsFixed (ρ.comp I.incl) q}
  have hYne : Y.Nonempty := ⟨p, hpX, hpI⟩
  have hY : IsCompact Y := hX.inter_right (isClosed_fixedPoints (ρ.comp I.incl))
  have hYInv : IsInvariant ρ Y := by
    intro x z q hq
    exact ⟨hInv x z q hq.1, fixed_ideal_flow ρ I q hq.2 x z⟩
  obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt hI.lt_top
  obtain ⟨q, hq, hqa⟩ := hsingle (ρ a) Y hYne hY (fun z q hq => hYInv a z q hq)
  refine ⟨q, hq.1, ?_⟩
  have hcompl := Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hI ha
  intro x v hv
  have hx : x ∈ I.toSubmodule ⊔ ℂ ∙ a := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨y, hy, b, hb, hsum⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [← hsum, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  exact q.submodule.add_mem (hq.2 ⟨y, hy⟩ v hv) (q.submodule.smul_mem c (hqa v hv))
termination_by Module.finrank ℂ L
decreasing_by
  rw [← finrank_top ℂ L]
  exact Submodule.finrank_lt_finrank_of_lt hI.lt_top

/-- The represented operators form a finite-dimensional solvable Lie algebra.
Its inclusion acts by the same operators on the same projective space. -/
theorem fixed_point_of_spectral_limit
    (hlimit : Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed.spectral_jordan_limit_type.{v})
    [LieAlgebra.IsSolvable L]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (X : Set (Projectivization ℂ V))
    (hne : X.Nonempty) (hX : IsCompact X) (hInv : IsInvariant ρ X) :
    ∃ p ∈ X, IsFixed ρ p := by
  have hInvRange : IsInvariant ρ.range.incl X := by
    intro A z p hp
    obtain ⟨x, rfl⟩ := ρ.surjective_rangeRestrict A
    exact hInv x z p hp
  obtain ⟨p, hpX, hp⟩ :=
    fixed_point_of_single_operator (eigenline_in_compact_of_spectral_limit hlimit)
      ρ.range ρ.range.incl X hne hX hInvRange
  exact ⟨p, hpX, fun x => hp (ρ.rangeRestrict x)⟩

/-- Once a power kills a vector, every larger power kills it. -/
theorem pow_apply_zero_of_le (B : Module.End ℂ V) {v : V} {n : ℕ}
    (hn : (B ^ n) v = 0) {j : ℕ} (hj : n ≤ j) : (B ^ j) v = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [add_comm n k, pow_add, Module.End.mul_apply, hn, map_zero]

/-- A nonzero generalized eigenvector has a last nonzero nilpotent power. -/
theorem exists_last_nonzero_power (B : Module.End ℂ V) (v : V) (hv : v ≠ 0)
    (n : ℕ) (hn : (B ^ n) v = 0) :
    ∃ m, (B ^ m) v ≠ 0 ∧ (B ^ (m + 1)) v = 0 := by
  induction n with
  | zero => exact (hv (by simpa using hn)).elim
  | succ n ih =>
    by_cases h : (B ^ n) v = 0
    · exact ih h
    · exact ⟨n, h, hn⟩

/-- The operator exponential applied to a vector killed by a power is a
finite polynomial, even when the operator is not globally nilpotent. -/
theorem exponential_eq_sum_of_pow_eq_zero (B : Module.End ℂ V) (v : V)
    (n : ℕ) (hn : (B ^ n) v = 0) (z : ℂ) :
    exponential B z v = ∑ j ∈ Finset.range n, (z ^ j / (j.factorial : ℂ)) • (B ^ j) v := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hc (j : ℕ) : (LinearMap.toContinuousLinearMap B ^ j) v = (B ^ j) v := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [pow_succ', Module.End.mul_apply, mul_apply_eq_comp,
        LinearMap.coe_toContinuousLinearMap', ih]
  have hs := (ContinuousLinearMap.apply ℂ V v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • LinearMap.toContinuousLinearMap B))
  have hs' : HasSum (fun j : ℕ => (z ^ j / (j.factorial : ℂ)) • (B ^ j) v)
      (exponential B z v) := by
    simpa only [ContinuousLinearMap.apply_apply, smul_pow, smul_apply,
      hc, smul_smul, div_eq_mul_inv, mul_comm, exponential] using hs
  exact hs'.unique (hasSum_sum_of_ne_finset_zero (s := Finset.range n) (by
    intro j hj
    rw [pow_apply_zero_of_le B hn (Nat.le_of_not_gt (by simpa using hj)), smul_zero]))

/-- Splitting off a scalar operator splits off its scalar exponential. -/
theorem exponential_shift (A : Module.End ℂ V) (μ z : ℂ) (v : V) :
    exponential A z v = Complex.exp (z * μ) • exponential (A - μ • 1) z v := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  let T := LinearMap.toContinuousLinearMap (A - μ • 1)
  have hsplit : z • LinearMap.toContinuousLinearMap A =
      (algebraMap ℂ (V →L[ℂ] V)) (z * μ) + z • T := by
    ext w
    simp [T, ContinuousLinearMap.algebraMap_apply, smul_sub, smul_smul, mul_comm]
  have hcomm : Commute ((algebraMap ℂ (V →L[ℂ] V)) (z * μ)) (z • T) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (Commute.one_left _).smul_left _
  unfold exponential
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm,
    ← NormedSpace.algebraMap_exp_comm, mul_apply_eq_comp,
    ContinuousLinearMap.algebraMap_apply, ← Complex.exp_eq_exp_ℂ]

/-- Exponential decay dominates every polynomial, also for complex
exponents with negative real part. -/
theorem tendsto_complex_exp_mul_pow {δ : ℂ} (hδ : δ.re < 0) (j : ℕ) :
    Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * δ) * (t : ℂ) ^ j) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (j : ℝ) (-δ.re) (neg_pos.mpr hδ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [norm_mul, norm_pow, Complex.norm_exp, Complex.mul_re,
    Real.norm_eq_abs, abs_of_nonneg ht, Real.rpow_natCast, mul_comm]

/-- Dividing an exponentially decaying polynomial by another monomial
still tends to zero at positive infinity. -/
theorem tendsto_complex_exp_mul_pow_div_pow {δ : ℂ} (hδ : δ.re < 0) (j m : ℕ) :
    Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * δ) * (t : ℂ) ^ j / (t : ℂ) ^ m)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ m) atTop (𝓝 ((0 : ℂ) ^ m)) := by
    apply Tendsto.pow
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  simpa only [div_eq_mul_inv, inv_pow, zero_mul] using
    (tendsto_complex_exp_mul_pow hδ j).mul hi


/-- The explicit normalized Jordan expansion on one generalized eigenspace. -/
theorem normalized_exponential_eq_sum (A : Module.End ℂ V) (μ ν c : ℂ)
    (v : V) (n m : ℕ) (hn : ((A - μ • 1) ^ n) v = 0) (t : ℝ) :
    (Complex.exp (-(t : ℂ) * c * ν) / (t : ℂ) ^ m) •
      exponential A ((t : ℂ) * c) v =
    ∑ j ∈ Finset.range n,
      ((Complex.exp ((t : ℂ) * (c * (μ - ν))) * (t : ℂ) ^ j / (t : ℂ) ^ m) *
        (c ^ j / (j.factorial : ℂ))) • ((A - μ • 1) ^ j) v := by
  rw [exponential_shift A μ, exponential_eq_sum_of_pow_eq_zero _ v n hn]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have he : Complex.exp (-(t : ℂ) * c * ν) * Complex.exp ((t : ℂ) * c * μ) =
      Complex.exp ((t : ℂ) * (c * (μ - ν))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [div_eq_mul_inv, mul_pow]
  calc
    _ = (Complex.exp (-(t : ℂ) * c * ν) * Complex.exp ((t : ℂ) * c * μ)) *
        ((t : ℂ) ^ j * c ^ j * ((j.factorial : ℂ)⁻¹) * ((t : ℂ) ^ m)⁻¹) := by ring
    _ = _ := by rw [he]; ring

/-- A lower degree monomial vanishes after division by the leading degree. -/
theorem tendsto_complex_pow_div_pow {j m : ℕ} (hjm : j < m) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ j / (t : ℂ) ^ m) atTop (𝓝 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hjm
  have hi : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ (k + 1)) atTop (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))).pow (k + 1)
    simpa [Function.comp_def] using h
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [show j + k + 1 = j + (k + 1) by omega, pow_add, inv_pow]
  field_simp

/-- The normalized monomial of the leading degree is eventually one. -/
theorem tendsto_complex_pow_div_self (m : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ m / (t : ℂ) ^ m) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (div_self (pow_ne_zero m (Complex.ofReal_ne_zero.mpr ht.ne'))).symm

/-- Every lower-real-part generalized eigenspace disappears under the
normalization chosen for a dominating eigenvalue. -/
theorem normalized_exponential_tendsto_zero (A : Module.End ℂ V) (μ ν c : ℂ)
    (v : V) (n m : ℕ) (hn : ((A - μ • 1) ^ n) v = 0)
    (hμ : (c * μ).re < (c * ν).re) :
    Tendsto (fun t : ℝ =>
      (Complex.exp (-(t : ℂ) * c * ν) / (t : ℂ) ^ m) •
        exponential A ((t : ℂ) * c) v) atTop (𝓝 0) := by
  have hδ : (c * (μ - ν)).re < 0 := by
    simpa only [mul_sub, Complex.sub_re, sub_lt_zero] using hμ
  have h := tendsto_finsetSum (Finset.range n) (fun j hj =>
    ((tendsto_complex_exp_mul_pow_div_pow hδ j m).mul_const
      (c ^ j / (j.factorial : ℂ))).smul_const (((A - μ • 1) ^ j) v))
  simp only [zero_mul, zero_smul, Finset.sum_const_zero] at h
  exact h.congr' (Filter.Eventually.of_forall fun t =>
    (normalized_exponential_eq_sum A μ ν c v n m hn t).symm)

/-- On the dominating generalized eigenspace, precisely its highest nonzero
power survives, with the exact leading coefficient. -/
theorem normalized_exponential_tendsto_leading (A : Module.End ℂ V) (μ c : ℂ)
    (v : V) (m : ℕ) (hm : ((A - μ • 1) ^ (m + 1)) v = 0) :
    Tendsto (fun t : ℝ =>
      (Complex.exp (-(t : ℂ) * c * μ) / (t : ℂ) ^ m) •
        exponential A ((t : ℂ) * c) v) atTop
      (𝓝 ((c ^ m / (m.factorial : ℂ)) • ((A - μ • 1) ^ m) v)) := by
  classical
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      Tendsto (fun t : ℝ =>
        (((t : ℂ) ^ j / (t : ℂ) ^ m) * (c ^ j / (j.factorial : ℂ))) •
          ((A - μ • 1) ^ j) v) atTop
        (𝓝 (if j = m then (c ^ m / (m.factorial : ℂ)) • ((A - μ • 1) ^ m) v else 0)) := by
    by_cases he : j = m
    · subst j
      simpa using ((tendsto_complex_pow_div_self m).mul_const
        (c ^ m / (m.factorial : ℂ))).smul_const (((A - μ • 1) ^ m) v)
    · have hjm : j < m := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) he
      simpa [he] using ((tendsto_complex_pow_div_pow hjm).mul_const
        (c ^ j / (j.factorial : ℂ))).smul_const (((A - μ • 1) ^ j) v)
  have h := tendsto_finsetSum (Finset.range (m + 1)) hterm
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, ↓reduceIte] at h
  apply h.congr'
  filter_upwards with t
  rw [normalized_exponential_eq_sum A μ μ c v (m + 1) m hm t]
  simp

/-- The spectral/Jordan limit for every vector, with no multiplicity or
Jordan-block restriction. Decompose into the whole generalized eigenspaces,
then select the dominant component and its last nonzero nilpotent power. -/
theorem spectral_jordan_limit :
    Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed.spectral_jordan_limit_type.{v} := by
  intro V _ _ _ A v hv
  classical
  have hvtop : v ∈ ⨆ μ : ℂ, A.maxGenEigenspace μ := by
    rw [A.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hvtop
  have hfnz : f ≠ 0 := by
    intro h
    apply hv
    simpa [h] using hsum.symm
  obtain ⟨c, hc, hsep⟩ := exists_spectral_rotation f.support
  obtain ⟨μ, hμ, hmax⟩ := f.support.exists_max_image (fun a => (c * a).re)
    (Finsupp.support_nonempty_iff.mpr hfnz)
  obtain ⟨n, hn⟩ := (A.mem_maxGenEigenspace μ (f μ)).mp (hf μ)
  obtain ⟨m, hmne, hmzero⟩ := exists_last_nonzero_power (A - μ • 1) (f μ)
    (Finsupp.mem_support_iff.mp hμ) n hn
  let w := (c ^ m / (m.factorial : ℂ)) • ((A - μ • 1) ^ m) (f μ)
  have hcoef : c ^ m / (m.factorial : ℂ) ≠ 0 :=
    div_ne_zero (pow_ne_zero m hc) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
  have heigen : A (((A - μ • 1) ^ m) (f μ)) =
      μ • ((A - μ • 1) ^ m) (f μ) := by
    simpa only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] using hmzero
  refine ⟨c, μ, m, w, hc, smul_ne_zero hcoef hmne, ?_, ?_⟩
  · simp only [w, map_smul, heigen, smul_smul, mul_comm]
  · have hterm (a : ℂ) (ha : a ∈ f.support) :
        Tendsto (fun t : ℝ =>
          (Complex.exp (-(t : ℂ) * c * μ) / (t : ℂ) ^ m) •
            exponential A ((t : ℂ) * c) (f a)) atTop (𝓝 (if a = μ then w else 0)) := by
      by_cases he : a = μ
      · subst a
        simpa only [↓reduceIte] using
          normalized_exponential_tendsto_leading A μ c (f μ) m hmzero
      · have halt : (c * a).re < (c * μ).re :=
          lt_of_le_of_ne (hmax a ha) (hsep a ha μ hμ he)
        obtain ⟨k, hk⟩ := (A.mem_maxGenEigenspace a (f a)).mp (hf a)
        simpa only [he, ↓reduceIte] using
          normalized_exponential_tendsto_zero A a μ c (f a) k m hk halt
    have hlim := tendsto_finsetSum f.support hterm
    simp only [Finset.sum_ite_eq', hμ, ↓reduceIte] at hlim
    apply hlim.congr'
    filter_upwards with t
    rw [← hsum]
    simp only [Finsupp.sum, map_sum, Finset.smul_sum]

/-- Every nonempty compact invariant projective set contains a line fixed
by the solvable Lie algebra. -/
theorem solvable_projective_fixed :
    Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed.solvable_projective_fixed_type.{u,v} := by
  intro L _ _ _ V _ _ _ ρ X hne hX hInv
  exact fixed_point_of_spectral_limit spectral_jordan_limit ρ X hne hX hInv

end LieAlgebrasAndRepresentations.SolvableProjectiveFixed
