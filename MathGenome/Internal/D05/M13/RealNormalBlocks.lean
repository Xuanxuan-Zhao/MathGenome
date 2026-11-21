import MathGenome.Internal.Specs.D05.M13.RealNormalBlocks
import MathGenome.Internal.D05.M13.NormalReducing
import MathGenome.Internal.D05.M13.Unitary
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! K05.13.real_normal_blocks. The construction stays over ℝ: choose a
joint eigenvector of (T+T†)/2 and T†T, normalize its transverse residual,
and iterate on its reducing orthogonal complement. -/

noncomputable section
open scoped BigOperators
namespace D05.M13.RealNormalBlocks
open Specs.D05.M13.RealNormalBlocks

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A unit eigenvector of a real symmetric map on a nonzero space. -/
theorem exists_unit_eigenvector [Nontrivial V] (S : V →ₗ[ℝ] V)
    (hS : S.IsSymmetric) : ∃ a : ℝ, ∃ e : V, ‖e‖ = 1 ∧ S e = a • e := by
  let i : Fin (Module.finrank ℝ V) := ⟨0, Module.finrank_pos⟩
  exact ⟨hS.eigenvalues rfl i, hS.eigenvectorBasis rfl i,
    (hS.eigenvectorBasis rfl).orthonormal.1 i, hS.apply_eigenvectorBasis rfl i⟩

/-- A normal map has a unit vector which is simultaneously an eigenvector of
its symmetric part and of T†T. This uses only the real symmetric theorem. -/
theorem joint_unit_vector [Nontrivial V] (T : V →ₗ[ℝ] V)
    (hT : D05.normalOperator T) :
    ∃ a q : ℝ, ∃ e : V, ‖e‖ = 1 ∧
      (T + T.adjoint) e = (2 * a) • e ∧ T.adjoint (T e) = q • e := by
  let S := (2 : ℝ)⁻¹ • (T + T.adjoint)
  have hS : S.IsSymmetric := by
    intro x y
    simp only [S, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left,
      inner_smul_right, inner_add_left, inner_add_right, conj_trivial,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
    ring
  obtain ⟨a, x, hx, hax⟩ := exists_unit_eigenvector S hS
  let M := Module.End.eigenspace S a
  have hxM : x ∈ M := Module.End.mem_eigenspace_iff.mpr hax
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have : Nontrivial M := ⟨⟨⟨x, hxM⟩, 0, by simpa using hx0⟩⟩
  have hcomm (v : V) : S (T v) = T (S v) := by
    have hv := DFunLike.congr_fun hT v
    change T (T.adjoint v) = T.adjoint (T v) at hv
    simp only [S, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add]
    rw [hv]
  have hM : ∀ v ∈ M, T v ∈ M := by
    intro v hv
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hcomm, Module.End.mem_eigenspace_iff.mp hv, map_smul]
  have hMa := (D05.M13.NormalReducing.invariant_subspace_reduces T M hT hM).1
  let Q := T.adjoint.comp T
  have hQM : ∀ v ∈ M, Q v ∈ M := fun v hv => hMa _ (hM v hv)
  have hQ : Q.IsSymmetric := by
    intro v w
    change ⟪T.adjoint (T v), w⟫ = ⟪v, T.adjoint (T w)⟫
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  obtain ⟨q, e, he, hqe⟩ := exists_unit_eigenvector (Q.restrict hQM)
    (hQ.restrict_invariant hQM)
  refine ⟨a, q, e, he, ?_, ?_⟩
  · have ha := Module.End.mem_eigenspace_iff.mp e.property
    change (2 : ℝ)⁻¹ • ((T + T.adjoint) (e : V)) = a • (e : V) at ha
    have := congrArg (fun z : V => (2 : ℝ) • z) ha
    simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] using this
  · exact congrArg Subtype.val hqe

/-- Remove the component along a joint unit vector. Its residual is either zero
or supplies the second unit vector of a positively oriented normal plane. -/
theorem normal_small_block : Specs.D05.M13.RealNormalBlocks.normal_small_block := by
  intro V _ _ _ _ T hT
  obtain ⟨a, q, e, he, hsum, hqe⟩ := joint_unit_vector T hT
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have het : ⟪e, T e⟫ = a := by
    have h := congrArg (fun v => ⟪e, v⟫) hsum
    simp only [LinearMap.add_apply, inner_add_right, inner_smul_right,
      LinearMap.adjoint_inner_right, hee, mul_one] at h
    rw [real_inner_comm e (T e)] at h
    linarith
  have htt : ⟪T e, T e⟫ = q := by
    rw [← LinearMap.adjoint_inner_right, hqe, inner_smul_right, hee, mul_one]
  have hquad : T (T e) = (2 * a) • T e - q • e := by
    have h := congrArg T hsum
    simp only [LinearMap.add_apply, map_add, map_smul] at h
    have ht := DFunLike.congr_fun hT e
    change T (T.adjoint e) = T.adjoint (T e) at ht
    rw [ht, hqe] at h
    exact eq_sub_of_add_eq h
  let w := T e - a • e
  have hew : ⟪e, w⟫ = 0 := by simp [w, inner_sub_right, real_inner_smul_right, het, he]
  have hnw : ‖w‖ ^ 2 = q - a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, htt, het, real_inner_comm e (T e), hee]
    ring
  have htw : T w = a • w - ‖w‖ ^ 2 • e := by
    dsimp [w]
    rw [map_sub, map_smul, hquad, hnw]
    module
  by_cases hw : w = 0
  · exact Or.inl ⟨a, e, he, sub_eq_zero.mp hw⟩
  · have hb : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let f := ‖w‖⁻¹ • w
    have hf : ‖f‖ = 1 := by
      simp [f, norm_smul, inv_mul_cancel₀ hb.ne']
    have hfw : ‖w‖ • f = w := by
      simp [f, smul_smul, mul_inv_cancel₀ hb.ne']
    refine Or.inr ⟨a, ‖w‖, e, f, hb, he, hf, ?_, ?_, ?_⟩
    · simp [f, inner_smul_right, hew]
    · rw [hfw]
      dsimp [w]
      module
    · dsimp [f]
      rw [map_smul, htw]
      simp only [smul_sub, smul_smul]
      have hc : ‖w‖⁻¹ * ‖w‖ ^ 2 = ‖w‖ := by field_simp
      rw [hc]
      module

/-- Transport a block through an intertwining linear map and an injective
change of indices. -/
theorem blockAt_transport {U W ι κ : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup W] [Module ℝ W] (S : U →ₗ[ℝ] U) (T : W →ₗ[ℝ] W)
    (v : ι → U) (w : κ → W) (f : U →ₗ[ℝ] W) (g : ι → κ)
    (hg : Function.Injective g) (hv : ∀ i, w (g i) = f (v i))
    (hTS : ∀ x, T (f x) = f (S x)) {i : ι} (hi : BlockAt S v i) :
    BlockAt T w (g i) := by
  rcases hi with ⟨a, ha⟩ | ⟨j, hji, a, b, hb, hp⟩
  · left
    exact ⟨a, by rw [hv, hTS, ha, map_smul]⟩
  · right
    refine ⟨g j, fun h => hji (hg h), a, b, hb, ?_⟩
    rcases hp with hp | hp
    · left
      constructor
      · rw [hv, hTS, hp.1, map_add, map_smul, map_smul, hv]
      · rw [hv, hTS, hp.2, map_add, map_smul, map_smul, hv]
    · right
      constructor
      · rw [hv, hTS, hp.1, map_add, map_smul, map_smul, hv]
      · rw [hv, hTS, hp.2, map_add, map_smul, map_smul, hv]

omit [FiniteDimensional ℝ V] in
/-- The span of a family of complete blocks is invariant. -/
theorem invariant_span_blocks {ι : Type*} (T : V →ₗ[ℝ] V) (v : ι → V)
    (hv : ∀ i, BlockAt T v i) :
    ∀ x ∈ Submodule.span ℝ (Set.range v), T x ∈ Submodule.span ℝ (Set.range v) := by
  let M := Submodule.span ℝ (Set.range v)
  have hmem (i : ι) : v i ∈ M := Submodule.subset_span ⟨i, rfl⟩
  have hle : M ≤ M.comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change T (v i) ∈ M
    rcases hv i with ⟨a, ha⟩ | ⟨j, _, a, b, _, hp⟩
    · rw [ha]; exact M.smul_mem a (hmem i)
    · rcases hp with hp | hp
      · rw [hp.1]; exact M.add_mem (M.smul_mem a (hmem i)) (M.smul_mem b (hmem j))
      · rw [hp.2]; exact M.add_mem (M.smul_mem (-b) (hmem j)) (M.smul_mem a (hmem i))
  exact fun x hx => hle hx

/-- Concatenate an orthonormal block family with a block basis of its
orthogonal complement. -/
theorem append_blocks {m n : ℕ} (T : V →ₗ[ℝ] V) (v : Fin m → V)
    (hv : Orthonormal ℝ v) (hb : ∀ i, BlockAt T v i)
    (hP : ∀ x ∈ (Submodule.span ℝ (Set.range v)).orthogonal,
      T x ∈ (Submodule.span ℝ (Set.range v)).orthogonal)
    (B : OrthonormalBasis (Fin n) ℝ (Submodule.span ℝ (Set.range v)).orthogonal)
    (hB : ∀ i, BlockAt (T.restrict hP) B i) :
    ∃ k : ℕ, ∃ C : OrthonormalBasis (Fin k) ℝ V, ∀ i, BlockAt T C i := by
  classical
  let M := Submodule.span ℝ (Set.range v)
  let u : Fin m ⊕ Fin n → V := Sum.elim v (fun j => (B j : V))
  have hmem (i : Fin m) : v i ∈ M := Submodule.subset_span ⟨i, rfl⟩
  have hu : Orthonormal ℝ u := by
    apply orthonormal_iff_ite.mpr
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [u] using (orthonormal_iff_ite.mp hv i j)
      | inr j =>
        simpa [u] using M.inner_right_of_mem_orthogonal (hmem i) (B j).property
    | inr i =>
      cases j with
      | inl j =>
        simpa [u] using M.inner_left_of_mem_orthogonal (hmem j) (B i).property
      | inr j => simpa [u] using (orthonormal_iff_ite.mp B.orthonormal i j)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range u) := by
    rw [← M.sup_orthogonal_of_hasOrthogonalProjection]
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · intro x hx
      let x' : M.orthogonal := ⟨x, hx⟩
      have heq : x = ∑ j, B.repr x' j • u (Sum.inr j) := by
        simpa only [u, Sum.elim_inr, map_sum, map_smul, Submodule.subtype_apply]
          using (congrArg M.orthogonal.subtype (B.sum_repr x')).symm
      rw [heq]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  let C := OrthonormalBasis.mk hu hsp
  have hC : ∀ i, BlockAt T C i := by
    intro i
    change BlockAt T (OrthonormalBasis.mk hu hsp) i
    simp only [OrthonormalBasis.coe_mk]
    cases i with
    | inl i =>
      exact blockAt_transport T T v u (LinearMap.id) Sum.inl Sum.inl_injective
        (fun _ => rfl) (fun _ => rfl) (hb i)
    | inr i =>
      exact blockAt_transport (T.restrict hP) T B u M.orthogonal.subtype Sum.inr
        Sum.inr_injective (fun _ => rfl) (fun _ => rfl) (hB i)
  let e : (Fin m ⊕ Fin n) ≃ Fin (m + n) := finSumFinEquiv
  refine ⟨m + n, C.reindex e, fun i => ?_⟩
  have hi := blockAt_transport T T C (C.reindex e) (LinearMap.id) e e.injective
    (fun j => by simp) (fun _ => rfl) (hC (e.symm i))
  simpa only [e.apply_symm_apply] using hi

/-- Package the first line or plane as a nonempty finite orthonormal family. -/
theorem exists_small_family [Nontrivial V] (T : V →ₗ[ℝ] V)
    (hT : D05.normalOperator T) :
    ∃ m : ℕ, ∃ v : Fin m → V, 0 < m ∧ Orthonormal ℝ v ∧ ∀ i, BlockAt T v i := by
  rcases normal_small_block T hT with ⟨a, e, he, hae⟩ |
    ⟨a, b, e, f, hb, he, hf, hef, hact⟩
  · refine ⟨1, ![e], by omega, ?_, ?_⟩
    · apply orthonormal_iff_ite.mpr
      intro i j
      fin_cases i; fin_cases j
      simp [he]
    · intro i
      fin_cases i
      exact Or.inl ⟨a, hae⟩
  · refine ⟨2, ![e, f], by omega, ?_, ?_⟩
    · apply orthonormal_iff_ite.mpr
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [he, hf, hef, real_inner_comm e f]
    · intro i
      fin_cases i
      · exact Or.inr ⟨1, by decide, a, b, hb, Or.inl hact⟩
      · exact Or.inr ⟨0, by decide, a, b, hb, Or.inr hact⟩

universe u
/-- Dimension induction with the ambient space generalized, so it applies to
an orthogonal-complement subtype at the next step. -/
private theorem normal_blocks_aux (n : ℕ) :
    ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V], Module.finrank ℝ V = n →
      ∀ T : V →ₗ[ℝ] V, D05.normalOperator T →
        ∃ k : ℕ, ∃ B : OrthonormalBasis (Fin k) ℝ V, ∀ i, BlockAt T B i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ hdim T hT
    by_cases hn : n = 0
    · have : Subsingleton V := Module.finrank_zero_iff.mp (hdim.trans hn)
      let v : Fin 0 → V := Fin.elim0
      have hv : Orthonormal ℝ v := Orthonormal.of_isEmpty v
      have hs : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
        intro x _
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx]
        exact Submodule.zero_mem _
      exact ⟨0, OrthonormalBasis.mk hv hs, fun i => Fin.elim0 i⟩
    · have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ V)
      obtain ⟨m, v, hm, hv, hb⟩ := exists_small_family T hT
      let M := Submodule.span ℝ (Set.range v)
      have hmem (i : Fin m) : v i ∈ M := Submodule.subset_span ⟨i, rfl⟩
      let i : Fin m := ⟨0, hm⟩
      have hvi : v i ≠ 0 := by
        intro h
        have := hv.norm_eq_one i
        simp [h] at this
      have hMpos : 0 < Module.finrank ℝ M :=
        Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨v i, hmem i⟩, fun h => hvi (congrArg Subtype.val h)⟩
      have hdimP : Module.finrank ℝ M.orthogonal < n := by
        have := M.finrank_add_finrank_orthogonal
        omega
      have hM := invariant_span_blocks T v hb
      obtain ⟨hMa, hP, hPa, hr⟩ :=
        D05.M13.NormalReducing.invariant_and_normal_restrictions T M hT hM
      have hTP : D05.normalOperator (T.restrict hP) := hr.2.1
      obtain ⟨k, B, hB⟩ := ih (Module.finrank ℝ M.orthogonal) hdimP rfl (T.restrict hP) hTP
      exact append_blocks T v hv hb hP B hB

/-- The real normal block theorem, with no positive-dimension hypothesis. -/
theorem normal_blocks : Specs.D05.M13.RealNormalBlocks.normal_blocks := by
  intro V _ _ _ T hT
  exact normal_blocks_aux (Module.finrank ℝ V) rfl T hT

/-- Norm preservation on a unit real eigenvector forces its eigenvalue to
be either 1 or -1. -/
theorem orthogonal_line_parameter {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (T : W →ₗ[ℝ] W) (hT : D05.IsInnerIsometry T)
    (e : W) (he : ‖e‖ = 1) (a : ℝ) (ha : T e = a • e) : a = 1 ∨ a = -1 := by
  have h := hT e e
  change inner ℝ (T e) (T e) = inner ℝ e e at h
  rw [ha] at h
  have hee : inner ℝ e e = 1 := by simp [he]
  rw [real_inner_smul_left, real_inner_smul_right, hee] at h
  have : a ^ 2 = 1 := by nlinarith
  exact sq_eq_one_iff.mp this

/-- A plane block preserves norm exactly at radius one in the (a,b) plane;
this is the necessary direction used for the orthogonal specialization. -/
theorem orthogonal_plane_parameter {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (T : W →ₗ[ℝ] W) (hT : D05.IsInnerIsometry T)
    (e f : W) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    (a b : ℝ) (ha : PlaneAction T e f a b) : a ^ 2 + b ^ 2 = 1 := by
  have h := hT e e
  change inner ℝ (T e) (T e) = inner ℝ e e at h
  rw [ha.1] at h
  have hee : inner ℝ e e = 1 := by simp [he]
  have hff : inner ℝ f f = 1 := by simp [hf]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hee, hff, hef, real_inner_comm e f,
    mul_one, mul_zero, add_zero, zero_add] at h
  nlinarith

/-- The orthogonal-map parameter constraints hold on every block family,
without any spanning or finite-dimensional assumption. -/
theorem orthogonal_parameters : Specs.D05.M13.RealNormalBlocks.orthogonal_parameters := by
  intro V ι _ _ T v hT hv i hi
  rcases hi with ⟨a, ha⟩ | ⟨j, hji, a, b, hb, hp⟩
  · left
    rcases orthogonal_line_parameter T hT (v i) (hv.norm_eq_one i) a ha with h | h
    · left; simpa [h] using ha
    · right; simpa [h] using ha
  · right
    refine ⟨j, hji, a, b, hb, ?_, hp⟩
    rcases hp with hp | hp
    · exact orthogonal_plane_parameter T hT (v i) (v j)
        (hv.norm_eq_one i) (hv.norm_eq_one j) (hv.inner_eq_zero hji.symm) a b hp
    · exact orthogonal_plane_parameter T hT (v j) (v i)
        (hv.norm_eq_one j) (hv.norm_eq_one i) (hv.inner_eq_zero hji) a b hp

/-- Orthogonal maps are normal by their two adjoint inverse identities, so
apply the real normal theorem and then impose the norm constraints. -/
theorem orthogonal_blocks : Specs.D05.M13.RealNormalBlocks.orthogonal_blocks := by
  intro V _ _ _ T hT
  obtain ⟨hAT, hTA⟩ := D05.M13.Unitary.unitary_iff_adjoint_identities T |>.mp hT
  have hn : D05.normalOperator T := hTA.trans hAT.symm
  obtain ⟨n, B, hB⟩ := normal_blocks T hn
  exact ⟨n, B, fun i => orthogonal_parameters T B hT.1 B.orthonormal i (hB i)⟩

/-- Extract the nonzero off-diagonal coefficient in either orientation. -/
theorem pair_offDiagonal {W ι : Type*} [AddCommGroup W] [Module ℝ W]
    {T : W →ₗ[ℝ] W} {v : ι → W} {i j : ι}
    (hp : ∃ a b : ℝ, 0 < b ∧
      (PlaneAction T (v i) (v j) a b ∨ PlaneAction T (v j) (v i) a b)) :
    ∃ a b : ℝ, b ≠ 0 ∧ T (v i) = a • v i + b • v j := by
  obtain ⟨a, b, hb, hp⟩ := hp
  rcases hp with hp | hp
  · exact ⟨a, b, hb.ne', hp.1⟩
  · exact ⟨a, -b, neg_ne_zero.mpr hb.ne', hp.2.trans (add_comm _ _)⟩

/-- A nonzero off-diagonal coordinate excludes an eigenline. -/
theorem offDiagonal_not_eigenline {W ι : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {T : W →ₗ[ℝ] W} {v : ι → W}
    (hv : Orthonormal ℝ v) {i j : ι} (hji : j ≠ i) {a b : ℝ}
    (hb : b ≠ 0) (h : T (v i) = a • v i + b • v j) :
    ¬ ∃ c : ℝ, T (v i) = c • v i := by
  rintro ⟨c, hc⟩
  have hi := congrArg (fun x => inner ℝ (v j) x) (h.symm.trans hc)
  have hji' := hv.inner_eq_zero hji
  have hjj : inner ℝ (v j) (v j) = 1 := by simp [hv.norm_eq_one j]
  simp only [inner_add_right, real_inner_smul_right, hji', hjj,
    mul_zero, mul_one, zero_add] at hi
  exact hb hi

/-- The nonzero off-diagonal coordinate uniquely determines the other index. -/
theorem offDiagonal_partner_unique {W ι : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {T : W →ₗ[ℝ] W} {v : ι → W}
    (hv : Orthonormal ℝ v) {i j k : ι} (hji : j ≠ i) {a b c d : ℝ}
    (hb : b ≠ 0) (h : T (v i) = a • v i + b • v j)
    (h' : T (v i) = c • v i + d • v k) : j = k := by
  by_contra hjk
  have hi := congrArg (fun x => inner ℝ (v j) x) (h.symm.trans h')
  have hji' := hv.inner_eq_zero hji
  have hjk' := hv.inner_eq_zero hjk
  have hjj : inner ℝ (v j) (v j) = 1 := by simp [hv.norm_eq_one j]
  simp only [inner_add_right, real_inner_smul_right, hji', hjk', hjj,
    mul_zero, mul_one, zero_add, add_zero] at hi
  exact hb hi

/-- The per-vector formulas yield a genuine disjoint block partition: a
plane's two off-diagonal coefficients force the partner choices to be mutual. -/
theorem block_partition : Specs.D05.M13.RealNormalBlocks.block_partition := by
  classical
  intro V ι _ _ T v hv hB
  have hchoice : ∀ i, ∃ j, (j = i ∧ ∃ a : ℝ, T (v i) = a • v i) ∨
      (j ≠ i ∧ ∃ a b : ℝ, 0 < b ∧
        (PlaneAction T (v i) (v j) a b ∨ PlaneAction T (v j) (v i) a b)) := by
    intro i
    rcases hB i with hi | ⟨j, hji, hp⟩
    · exact ⟨i, Or.inl ⟨rfl, hi⟩⟩
    · exact ⟨j, Or.inr ⟨hji, hp⟩⟩
  choose p hp using hchoice
  refine ⟨p, ?_, hp⟩
  intro i
  rcases hp i with ⟨hpi, _⟩ | ⟨hpi, hpair⟩
  · rw [hpi, hpi]
  · have hpair' : ∃ a b : ℝ, 0 < b ∧
        (PlaneAction T (v (p i)) (v i) a b ∨ PlaneAction T (v i) (v (p i)) a b) := by
      obtain ⟨a, b, hb, hh⟩ := hpair
      exact ⟨a, b, hb, hh.symm⟩
    obtain ⟨a, b, hb, hab⟩ := pair_offDiagonal hpair'
    rcases hp (p i) with ⟨_, heig⟩ | ⟨_, hpair2⟩
    · exact False.elim (offDiagonal_not_eigenline hv hpi.symm hb hab heig)
    · obtain ⟨c, d, _, hcd⟩ := pair_offDiagonal hpair2
      exact (offDiagonal_partner_unique hv hpi.symm hb hab hcd).symm

/-- Normal blocks with an explicit disjoint partition of all basis indices. -/
theorem normal_blocks_partitioned : Specs.D05.M13.RealNormalBlocks.normal_blocks_partitioned := by
  intro V _ _ _ T hT
  obtain ⟨n, B, hB⟩ := normal_blocks T hT
  obtain ⟨p, hp, hpart⟩ := block_partition T B B.orthonormal hB
  exact ⟨n, B, p, hp, hpart⟩

/-- Impose the orthogonal scalar constraints on the same selected partition. -/
theorem orthogonal_blocks_partitioned : Specs.D05.M13.RealNormalBlocks.orthogonal_blocks_partitioned := by
  intro V _ _ _ T hT
  obtain ⟨hAT, hTA⟩ := D05.M13.Unitary.unitary_iff_adjoint_identities T |>.mp hT
  have hn : D05.normalOperator T := hTA.trans hAT.symm
  obtain ⟨n, B, p, hp, hpart⟩ := normal_blocks_partitioned T hn
  refine ⟨n, B, p, hp, fun i => ?_⟩
  rcases hpart i with ⟨hpi, a, ha⟩ | ⟨hpi, a, b, hb, hact⟩
  · left
    refine ⟨hpi, ?_⟩
    rcases orthogonal_line_parameter T hT.1 (B i) (B.orthonormal.norm_eq_one i) a ha with h | h
    · left; simpa [h] using ha
    · right; simpa [h] using ha
  · right
    refine ⟨hpi, a, b, hb, ?_, hact⟩
    rcases hact with hact | hact
    · exact orthogonal_plane_parameter T hT.1 (B i) (B (p i))
        (B.orthonormal.norm_eq_one i) (B.orthonormal.norm_eq_one (p i))
        (B.orthonormal.inner_eq_zero hpi.symm) a b hact
    · exact orthogonal_plane_parameter T hT.1 (B (p i)) (B i)
        (B.orthonormal.norm_eq_one (p i)) (B.orthonormal.norm_eq_one i)
        (B.orthonormal.inner_eq_zero hpi) a b hact

/-- Both transpose products of a real plane block. -/
theorem plane_gram_products : Specs.D05.M13.RealNormalBlocks.plane_gram_products := by
  intro a b
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, pow_two] <;> ring

/-- The full necessary-and-sufficient orthogonality criterion for a plane block. -/
theorem plane_orthogonal_iff : Specs.D05.M13.RealNormalBlocks.plane_orthogonal_iff := by
  intro a b
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![a, -b; b, a]
  have hstar : M.conjTranspose = M.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  constructor
  · intro h
    have hp := ((D05.M13.Unitary.unitary_iff_adjoint_identities (Matrix.toEuclideanLin M)).mp h).1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← Matrix.toLpLin_mul] at hp
    have hm : M.conjTranspose * M = 1 :=
      Matrix.toEuclideanLin.injective (hp.trans (Matrix.toLpLin_one 2).symm)
    rw [hstar, (plane_gram_products a b).1] at hm
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) hm
    simpa using h00
  · intro h
    apply (D05.M13.Unitary.unitary_iff_adjoint_identities (Matrix.toEuclideanLin M)).mpr
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← Matrix.toLpLin_mul,
      ← Matrix.toLpLin_mul, hstar]
    change (Matrix.toEuclideanLin (M.transpose * M) = LinearMap.id) ∧
      (Matrix.toEuclideanLin (M * M.transpose) = LinearMap.id)
    rw [(plane_gram_products a b).1, (plane_gram_products a b).2, h, one_smul]
    exact ⟨Matrix.toLpLin_one 2, Matrix.toLpLin_one 2⟩

end D05.M13.RealNormalBlocks
