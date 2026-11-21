import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.GalerkinCea
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramEnergy
import Mathlib.Tactic.Abel

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace ExpandedFA.PartV.GalerkinCea
open ExpandedFA.Hilbert.Conventions.Spec
open Spec
universe u v

theorem galerkin_solvability : Spec.GalerkinSolvability.{u, v} := by
  intro 𝕜 H _ _ _ _ a α hc F W hW
  let : CompleteSpace W := hW.completeSpace_coe
  have hcW : FormCoerciveValue 𝕜 W (a.bilinearComp W.subtypeL W.subtypeL) α :=
    ⟨hc.1, fun z => hc.2 z⟩
  obtain ⟨w, hw, hnorm, huniq, _⟩ :=
    ExpandedFA.Hilbert.LaxMilgramEnergy.lax_milgram 𝕜 W
      (a.bilinearComp W.subtypeL W.subtypeL) α hcW (F.domRestrict W)
  have hF : ‖F.domRestrict W‖ ≤ ‖F‖ := by
    apply (F.domRestrict W).opNorm_le_bound (norm_nonneg F)
    intro z
    exact F.le_opNorm (z : H)
  exact ⟨w, hw, hnorm.trans (div_le_div_of_nonneg_right hF hc.1.le), huniq⟩

/-- Orthogonality follows directly from the two weak equations. -/
theorem galerkin_orthogonality_of_equations :
    ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
      [NormedSpace 𝕜 H] (a : BoundedSesquilinearFormValue 𝕜 H H)
      (F : ContinuousAntidualValue 𝕜 H) (W : Submodule 𝕜 H) (u : H) (w : W),
      (∀ z : H, a z u = F z) → (∀ z : W, a (z : H) (w : H) = F (z : H)) →
      ∀ z : W, a (z : H) (u - (w : H)) = 0 := by
  intro 𝕜 H _ _ _ a F W u u_h hu hu_h v
  calc
    a (v : H) (u - (u_h : H)) =
        a (v : H) u - a (v : H) (u_h : H) := (a (v : H)).map_sub u (u_h : H)
    _ = 0 := by rw [hu (v : H), hu_h v, sub_self]

/-- The pointwise Céa estimate needs only the form inequalities and
orthogonality, and is valid even in an incomplete normed space. -/
theorem cea_estimate_of_orthogonality
    (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [NormedSpace 𝕜 H] (a : BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ)
    (ha : FormBoundValue 𝕜 H H a M) (hc : FormCoerciveValue 𝕜 H a α)
    (W : Submodule 𝕜 H) (u : H) (u_h : W)
    (horth : ∀ v : W, a (v : H) (u - (u_h : H)) = 0) (v_h : W) :
    ‖u - (u_h : H)‖ ≤ (M / α) * ‖u - (v_h : H)‖ := by
  let e := u - (u_h : H)
  have hratio : 0 ≤ M / α := div_nonneg ha.1 hc.1.le
  change ‖e‖ ≤ (M / α) * ‖u - (v_h : H)‖
  by_cases he : e = 0
  · simpa only [he, norm_zero] using mul_nonneg hratio (norm_nonneg (u - (v_h : H)))
  have hpos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hz : a ((v_h : H) - (u_h : H)) e = 0 :=
    horth ⟨(v_h : H) - (u_h : H), W.sub_mem v_h.property u_h.property⟩
  have heq : a e e = a (u - (v_h : H)) e := by
    calc
      a e e = a ((u - (v_h : H)) + ((v_h : H) - (u_h : H))) e := by
        congr 2
        dsimp [e]
        abel
      _ = a (u - (v_h : H)) e := by
        rw [map_add, add_apply, hz, add_zero]
  have hbound : α * ‖e‖ ^ 2 ≤ M * ‖u - (v_h : H)‖ * ‖e‖ := calc
    α * ‖e‖ ^ 2 ≤ RCLike.re (a e e) := hc.2 e
    _ = RCLike.re (a (u - (v_h : H)) e) := congrArg RCLike.re heq
    _ ≤ ‖a (u - (v_h : H)) e‖ := RCLike.re_le_norm _
    _ ≤ M * ‖u - (v_h : H)‖ * ‖e‖ := ha.2 _ _
  have hcancel : α * ‖e‖ ≤ M * ‖u - (v_h : H)‖ :=
    (mul_le_mul_iff_left₀ hpos).mp (by simpa only [pow_two, mul_assoc] using hbound)
  calc
    ‖e‖ ≤ (M * ‖u - (v_h : H)‖) / α := (le_div_iff₀' hc.1).mpr hcancel
    _ = (M / α) * ‖u - (v_h : H)‖ := div_mul_eq_mul_div M α _ |>.symm

theorem cea_quasi_optimality : Spec.QuasiOptimality.{u, v} := by
  intro 𝕜 H _ _ _ _ a M α ha hc F W _hW u u_h hu hu_h
  have horth := galerkin_orthogonality_of_equations 𝕜 H a F W u u_h hu hu_h
  refine ⟨horth, ?_⟩
  rcases subsingleton_or_nontrivial H with hzero | hnontrivial
  · have heq : u = (u_h : H) := Subsingleton.elim _ _
    rw [heq, sub_self, norm_zero, Metric.infDist_zero_of_mem u_h.property, mul_zero]
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hposx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left
    (nonneg_of_mul_nonneg_left ((norm_nonneg (a x x)).trans (ha x x)) hposx) hposx
  have hpoint := cea_estimate_of_orthogonality 𝕜 H a M α ⟨hM, ha⟩ hc W u u_h horth
  have hnonneg : 0 ≤ M / α := div_nonneg hM hc.1.le
  by_cases hz : M / α = 0
  · simpa only [hz, zero_mul] using hpoint 0
  have hpos : 0 < M / α := lt_of_le_of_ne hnonneg (Ne.symm hz)
  have hinf : ‖u - (u_h : H)‖ / (M / α) ≤ Metric.infDist u (W : Set H) := by
    apply (Metric.le_infDist ⟨0, W.zero_mem⟩).mpr
    intro v hv
    rw [dist_eq_norm]
    exact (div_le_iff₀' hpos).mpr (hpoint ⟨v, hv⟩)
  exact (div_le_iff₀' hpos).mp hinf

theorem galerkin_sequence_convergence : Spec.SequenceConvergence.{u, v} := by
  classical
  intro 𝕜 H _ _ _ _ a M α ha hc W hW happ F
  obtain ⟨u, hu, _, _, _⟩ :=
    ExpandedFA.Hilbert.LaxMilgramEnergy.lax_milgram 𝕜 H a α hc F
  have hs (n : ℕ) : ∃ w : W n, ∀ z : W n, a (z : H) (w : H) = F (z : H) := by
    obtain ⟨w, hw, _, _⟩ := galerkin_solvability 𝕜 H a α hc F (W n) (hW n)
    exact ⟨w, hw⟩
  choose w hw using hs
  refine ⟨u, w, hu, hw, ?_⟩
  have hbound (n : ℕ) :=
    (cea_quasi_optimality 𝕜 H a M α ha hc F (W n) (hW n) u (w n) hu (hw n)).2
  have hlim : Filter.Tendsto (fun n => (M / α) * Metric.infDist u (W n : Set H))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (happ u)
  have herr : Filter.Tendsto (fun n => ‖u - (w n : H)‖) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hbound hlim
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm, norm_sub_rev] using herr

section Coordinates
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] {m : ℕ} {W : Submodule 𝕜 H}
  (a : BoundedSesquilinearFormValue 𝕜 H H) (e : Module.Basis (Fin m) 𝕜 W)

lemma synthesis_repr (z : W) : synthesis e (fun i => e.repr z i) = z := by
  exact e.sum_repr z

lemma synthesis_injective : Function.Injective (synthesis e) := by
  have he : synthesis e = e.equivFun.symm := by
    funext c
    exact (e.equivFun_symm_apply c).symm
  rw [he]
  exact e.equivFun.symm.injective

lemma form_synthesis_left (d : Fin m → 𝕜) (x : H) :
    a (synthesis e d : H) x = ∑ i, conj (d i) * a (e i : H) x := by
  simp [synthesis, map_sum, map_smulₛₗ]

lemma formMatrix_mulVec (c : Fin m → 𝕜) (i : Fin m) :
    (formMatrix a e).mulVec c i = a (e i : H) (synthesis e c : H) := by
  simp [formMatrix, Matrix.mulVec, dotProduct, synthesis, map_sum, map_smul,
    mul_comm]

private def pairing (B : Matrix (Fin m) (Fin m) 𝕜) (d c : Fin m → 𝕜) : 𝕜 :=
  ∑ i, conj (d i) * (B.mulVec c) i

lemma pairing_formMatrix (d c : Fin m → 𝕜) :
    pairing (formMatrix a e) d c = a (synthesis e d : H) (synthesis e c : H) := by
  simp only [pairing, formMatrix_mulVec]
  exact (form_synthesis_left a e d _).symm

lemma matrix_equations (F : H →L⋆[𝕜] 𝕜) (c : Fin m → 𝕜) :
    (∀ z : W, a (z : H) (synthesis e c : H) = F (z : H)) ↔
      (formMatrix a e).mulVec c = loadVector F e := by
  constructor
  · intro h
    funext i
    rw [formMatrix_mulVec]
    exact h (e i)
  · intro h z
    calc
      a (z : H) (synthesis e c : H) =
          ∑ i, conj (e.repr z i) * a (e i : H) (synthesis e c : H) := by
        rw [← form_synthesis_left, synthesis_repr]
      _ = ∑ i, conj (e.repr z i) * F (e i : H) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh := congrFun h i
        rw [formMatrix_mulVec] at hh
        rw [hh]
        rfl
      _ = F (z : H) := by
        have hh : F (synthesis e (fun i => e.repr z i) : H) =
            ∑ i, conj (e.repr z i) * F (e i : H) := by
          simp only [synthesis, Submodule.coe_sum, Submodule.coe_smul, map_sum,
            map_smulₛₗ, smul_eq_mul]
        rw [synthesis_repr] at hh
        exact hh.symm

lemma matrix_isUnit (α : ℝ) (hc : FormCoerciveValue 𝕜 H a α) :
    IsUnit (formMatrix a e) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (injective_iff_map_eq_zero (formMatrix a e).mulVecLin).mpr
  intro c hc0
  change (formMatrix a e).mulVec c = 0 at hc0
  have hp : pairing (formMatrix a e) c c = 0 := by simp [pairing, hc0]
  have hn := hc.2 (synthesis e c : H)
  rw [← pairing_formMatrix, hp] at hn
  have hz : synthesis e c = 0 := by
    apply norm_eq_zero.mp
    have : ‖synthesis e c‖ ^ 2 = 0 := by
      have : α * ‖synthesis e c‖ ^ 2 ≤ 0 := by simpa using hn
      nlinarith [sq_nonneg ‖synthesis e c‖, hc.1]
    nlinarith [norm_nonneg (synthesis e c)]
  apply synthesis_injective e
  simpa [synthesis] using hz

end Coordinates

theorem galerkin_matrix : Spec.MatrixConclusion.{u, v} := by
  intro 𝕜 H _ _ _ a α hc F W m e
  exact ⟨matrix_isUnit a e α hc, matrix_equations a e F⟩

end ExpandedFA.PartV.GalerkinCea
