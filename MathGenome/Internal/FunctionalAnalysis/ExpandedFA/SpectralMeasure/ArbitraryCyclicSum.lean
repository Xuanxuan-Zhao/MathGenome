import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.CyclicModel
import Mathlib.Order.Zorn
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
The arbitrary-Hilbert-space part of `fa2:p2:cyclic-model`, following the
bounded normal spectral theorem on complex Hilbert spaces. Cyclic spaces are
defined using the original generated star algebra. The disjoint-union model
uses the sum of the component measures, with no countability or sigma-finiteness
assumption. The final theorem also includes the upstream cyclic-vector model.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma self_mem_cyclicSpace (N : H →L[ℂ] H) (e : H) : e ∈ Spec.cyclicSpace N e := by
  apply Submodule.le_topologicalClosure
  exact ⟨1, by simp [Spec.algebraOrbit]⟩

/-- Every operator of the generated star algebra preserves the cyclic space. -/
lemma cyclicSpace_invariant (N : H →L[ℂ] H) (e : H)
    (a : StarAlgebra.elemental ℂ N) :
    ∀ x ∈ Spec.cyclicSpace N e, (a : H →L[ℂ] H) x ∈ Spec.cyclicSpace N e := by
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rintro x ⟨b, rfl⟩
  exact ⟨a * b, rfl⟩

/-- In a star-invariant space the orthogonal complement is star-invariant too. -/
lemma orthogonal_invariant (N : H →L[ℂ] H) (V : Submodule ℂ H)
    (hV : ∀ a : StarAlgebra.elemental ℂ N, ∀ x ∈ V, (a : H →L[ℂ] H) x ∈ V)
    (a : StarAlgebra.elemental ℂ N) :
    ∀ x ∈ Vᗮ, (a : H →L[ℂ] H) x ∈ Vᗮ := by
  intro x hx y hy
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hx _ (hV (star a) y hy)

lemma cyclicSpace_reducing (N : H →L[ℂ] H) (e : H) :
    Spec.IsReducing N (Spec.cyclicSpace N e) := by
  let a : StarAlgebra.elemental ℂ N := ⟨N, StarAlgebra.elemental.self_mem ℂ N⟩
  exact ⟨cyclicSpace_invariant N e a,
    orthogonal_invariant N (Spec.cyclicSpace N e) (cyclicSpace_invariant N e) a⟩

lemma cyclicSpace_le (N : H →L[ℂ] H) (e : H) (V : Submodule ℂ H)
    (hVclosed : IsClosed (V : Set H)) (he : e ∈ V)
    (hV : ∀ a : StarAlgebra.elemental ℂ N, ∀ x ∈ V, (a : H →L[ℂ] H) x ∈ V) :
    Spec.cyclicSpace N e ≤ V := by
  apply Submodule.topologicalClosure_minimal _ _ hVclosed
  rintro x ⟨a, rfl⟩
  exact hV a e he

/-- Unions of chains of orthogonal cyclic families remain orthogonal. -/
lemma orthogonal_chain_union (N : H →L[ℂ] H) (c : Set (Set H))
    (hc : IsChain (· ⊆ ·) c)
    (h : ∀ s ∈ c, s.Pairwise (fun e f => Spec.cyclicSpace N e ⟂ Spec.cyclicSpace N f)) :
    (⋃₀ c).Pairwise (fun e f => Spec.cyclicSpace N e ⟂ Spec.cyclicSpace N f) := by
  intro e he f hf hef
  obtain ⟨s, hs, hes⟩ := he
  obtain ⟨t, ht, hft⟩ := hf
  rcases hc.total hs ht with hst | hts
  · exact h t ht (hst hes) hft hef
  · exact h s hs hes (hts hft) hef


/-- Maximal orthogonal cyclic families have no nonzero perpendicular vector. -/
theorem orthogonal_decomposition : Spec.OrthogonalDecomposition.{u} := by
  classical
  intro H _ _ _ N _hN
  let F : Set (Set H) := {s | (∀ e ∈ s, e ≠ 0) ∧
    s.Pairwise (fun e f => Spec.cyclicSpace N e ⟂ Spec.cyclicSpace N f)}
  obtain ⟨s, hs⟩ := zorn_subset F (by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, orthogonal_chain_union N c hchain (fun t ht => (hc ht).2)⟩,
      fun t ht => subset_sUnion_of_mem ht⟩
    rintro e ⟨t, ht, het⟩
    exact (hc ht).1 e het)
  let W : Submodule ℂ H := (⨆ e : s, Spec.cyclicSpace N (e : H)).topologicalClosure
  have hWinv : ∀ a : StarAlgebra.elemental ℂ N, ∀ x ∈ W, (a : H →L[ℂ] H) x ∈ W := by
    intro a
    apply Submodule.topologicalClosure_mem_invtSubmodule
    rw [Module.End.mem_invtSubmodule]
    apply iSup_le
    intro e x hx
    exact Submodule.mem_iSup_of_mem e (cyclicSpace_invariant N e a x hx)
  have htotal : W = ⊤ := by
    have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    apply (Submodule.orthogonal_eq_bot_iff).mp
    apply eq_bot_iff.mpr
    intro x hx
    change x = 0
    by_contra hxzero
    have hcx : Spec.cyclicSpace N x ≤ Wᗮ :=
      cyclicSpace_le N x Wᗮ W.isClosed_orthogonal hx (orthogonal_invariant N W hWinv)
    have hxortho (e : s) : Spec.cyclicSpace N x ⟂ Spec.cyclicSpace N (e : H) := by
      exact hcx.trans (Submodule.orthogonal_le
        ((le_iSup (fun e : s => Spec.cyclicSpace N (e : H)) e).trans
          (Submodule.le_topologicalClosure _)))
    have hnew : insert x s ∈ F := by
      refine ⟨?_, ?_⟩
      · intro e he
        rcases he with rfl | he
        · exact hxzero
        · exact hs.1.1 e he
      · intro e he f hf hef
        rcases he with rfl | he <;> rcases hf with rfl | hf
        · exact (hef rfl).elim
        · exact hxortho ⟨f, hf⟩
        · exact (hxortho ⟨e, he⟩).symm
        · exact hs.1.2 he hf hef
    have hxs : x ∈ s := hs.2 hnew (subset_insert x s) (mem_insert x s)
    have hxW : x ∈ W := Submodule.le_topologicalClosure _
      (Submodule.mem_iSup_of_mem (⟨x, hxs⟩ : s) (self_mem_cyclicSpace N x))
    exact hxzero ((inner_self_eq_zero (𝕜 := ℂ)).mp (hx x hxW))
  have hortho : OrthogonalFamily ℂ (fun e : s => Spec.cyclicSpace N (e : H))
      (fun e => (Spec.cyclicSpace N (e : H)).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro e f hef
    exact hs.1.2 e.property f.property (fun h => hef (Subtype.ext h))
  have (e : s) : CompleteSpace (Spec.cyclicSpace N (e : H)) := by
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let hsum := IsHilbertSum.mkInternal (fun e : s => Spec.cyclicSpace N (e : H))
    hortho (le_of_eq htotal.symm)
  refine ⟨s, hs.1.1, hs.1.2, fun e _ => cyclicSpace_reducing N e, htotal,
    hsum.linearIsometryEquiv.symm, ?_⟩
  exact hsum.linearIsometryEquiv_symm_apply


lemma orbit_range_eq (N : H →L[ℂ] H) (hN : IsStarNormal N) (e : H) :
    LinearMap.range (CyclicModel.orbitMap N hN e) = LinearMap.range (Spec.algebraOrbit N e) := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    have hf : cfcHom hN f ∈ StarAlgebra.elemental ℂ N := by
      rw [← range_cfcHom ℂ hN]
      exact ⟨f, rfl⟩
    exact ⟨⟨cfcHom hN f, hf⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha : (a : H →L[ℂ] H) ∈ (cfcHom (R := ℂ) hN).range := by
      rw [range_cfcHom ℂ hN]
      exact a.property
    obtain ⟨f, hf⟩ := ha
    exact ⟨f, congrArg (fun T : H →L[ℂ] H => T e) hf⟩

/-- The local spectral model onto the closed cyclic space of any vector,
without assuming that vector is cyclic in the whole Hilbert space. -/
theorem local_cyclic_model (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : NormalPVM.Spec.Resolves N E) (e : H) :
    ∃ U : Lp ℂ 2 (E.diagonalMeasure e) ≃ₗᵢ[ℂ] Spec.cyclicSpace N e,
      ∀ f, (U (CyclicModel.Spec.multiplier (E.diagonalMeasure e)
        (CyclicModel.Spec.coordinate N) f) : H) = N (U f : H) := by
  let μ := E.diagonalMeasure e
  let : CompleteSpace (Spec.cyclicSpace N e) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let j := (ContinuousMap.toLp 2 μ ℂ : C(spectrum ℂ N, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap
  let v : C(spectrum ℂ N, ℂ) →ₗ[ℂ] Spec.cyclicSpace N e :=
    (CyclicModel.orbitMap N hN e).codRestrict _ (fun f =>
      Submodule.le_topologicalClosure _ ((orbit_range_eq N hN e) ▸ ⟨f, rfl⟩))
  have hj : DenseRange j := CyclicModel.continuous_density H N μ
  have hv : DenseRange v := by
    change Dense (Set.range v)
    rw [Subtype.dense_iff, ← Set.range_comp]
    change (Spec.cyclicSpace N e : Set H) ⊆ closure (Set.range (CyclicModel.orbitMap N hN e))
    rw [← LinearMap.coe_range, orbit_range_eq]
    exact subset_rfl
  have hn : ∀ f, ‖v f‖ = ‖j f‖ := CyclicModel.orbitMap_norm N hN E hE e
  let U := (LinearEquiv.refl ℂ C(spectrum ℂ N, ℂ)).extendOfIsometry j v hj hv hn
  let J : Lp ℂ 2 μ →ₗᵢ[ℂ] H := (Spec.cyclicSpace N e).subtypeₗᵢ.comp U.toLinearIsometry
  have hJ (f : C(spectrum ℂ N, ℂ)) : J (ContinuousMap.toLp 2 μ ℂ f) = cfcHom hN f e := by
    exact congrArg (fun x : Spec.cyclicSpace N e => (x : H))
      (LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ C(spectrum ℂ N, ℂ)) j v hj hv hn f)
  have hinter (g : C(spectrum ℂ N, ℂ)) (f : Lp ℂ 2 μ) :
      J (CyclicModel.Spec.multiplier μ g f) = cfcHom hN g (J f) := by
    apply congrFun (hj.equalizer
      (J.continuous.comp (CyclicModel.Spec.multiplier μ g).continuous)
      ((cfcHom hN g).continuous.comp J.continuous) ?_) f
    funext k
    change J (CyclicModel.Spec.multiplier μ g (ContinuousMap.toLp 2 μ ℂ k)) =
      cfcHom hN g (J (ContinuousMap.toLp 2 μ ℂ k))
    rw [CyclicModel.multiplier_toLp, hJ, hJ, map_mul]
    rfl
  refine ⟨U, fun f => ?_⟩
  change J (CyclicModel.Spec.multiplier μ (CyclicModel.Spec.coordinate N) f) = N (J f)
  simpa only [CyclicModel.Spec.coordinate, cfcHom_id] using
    hinter (CyclicModel.Spec.coordinate N) f

namespace DisjointL2
variable {I : Type v} {S : I → Type w} [m : ∀ i, MeasurableSpace (S i)]
variable (μ : ∀ i, Measure (S i))

lemma measurable_mk (i : I) : Measurable (Sigma.mk i : S i → Sigma S) :=
  Measurable.of_le_map (iInf_le _ i)

lemma measurable_iff {T : Type*} [MeasurableSpace T] (f : Sigma S → T) :
    Measurable f ↔ ∀ i, Measurable (fun s => f ⟨i, s⟩) := by
  constructor
  · intro hf i
    exact hf.comp (measurable_mk i)
  · intro hf B hB
    exact MeasurableSpace.measurableSet_iInf.mpr (fun i => hf i hB)

lemma measure_apply (B : Set (Sigma S)) (hB : MeasurableSet B) :
    Spec.disjointMeasure μ B = ∑' i, μ i (Sigma.mk i ⁻¹' B) := by
  simp only [Spec.disjointMeasure, Measure.sum_apply _ hB,
    Measure.map_apply (measurable_mk _) hB]

lemma ae_iff {P : Sigma S → Prop} (hP : MeasurableSet {x | P x}) :
    (∀ᵐ x ∂Spec.disjointMeasure μ, P x) ↔ ∀ i, ∀ᵐ s ∂μ i, P ⟨i, s⟩ := by
  rw [Spec.disjointMeasure, Measure.ae_sum_iff' hP]
  exact forall_congr' fun i => ae_map_iff (measurable_mk i).aemeasurable hP

lemma lintegral (f : Sigma S → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂Spec.disjointMeasure μ = ∑' i, ∫⁻ s, f ⟨i, s⟩ ∂μ i := by
  rw [Spec.disjointMeasure, lintegral_sum_measure]
  congr 1
  funext i
  exact lintegral_map hf (measurable_mk i)

lemma l2_enorm_sq {A : Type*} [MeasurableSpace A] {ν : Measure A}
    (f : Lp ℂ 2 ν) : ‖f‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  simpa [Lp.enorm_def, ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (Lp.aestronglyMeasurable f)

/-- Glue the measurable chosen representatives of the component L² classes. -/
def glue (f : ∀ i, Lp ℂ 2 (μ i)) : Sigma S → ℂ := fun x => f x.1 x.2

lemma measurable_glue (f : ∀ i, Lp ℂ 2 (μ i)) : Measurable (glue μ f) := by
  apply (measurable_iff _).mpr
  intro i
  exact (Lp.stronglyMeasurable (f i)).measurable

lemma glue_lintegral (f : ∀ i, Lp ℂ 2 (μ i)) :
    ∫⁻ x, ‖glue μ f x‖ₑ ^ 2 ∂Spec.disjointMeasure μ = ∑' i, ‖f i‖ₑ ^ 2 := by
  rw [lintegral μ _ ((measurable_glue μ f).enorm.pow_const 2)]
  exact tsum_congr fun i => (l2_enorm_sq (f i)).symm

lemma glue_memLp (f : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    MemLp (glue μ (fun i => f i)) 2 (Spec.disjointMeasure μ) := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (measurable_glue μ _).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [glue_lintegral]
  have hsum : Summable (fun i => ‖f i‖ ^ 2) := by
    simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using
    hsum.tsum_ofReal_lt_top

def toUnion (f : lp (fun i => Lp ℂ 2 (μ i)) 2) : Lp ℂ 2 (Spec.disjointMeasure μ) :=
  (glue_memLp μ f).toLp (glue μ (fun i => f i))

lemma toUnion_ae (f : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    toUnion μ f =ᵐ[Spec.disjointMeasure μ] glue μ (fun i => f i) :=
  MemLp.coeFn_toLp _

lemma toUnion_norm (f : lp (fun i => Lp ℂ 2 (μ i)) 2) : ‖toUnion μ f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, l2_enorm_sq]
  have hae : (fun x => ‖toUnion μ f x‖ₑ ^ 2) =ᵐ[Spec.disjointMeasure μ]
      fun x => ‖glue μ (fun i => f i) x‖ₑ ^ 2 := by
    filter_upwards [toUnion_ae μ f] with x hx
    rw [hx]
  rw [lintegral_congr_ae hae, glue_lintegral]
  have hsum : Summable (fun i => ‖f i‖ ^ 2) := by
    simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  rw [show ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f,
    ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsum]
  exact tsum_congr fun i => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma glue_add (f g : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    glue μ (fun i => (f + g) i) =ᵐ[Spec.disjointMeasure μ]
      fun x => glue μ (fun i => f i) x + glue μ (fun i => g i) x := by
  apply (ae_iff μ (measurableSet_eq_fun (measurable_glue μ _)
    ((measurable_glue μ _).add (measurable_glue μ _)))).mpr
  intro i
  exact Lp.coeFn_add (f i) (g i)

lemma toUnion_add (f g : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    toUnion μ (f + g) = toUnion μ f + toUnion μ g := by
  apply Lp.ext
  filter_upwards [toUnion_ae μ (f + g), toUnion_ae μ f, toUnion_ae μ g,
    glue_add μ f g, Lp.coeFn_add (toUnion μ f) (toUnion μ g)] with x h h1 h2 h3 h4
  simp only [Pi.add_apply] at h4
  rw [h, h3, h4, h1, h2]

lemma glue_smul (c : ℂ) (f : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    glue μ (fun i => (c • f) i) =ᵐ[Spec.disjointMeasure μ]
      fun x => c • glue μ (fun i => f i) x := by
  apply (ae_iff μ (measurableSet_eq_fun (measurable_glue μ _)
    ((measurable_glue μ _).const_smul c))).mpr
  intro i
  exact Lp.coeFn_smul c (f i)

lemma toUnion_smul (c : ℂ) (f : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    toUnion μ (c • f) = c • toUnion μ f := by
  apply Lp.ext
  filter_upwards [toUnion_ae μ (c • f), toUnion_ae μ f,
    glue_smul μ c f, Lp.coeFn_smul c (toUnion μ f)] with x h h1 h2 h3
  simp only [Pi.smul_apply] at h3
  rw [h, h2, h3, h1]

def linearIsometry : lp (fun i => Lp ℂ 2 (μ i)) 2 →ₗᵢ[ℂ]
    Lp ℂ 2 (Spec.disjointMeasure μ) where
  toFun := toUnion μ
  map_add' := toUnion_add μ
  map_smul' := toUnion_smul μ
  norm_map' := toUnion_norm μ

lemma component_memLp (f : Lp ℂ 2 (Spec.disjointMeasure μ)) (i : I) :
    MemLp (fun s => f ⟨i, s⟩) 2 (μ i) := by
  exact (MemLp.mono_measure (Measure.le_sum _ i) (Lp.memLp f)).comp_of_map
    (measurable_mk i).aemeasurable

def component (f : Lp ℂ 2 (Spec.disjointMeasure μ)) (i : I) : Lp ℂ 2 (μ i) :=
  (component_memLp μ f i).toLp (fun s => f ⟨i, s⟩)

lemma component_ae (f : Lp ℂ 2 (Spec.disjointMeasure μ)) (i : I) :
    component μ f i =ᵐ[μ i] fun s => f ⟨i, s⟩ := MemLp.coeFn_toLp _

lemma component_lintegral (f : Lp ℂ 2 (Spec.disjointMeasure μ)) (i : I) :
    ‖component μ f i‖ₑ ^ 2 = ∫⁻ s, ‖f ⟨i, s⟩‖ₑ ^ 2 ∂μ i := by
  rw [l2_enorm_sq]
  apply lintegral_congr_ae
  filter_upwards [component_ae μ f i] with s hs
  rw [hs]

lemma component_memℓp (f : Lp ℂ 2 (Spec.disjointMeasure μ)) :
    Memℓp (component μ f) 2 := by
  have hs : ∑' i, ‖component μ f i‖ₑ ^ 2 = ‖f‖ₑ ^ 2 := by
    rw [l2_enorm_sq, lintegral μ _ ((Lp.stronglyMeasurable f).measurable.enorm.pow_const 2)]
    exact tsum_congr fun i => component_lintegral μ f i
  have hfin : ∑' i, ‖component μ f i‖ₑ ^ 2 ≠ ∞ := by
    rw [hs]
    exact ENNReal.pow_ne_top (by finiteness)
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  simpa using ENNReal.summable_toReal hfin

lemma toUnion_surjective : Function.Surjective (toUnion μ) := by
  intro f
  let v : lp (fun i => Lp ℂ 2 (μ i)) 2 := ⟨component μ f, component_memℓp μ f⟩
  refine ⟨v, ?_⟩
  apply Lp.ext
  apply (toUnion_ae μ v).trans
  apply (ae_iff μ (measurableSet_eq_fun (measurable_glue μ _)
    (Lp.stronglyMeasurable f).measurable)).mpr
  intro i
  exact component_ae μ f i

/-- L² of an arbitrary measurable disjoint union is the Hilbert direct sum.
The proof uses arbitrary sums of measures, not a sigma-finite product theorem. -/
def equivalence : lp (fun i => Lp ℂ 2 (μ i)) 2 ≃ₗᵢ[ℂ]
    Lp ℂ 2 (Spec.disjointMeasure μ) :=
  LinearIsometryEquiv.ofSurjective (linearIsometry μ) (toUnion_surjective μ)

end DisjointL2

/-- The bounded normal operator is multiplication on the sum-measure
space. The construction does not identify different cyclic copies of a point
of the spectrum, and does not require a finite common control measure. -/
theorem multiplication_model : Spec.MultiplicationTheorem.{u} := by
  classical
  intro H _ _ _ N hN
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem H N hN
  obtain ⟨s, _hnonzero, horth, _hred, htotal, _⟩ := orthogonal_decomposition H N hN
  let μ : s → Measure (spectrum ℂ N) := fun e => E.diagonalMeasure (e : H)
  have (e : s) : IsFiniteMeasure (μ e) := by dsimp [μ]; infer_instance
  choose Ui hUi using fun e : s => local_cyclic_model N hN E hE (e : H)
  let A (e : s) : Lp ℂ 2 (μ e) →ₗᵢ[ℂ] H :=
    (Spec.cyclicSpace N (e : H)).subtypeₗᵢ.comp (Ui e).toLinearIsometry
  have hA : OrthogonalFamily ℂ (fun e : s => Lp ℂ 2 (μ e)) A := by
    intro e f hef x y
    exact (horth e.property f.property (fun h => hef (Subtype.ext h))).inner_eq
      (Ui e x).property (Ui f y).property
  have hArange (e : s) : LinearMap.range (A e).toLinearMap = Spec.cyclicSpace N (e : H) := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact (Ui e f).property
    · intro hx
      obtain ⟨f, hf⟩ := (Ui e).surjective ⟨x, hx⟩
      exact ⟨f, congrArg (fun y : Spec.cyclicSpace N (e : H) => (y : H)) hf⟩
  let hsum : IsHilbertSum ℂ (fun e : s => Lp ℂ 2 (μ e)) A :=
    IsHilbertSum.mk hA (by simp_rw [hArange]; exact le_of_eq htotal.symm)
  let W := hsum.linearIsometryEquiv.symm
  let T (e : s) : Lp ℂ 2 (μ e) →L[ℂ] Lp ℂ 2 (μ e) :=
    CyclicModel.Spec.multiplier (μ e) (CyclicModel.Spec.coordinate N)
  have hinter (e : s) (f : Lp ℂ 2 (μ e)) : A e (T e f) = N (A e f) := hUi e f
  have hT (e : s) : ‖T e‖ ≤ ‖N‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg N)
    intro f
    calc
      ‖T e f‖ = ‖A e (T e f)‖ := ((A e).norm_map _).symm
      _ = ‖N (A e f)‖ := congrArg norm (hinter e f)
      _ ≤ ‖N‖ * ‖A e f‖ := N.le_opNorm _
      _ = ‖N‖ * ‖f‖ := by rw [(A e).norm_map]
  let D := lp.mapCLM 2 T (norm_nonneg N) hT
  have hdiag (v : lp (fun e : s => Lp ℂ 2 (μ e)) 2) : W (D v) = N (W v) := by
    have hsumN := (hsum.hasSum_linearIsometryEquiv_symm v).map N N.continuous
    rw [← hsumN.tsum_eq]
    change (∑' e, A e (T e (v e))) = ∑' e, N (A e (v e))
    exact tsum_congr fun e => hinter e (v e)
  let Q := DisjointL2.equivalence μ
  let U : Lp ℂ 2 (Spec.disjointMeasure μ) ≃ₗᵢ[ℂ] H := Q.symm.trans W
  let M : Lp ℂ 2 (Spec.disjointMeasure μ) →L[ℂ] Lp ℂ 2 (Spec.disjointMeasure μ) :=
    Q.toLinearIsometry.toContinuousLinearMap.comp
      (D.comp Q.symm.toLinearIsometry.toContinuousLinearMap)
  let g : (Σ _ : s, spectrum ℂ N) → ℂ := fun x => (x.2 : ℂ)
  have hg : Measurable g := by
    apply (DisjointL2.measurable_iff _).mpr
    intro e
    exact continuous_subtype_val.measurable
  have hgbound (x : Σ _ : s, spectrum ℂ N) : ‖g x‖ ≤ ‖N‖ := by
    exact (spectrum.norm_le_norm_mul_of_mem x.2.property).trans
      (mul_le_of_le_one_right (norm_nonneg N) ContinuousLinearMap.norm_id_le)
  have hpoint (v : lp (fun e : s => Lp ℂ 2 (μ e)) 2) :
      DisjointL2.glue μ (fun e => D v e) =ᵐ[Spec.disjointMeasure μ]
        fun x => g x * DisjointL2.glue μ (fun e => v e) x := by
    apply (DisjointL2.ae_iff μ (measurableSet_eq_fun
      (DisjointL2.measurable_glue μ _) (hg.mul (DisjointL2.measurable_glue μ _)))).mpr
    intro e
    exact CyclicModel.multiplier_apply (μ e) (CyclicModel.Spec.coordinate N) (v e)
  refine ⟨s, (fun _ => spectrum ℂ N), (fun _ => inferInstance), μ,
    (fun _ => inferInstance), g, hg, hgbound, M, U, ?_, ?_⟩
  · intro f
    have h1 := DisjointL2.toUnion_ae μ (D (Q.symm f))
    change M f =ᵐ[Spec.disjointMeasure μ] DisjointL2.glue μ (fun e => D (Q.symm f) e) at h1
    have h2 := DisjointL2.toUnion_ae μ (Q.symm f)
    change Q (Q.symm f) =ᵐ[Spec.disjointMeasure μ] DisjointL2.glue μ (fun e => Q.symm f e) at h2
    rw [Q.apply_symm_apply] at h2
    filter_upwards [h1, h2, hpoint (Q.symm f)] with x hx1 hx2 hx3
    rw [hx1, hx3, ← hx2]
  · intro f
    change W (Q.symm (Q (D (Q.symm f)))) = N (W (Q.symm f))
    rw [Q.symm_apply_apply]
    exact hdiag (Q.symm f)

/-- Cyclic and arbitrary multiplicity versions, for every complex Hilbert
space, including the zero space. -/
theorem cyclic_models : Spec.FullTheorem.{u} :=
  ⟨CyclicModel.exists_cyclic_model, orthogonal_decomposition, multiplication_model⟩

end ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
