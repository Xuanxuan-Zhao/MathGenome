import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.LocalGraphAndAmbientInverse
import MathGenome.Internal.MultivariableAnalysis.D04.C14.EmbeddedManifoldCharts
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Local coordinate graphs and ambient inverses for full-rank parametrizations
(d04:14:charts), including finite regularity, half-space restrictions and k=0.
The inverse theorem is applied on a Euclidean extension, not on the half-space. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
open Specs.D04.C14.LocalGraphAndAmbientInverse.Model
open private inverse_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

abbrev coordinateProjection := @Specs.D04.C14.LocalGraphAndAmbientInverse.Model.coordinateProjection

-- Algebra: a spanning family of pulled-back coordinate covectors contains a basis.
theorem independent_coordinate_projection :
    Specs.D04.C14.LocalGraphAndAmbientInverse.independent_coordinate_projectionType := by
  intro k n A hA
  classical
  let bₙ := Specs.D04.C01.EuclideanInterfaces.Model.standardBasis n
  let c : Fin n → Module.Dual ℝ (E k) := fun i => (bₙ.coord i).comp A.toLinearMap
  have hspan : Submodule.span ℝ (range c) = ⊤ := by
    calc
      Submodule.span ℝ (range c) =
          (Submodule.span ℝ (range bₙ.dualBasis)).map A.toLinearMap.dualMap := by
        rw [Submodule.map_span, ← range_comp, Module.Basis.coe_dualBasis]
        rfl
      _ = ⊤ := by
        rw [bₙ.dualBasis.span_eq, Submodule.map_top, LinearMap.range_eq_top]
        exact LinearMap.dualMap_surjective_of_injective hA
  obtain ⟨ι, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ c
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι ℝ (Module.Dual ℝ (E k)) :=
    Module.Basis.mk hli (by rw [hsp, hspan])
  have hc : Fintype.card ι = k := by
    rw [← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
    exact finrank_euclideanSpace_fin
  let e : Fin k ≃ ι := (Fintype.equivFinOfCardEq hc).symm
  let s : Fin k ↪ Fin n := ⟨a ∘ e, ha.comp e.injective⟩
  let T := (coordinateProjection s).comp A
  have hT : Function.Injective T := by
    intro x y hxy
    apply Module.eval_apply_injective ℝ
    apply b.ext
    intro i
    have h := congrArg (fun z : E k => z (e.symm i)) hxy
    change (A x) (a (e (e.symm i))) = (A y) (a (e (e.symm i))) at h
    simp only [e.apply_symm_apply] at h
    simp only [Module.Dual.eval_apply, b, Module.Basis.mk_apply, Function.comp_apply,
      c, LinearMap.comp_apply, Module.Basis.coord_apply]
    simpa only [bₙ, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      ContinuousLinearMap.coe_coe] using h
  exact ⟨s, (LinearEquiv.ofInjectiveEndo T.toLinearMap hT).toContinuousLinearEquiv, rfl⟩

theorem local_graph_and_ambient_inverse :
    Specs.D04.C14.LocalGraphAndAmbientInverse.local_graph_and_ambient_inverseType := by
  intro r k n V φ u half hr hkn hhalf hV hφ hu
  obtain ⟨W, g, hW, huW, hagree, hg, hgrank⟩ := hφ u hu
  obtain ⟨s, B, hB⟩ := independent_coordinate_projection (fderiv ℝ g u) (hgrank u huW)
  let P := coordinateProjection s
  have hgder : HasFDerivAt g (fderiv ℝ g u) u :=
    ((hg.contDiffAt (hW.mem_nhds huW)).differentiableAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))).hasFDerivAt
  have hFder := P.hasFDerivAt.comp u hgder
  have hF : ContDiffOn ℝ r (P ∘ g) W := P.contDiff.comp_contDiffOn hg
  obtain ⟨X, Y, q, hI, hq⟩ := inverse_neighborhood W (P ∘ g) u B hr.1 hW hF huW
    (hB.trans hFder.fderiv.symm)
  have hIcopy := hI
  obtain ⟨hX, hY, huX, hFuY, hXW, hbij, hqmap, hleft, hright, hrest⟩ := hI
  have hL : ∀ {v}, v ∈ V ∩ X → q (P (φ v)) = v := by
    intro v hv
    rw [← hagree ⟨hv.1, hXW hv.2⟩]
    exact hleft hv.2
  have hproj : (P ∘ φ) '' (V ∩ X) = Y ∩ q ⁻¹' V := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · change P (φ w) ∈ Y
        rw [← hagree ⟨hw.1, hXW hw.2⟩]
        exact hbij.mapsTo hw.2
      · change q (P (φ w)) ∈ V
        rw [hL hw]
        exact hw.1
    · intro hv
      refine ⟨q v, ⟨hv.2, hqmap hv.1⟩, ?_⟩
      change P (φ (q v)) = v
      rw [← hagree ⟨hv.2, hXW (hqmap hv.1)⟩]
      exact hright hv.1
  refine ⟨s, W, g, X, Y, q, hW, huW, hagree, hg, hIcopy, hq, ?_, ?_, hproj, ?_, ?_, ?_, (fun _ hv => hL hv), ?_⟩
  · exact hg.comp hq (fun v hv => hXW (hqmap hv))
  · intro v hv
    exact hright hv
  · ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, hv, rfl⟩, ?_⟩
      change φ v = g (q (P (φ v)))
      rw [hL hv]
      exact (hagree ⟨hv.1, hXW hv.2⟩).symm
    · intro hx
      have hv := hproj ▸ hx.1
      refine ⟨q (P x), ⟨hv.2, hqmap hv.1⟩, ?_⟩
      rw [← hagree ⟨hv.2, hXW (hqmap hv.1)⟩]
      exact hx.2.symm
  · exact hq.comp P.contDiff.contDiffOn (fun _ hv => hv)
  · rintro x ⟨v, hv, rfl⟩
    change q (P (φ v)) ∈ V ∩ X
    rw [hL hv]
    exact hv
  · rintro x ⟨v, hv, rfl⟩
    change φ (q (P (φ v))) = φ v
    rw [hL hv]

theorem zero_parameter_graph :
    Specs.D04.C14.LocalGraphAndAmbientInverse.zero_parameter_graphType := by
  intro n V φ u hu
  have hV : V = univ := by
    apply eq_univ_of_forall
    intro v
    simpa only [Subsingleton.elim v u] using hu
  refine ⟨hV, ?_, ?_⟩
  · ext x
    simp only [mem_image, mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [Subsingleton.elim v u]
    · intro hx
      exact ⟨u, hu, hx.symm⟩
  · intro s
    refine ⟨?_, ?_, ?_⟩
    · apply eq_univ_of_forall
      intro v
      exact ⟨u, hu, Subsingleton.elim _ _⟩
    · intro v hv
      exact Subsingleton.elim _ _
    · rintro x ⟨v, hv, rfl⟩
      rw [Subsingleton.elim (0 : E 0) v]

end D04
