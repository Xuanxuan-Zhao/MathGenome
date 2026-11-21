import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.BoundedFlowIntegrality
import MathGenome.Internal.ExtremalOptimization.P205.Networks.IncidenceTU
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.IntegralVertices
import Mathlib.Topology.Order.Bornology

/-! W35: bounded integer flows. Equalities become opposing inequalities;
coordinate bounds give a bounded TU polyhedron. Relabelling retains arbitrary
finite vertex and arc types, including empty types. -/

universe u v
noncomputable section
open Matrix Set
open P205.Polyhedra
open Specs.P205.Networks (boundedFlowSet)
namespace P205.Networks.BoundedFlowIntegrality

private abbrev Rows (V : Type u) (n : ℕ) := ((V ⊕ V) ⊕ Fin n) ⊕ Fin n

private def constraintMatrix {V : Type u} {n : ℕ} (tail head : Fin n → V) :
    Matrix (Rows V n) (Fin n) ℤ := by
  classical
  exact Matrix.fromRows
    (Matrix.fromRows
      (Matrix.fromRows (directedIncidence tail head) (-directedIncidence tail head)) 1) (-1)

private def constraintBound {V : Type u} {n : ℕ}
    (b : V → ℤ) (lower upper : Fin n → ℤ) : Rows V n → ℤ :=
  Sum.elim (Sum.elim (Sum.elim b (-b)) upper) (-lower)

private def finMatrix {V : Type u} [Fintype V] {n : ℕ} (tail head : Fin n → V) :
    Matrix (Fin (Fintype.card (Rows V n))) (Fin n) ℤ :=
  (constraintMatrix tail head).submatrix (Fintype.equivFin (Rows V n)).symm id

private def finBound {V : Type u} [Fintype V] {n : ℕ}
    (b : V → ℤ) (lower upper : Fin n → ℤ) : Fin (Fintype.card (Rows V n)) → ℤ :=
  fun i => constraintBound b lower upper ((Fintype.equivFin (Rows V n)).symm i)

private lemma finMatrix_tu {V : Type u} [Fintype V] {n : ℕ} (tail head : Fin n → V) :
    (finMatrix tail head).IsTotallyUnimodular := by
  classical
  exact (TotalUnimodularity.opposing_rows_with_bounds
    (directed_incidence_tu tail head)).submatrix _ _

private lemma polyhedron_eq_flow {V : Type u} [Fintype V] {n : ℕ}
    (tail head : Fin n → V) (b : V → ℤ) (lower upper : Fin n → ℤ) :
    polyhedron ((finMatrix tail head).map (Int.cast : ℤ → ℝ))
      (fun i => (finBound b lower upper i : ℝ)) =
    boundedFlowSet tail head b lower upper := by
  classical
  ext f
  change (∀ i, ∑ j, (constraintMatrix tail head
      ((Fintype.equivFin (Rows V n)).symm i) j : ℝ) * f j ≤
      (constraintBound b lower upper ((Fintype.equivFin (Rows V n)).symm i) : ℝ)) ↔ _
  trans (∀ r : Rows V n, ∑ j, (constraintMatrix tail head r j : ℝ) * f j ≤
    (constraintBound b lower upper r : ℝ))
  · exact (Fintype.equivFin (Rows V n)).symm.surjective.forall
      (p := fun r => ∑ j, (constraintMatrix tail head r j : ℝ) * f j ≤
        (constraintBound b lower upper r : ℝ)) |>.symm
  · simp only [constraintMatrix, constraintBound, boundedFlowSet, Set.mem_ofPred_eq,
      Sum.forall, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      Matrix.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
      Matrix.one_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, neg_le_neg_iff,
      Matrix.mulVec, dotProduct, funext_iff, Matrix.map_apply]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, hu⟩, hl⟩
      exact ⟨fun i => le_antisymm (h₁ i) (h₂ i), fun j => ⟨hl j, hu j⟩⟩
    · rintro ⟨hb, hbounds⟩
      exact ⟨⟨⟨fun i => (hb i).le, fun i => (hb i).ge⟩,
        fun j => (hbounds j).2⟩, fun j => (hbounds j).1⟩

private lemma flow_bounded {V : Type u} {n : ℕ}
    (tail head : Fin n → V) (b : V → ℤ) (lower upper : Fin n → ℤ) :
    Bornology.IsBounded (boundedFlowSet tail head b lower upper) := by
  apply (Metric.isBounded_Icc (fun e => (lower e : ℝ)) (fun e => (upper e : ℝ))).subset
  intro f hf
  exact ⟨fun e => hf.2 e |>.1, fun e => hf.2 e |>.2⟩

private theorem fin_vertex_integral {V : Type u} [Fintype V] {n : ℕ}
    (tail head : Fin n → V) (b : V → ℤ) (lower upper : Fin n → ℤ)
    (f : Fin n → ℝ) (hf : f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ) :
    ∀ e, ∃ z : ℤ, f e = (z : ℝ) := by
  apply P205.Polyhedra.vertex_integral (finMatrix tail head) (finBound b lower upper)
    f (finMatrix_tu tail head)
  simpa only [IsVertex, polyhedron_eq_flow] using hf

private theorem fin_integral_minimizer {V : Type u} [Fintype V] {n : ℕ}
    (tail head : Fin n → V) (b : V → ℤ) (lower upper : Fin n → ℤ) (c : Fin n → ℝ)
    (hne : (boundedFlowSet tail head b lower upper).Nonempty) :
    ∃ f, f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ ∧
      (∀ e, ∃ z : ℤ, f e = (z : ℝ)) ∧
      ∀ g ∈ boundedFlowSet tail head b lower upper, c ⬝ᵥ f ≤ c ⬝ᵥ g := by
  have heq := polyhedron_eq_flow tail head b lower upper
  obtain ⟨f, hf, hint, hopt⟩ := P205.Polyhedra.bounded_integral_minimizer
    (finMatrix tail head) (finBound b lower upper) c (finMatrix_tu tail head)
    (heq.symm ▸ hne) (heq.symm ▸ flow_bounded tail head b lower upper)
  exact ⟨f, by simpa only [IsVertex, heq] using hf, hint, heq ▸ hopt⟩

/-- Permute arc coordinates by an arbitrary equivalence. -/
private def relabel {E : Type v} {F : Type*} (e : F ≃ E) :
    (E → ℝ) ≃ₗ[ℝ] (F → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e

private lemma mem_relabel_flow {V : Type u} {E : Type v} {F : Type*}
    [Fintype E] [Fintype F] (e : F ≃ E) (tail head : E → V)
    (b : V → ℤ) (lower upper : E → ℤ) (f : E → ℝ) :
    relabel e f ∈ boundedFlowSet (tail ∘ e) (head ∘ e) b (lower ∘ e) (upper ∘ e) ↔
      f ∈ boundedFlowSet tail head b lower upper := by
  have hbal : (directedIncidence (tail ∘ e) (head ∘ e)).map (Int.cast : ℤ → ℝ) *ᵥ
      relabel e f = (directedIncidence tail head).map (Int.cast : ℤ → ℝ) *ᵥ f := by
    ext i
    exact e.sum_comp (fun j => (directedIncidence tail head i j : ℝ) * f j)
  change (_ = _ ∧ ∀ j, (lower (e j) : ℝ) ≤ f (e j) ∧ f (e j) ≤ (upper (e j) : ℝ)) ↔ _
  rw [hbal]
  change (_ ∧ ∀ j, (lower (e j) : ℝ) ≤ f (e j) ∧ f (e j) ≤ (upper (e j) : ℝ)) ↔
    (_ ∧ ∀ j, (lower j : ℝ) ≤ f j ∧ f j ≤ (upper j : ℝ))
  exact and_congr Iff.rfl (e.surjective.forall
    (p := fun j => (lower j : ℝ) ≤ f j ∧ f j ≤ (upper j : ℝ))).symm

private lemma image_relabel_flow {V : Type u} {E : Type v} {F : Type*}
    [Fintype E] [Fintype F] (e : F ≃ E) (tail head : E → V)
    (b : V → ℤ) (lower upper : E → ℤ) :
    relabel e '' boundedFlowSet tail head b lower upper =
      boundedFlowSet (tail ∘ e) (head ∘ e) b (lower ∘ e) (upper ∘ e) := by
  ext x
  obtain ⟨f, rfl⟩ := (relabel e).surjective x
  rw [(relabel e).injective.mem_set_image]
  exact (mem_relabel_flow e tail head b lower upper f).symm

private lemma extreme_relabel_flow {V : Type u} {E : Type v} {F : Type*}
    [Fintype E] [Fintype F] (e : F ≃ E) (tail head : E → V)
    (b : V → ℤ) (lower upper : E → ℤ) (f : E → ℝ) :
    relabel e f ∈
        (boundedFlowSet (tail ∘ e) (head ∘ e) b (lower ∘ e) (upper ∘ e)).extremePoints ℝ ↔
      f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ := by
  rw [← image_relabel_flow e tail head b lower upper, ← image_extremePoints]
  exact (relabel e).injective.mem_set_image

private lemma dotProduct_relabel {E : Type v} {F : Type*} [Fintype E] [Fintype F]
    (e : F ≃ E) (c f : E → ℝ) : (c ∘ e) ⬝ᵥ relabel e f = c ⬝ᵥ f :=
  e.sum_comp (fun j => c j * f j)

/-- All flow vertices are integral, with no feasibility or bound-order hypothesis. -/
theorem vertex_integral : Specs.P205.Networks.BoundedFlowIntegrality.vertex_integral.{u, v} := by
  intro V E _ _ tail head b lower upper f hf
  let e := (Fintype.equivFin E).symm
  have hfe := (extreme_relabel_flow e tail head b lower upper f).mpr hf
  have hint := fin_vertex_integral (tail ∘ e) (head ∘ e) b (lower ∘ e) (upper ∘ e)
    (relabel e f) hfe
  intro k
  obtain ⟨j, rfl⟩ := e.surjective k
  exact hint j

/-- Finite bounds ensure an attained integral minimum for every real objective. -/
theorem integral_minimizer :
    Specs.P205.Networks.BoundedFlowIntegrality.integral_minimizer.{u, v} := by
  intro V E _ _ tail head b lower upper c hne
  let e := (Fintype.equivFin E).symm
  have hne' : (boundedFlowSet (tail ∘ e) (head ∘ e) b (lower ∘ e) (upper ∘ e)).Nonempty := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨relabel e f, (mem_relabel_flow e tail head b lower upper f).mpr hf⟩
  obtain ⟨g, hg, _, hopt⟩ := fin_integral_minimizer
    (tail ∘ e) (head ∘ e) b (lower ∘ e) (upper ∘ e) (c ∘ e) hne'
  let f := (relabel e).symm g
  have hfg : relabel e f = g := (relabel e).apply_symm_apply g
  have hf : f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ :=
    (extreme_relabel_flow e tail head b lower upper f).mp (hfg.symm ▸ hg)
  refine ⟨f, hf, vertex_integral tail head b lower upper f hf, ?_⟩
  intro y hy
  have hye := (mem_relabel_flow e tail head b lower upper y).mpr hy
  have h := hopt (relabel e y) hye
  rw [← hfg, dotProduct_relabel, dotProduct_relabel] at h
  exact h

/-- Objective negation supplies an integral maximum as well. -/
theorem integral_maximizer :
    Specs.P205.Networks.BoundedFlowIntegrality.integral_maximizer.{u, v} := by
  intro V E _ _ tail head b lower upper c hne
  obtain ⟨f, hf, hint, hopt⟩ := integral_minimizer tail head b lower upper (-c) hne
  refine ⟨f, hf, hint, ?_⟩
  intro g hg
  simpa only [neg_dotProduct, neg_le_neg_iff] using hopt g hg

end P205.Networks.BoundedFlowIntegrality
