import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionBundleCharts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts
import Mathlib.AlgebraicGeometry.AffineSpace
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Geometric.ConvolutionBundleCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra mapPoints pointsFunctor)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts (affineProbesEquiv hom_ext_on_affines)
open ConvolutionBundleChartsSpecs
open scoped TensorProduct

open private matrixOfPoint_map planeMap_eq_span_of_hom tensorExtensionOfHom from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts

noncomputable section

private abbrev Index := Fin 2 × Fin 1

section Coordinates

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (b : Module.Basis Index ℂ V) {I : Pivot Index 1}
variable (i : Inside I) (k : Outside I) (R : TestAlgebra ℂ) (z : R)

private theorem pivotIndices (I : Pivot Index 1) :
    Nonempty (Inside I) ∧ Nonempty (Outside I) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.property
  have hc : I.valᶜ.card = 1 := by
    rw [Finset.card_compl, I.property]
    decide
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  exact ⟨⟨⟨a, by simp [ha]⟩⟩, ⟨⟨c, by
    rw [← Finset.mem_compl, hc]
    simp⟩⟩⟩

private theorem distinctIndices : k.val ≠ i.val :=
  fun h ↦ k.property (h.symm ▸ i.property)

private theorem indexCases (l : Index) : l = i.val ∨ l = k.val := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.property
  have hc : I.valᶜ.card = 1 := by
    rw [Finset.card_compl, I.property]
    decide
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  by_cases hl : l ∈ I.val
  · left
    have hi := i.property
    simp only [ha, Finset.mem_singleton] at hl hi
    exact hl.trans hi.symm
  · right
    have hl' := Finset.mem_compl.mpr hl
    have hk := Finset.mem_compl.mpr k.property
    simp only [hc, Finset.mem_singleton] at hl' hk
    exact hl'.trans hk.symm

private theorem inside_eq (j : Inside I) : j = i := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.property
  have hj := j.property
  have hi := i.property
  simp only [ha, Finset.mem_singleton] at hj hi
  exact Subtype.ext (hj.trans hi.symm)

/-- The two evaluated basis coordinates determine the vector. -/
private theorem coordinate_ext {x y : Coefficients R V}
    (hi : coordinates b R x i.val = coordinates b R y i.val)
    (hk : coordinates b R x k.val = coordinates b R y k.val) : x = y := by
  apply (coordinates b R).injective
  funext l
  rcases indexCases i k l with h | h
  · simpa only [h] using hi
  · simpa only [h] using hk

private def coord (l : Index) : Coefficients R V →ₗ[R] R :=
  (LinearMap.proj (R := R) (φ := fun _ : Index ↦ R) l).comp (coordinates b R).toLinearMap

private def residual : Coefficients R V →ₗ[R] R :=
  coord b R k.val - z • coord b R i.val

private def quotientCoordinates :
    (Coefficients R V × Coefficients R V) →ₗ[R] Coefficients R V :=
  let A := Coefficients R V
  let first := (coord b R i.val).comp (LinearMap.fst R A A)
  let second := (residual b i k R z).comp (LinearMap.snd R A A)
  (coordinates b R).symm.toLinearMap.comp
    (LinearMap.pi fun l ↦ if l = i.val then first else second)

private theorem quotientCoordinates_i (x : Coefficients R V × Coefficients R V) :
    coordinates b R (quotientCoordinates b i k R z x) i.val = coordinates b R x.1 i.val := by
  simp [quotientCoordinates, coord]

private theorem quotientCoordinates_k (x : Coefficients R V × Coefficients R V) :
    coordinates b R (quotientCoordinates b i k R z x) k.val = residual b i k R z x.2 := by
  simp [quotientCoordinates, distinctIndices i k]

private theorem residual_apply (x : Coefficients R V) :
    residual b i k R z x = coordinates b R x k.val - z * coordinates b R x i.val := rfl

private theorem pivotQuotient_eq (S : Submodule R (Coefficients R V)) :
    pivotQuotient b i k R z S = (quotientCoordinates b i k R z).comp (S.prod ⊤).subtype := by
  rfl

private theorem graph_eq_ker (M : Matrix (Outside I) (Inside I) R) :
    (graphInclusion b I R M).range = (residual b i k R (M k i)).ker := by
  have hentry (v : Inside I → R) : Matrix.toLin' M v k = M k i * v i := by
    classical
    have h : (Finset.univ : Finset (Inside I)) = {i} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun j _ ↦ inside_eq i j⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, h, Finset.sum_singleton]
  have h_i (v : Inside I → R) :
      coordinates b R (graphInclusion b I R M v) i.val = v i := by
    simp [graphInclusion, graphColumns, i.property]
  have h_k (v : Inside I → R) :
      coordinates b R (graphInclusion b I R M v) k.val = M k i * v i := by
    simpa [graphInclusion, graphColumns, k.property] using hentry v
  ext x
  rw [LinearMap.mem_ker, residual_apply, sub_eq_zero]
  constructor
  · rintro ⟨v, rfl⟩
    rw [h_i, h_k]
  · intro hx
    refine ⟨fun _ ↦ coordinates b R x i.val, coordinate_ext b i k R ?_ ?_⟩
    · rw [h_i]
    · rw [h_k, hx]

private def firstResidual :
    (Coefficients R V × Coefficients R V) →ₗ[R] R :=
  (residual b i k R z).comp (LinearMap.fst R _ _)

private theorem ker_firstResidual (S : Submodule R (Coefficients R V))
    (hS : S = (residual b i k R z).ker) :
    (firstResidual b i k R z).ker = S.prod ⊤ := by
  rw [firstResidual, LinearMap.ker_comp, ← hS, Submodule.comap_fst]

private theorem ker_quotientCoordinates_prod (S : Submodule R (Coefficients R V))
    (hS : S = (residual b i k R z).ker) :
    ((quotientCoordinates b i k R z).prod (firstResidual b i k R z)).ker =
      (⊥ : Submodule R (Coefficients R V)).prod S := by
  ext x
  change (quotientCoordinates b i k R z x, residual b i k R z x.1) = (0, 0) ↔
    x.1 ∈ (⊥ : Submodule R (Coefficients R V)) ∧ x.2 ∈ S
  rw [Prod.mk.injEq, hS, Submodule.mem_bot, LinearMap.mem_ker]
  constructor
  · rintro ⟨hq, hx⟩
    have hi := quotientCoordinates_i b i k R z x
    have hk := quotientCoordinates_k b i k R z x
    rw [hq, map_zero, Pi.zero_apply] at hi hk
    refine ⟨coordinate_ext b i k R (by simpa using hi.symm) ?_, hk.symm⟩
    rw [residual_apply, sub_eq_zero, ← hi, mul_zero] at hx
    simpa using hx
  · rintro ⟨hx, hy⟩
    refine ⟨coordinate_ext b i k R ?_ ?_, by simp [hx]⟩
    · simp [quotientCoordinates_i, hx]
    · simp [quotientCoordinates_k, hy]

private theorem quotientCoordinates_prod_surjective :
    Function.Surjective ((quotientCoordinates b i k R z).prod (firstResidual b i k R z)) := by
  rintro ⟨v, t⟩
  let c := coordinates b R
  let a := c v i.val
  let d := c v k.val
  let x := c.symm (fun l ↦ if l = i.val then a else t + z * a)
  let y := c.symm (fun l ↦ if l = i.val then 0 else d)
  have hxi : c x i.val = a := by simp [x]
  have hxk : c x k.val = t + z * a := by simp [x, distinctIndices i k]
  have hyi : c y i.val = 0 := by simp [y]
  have hyk : c y k.val = d := by simp [y, distinctIndices i k]
  refine ⟨(x, y), Prod.ext (coordinate_ext b i k R ?_ ?_) ?_⟩
  · change coordinates b R (quotientCoordinates b i k R z (x, y)) i.val = c v i.val
    rw [quotientCoordinates_i]
    exact hxi
  · change coordinates b R (quotientCoordinates b i k R z (x, y)) k.val = c v k.val
    rw [quotientCoordinates_k, residual_apply]
    change c y k.val - z * c y i.val = d
    rw [hyi, hyk, mul_zero, sub_zero]
  · change residual b i k R z x = t
    rw [residual_apply]
    change c x k.val - z * c x i.val = t
    rw [hxi, hxk, add_sub_cancel_right]

end Coordinates

section GrassmannianComparison

variable {R W A : Type} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup A] [Module R A]
variable (F : W →ₗ[R] A) (r : W →ₗ[R] R)

/-- The incidence plane with fibre line `B` is the kernel of this map. -/
private def lineProjection (B : Submodule R A) : W →ₗ[R] (A ⧸ B) × R :=
  (B.mkQ.comp F).prod r

private theorem mem_lineProjection_ker (B : Submodule R A) (x : W) :
    x ∈ (lineProjection F r B).ker ↔ F x ∈ B ∧ x ∈ r.ker := by
  change (B.mkQ (F x), r x) = (0, 0) ↔ _
  rw [Prod.mk.injEq, LinearMap.mem_ker]
  exact and_congr_left fun _ ↦ Submodule.Quotient.mk_eq_zero B

private theorem lineProjection_surjective (B : Submodule R A)
    (h : Function.Surjective (F.prod r)) : Function.Surjective (lineProjection F r B) := by
  rintro ⟨v, t⟩
  obtain ⟨u, hu⟩ := B.mkQ_surjective v
  obtain ⟨x, hx⟩ := h (u, t)
  have he := Prod.mk.inj hx
  exact ⟨x, Prod.ext ((congrArg B.mkQ he.1).trans hu) he.2⟩

private theorem lineProjection_ker_map {P : Submodule R W}
    (h₁ : (F.prod r).ker ≤ P) (h₂ : P ≤ r.ker) :
    (lineProjection F r (P.map F)).ker = P := by
  ext x
  rw [mem_lineProjection_ker]
  constructor
  · rintro ⟨hx, hr⟩
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hx
    have hxy : x - y ∈ (F.prod r).ker := by
      change (F (x - y), r (x - y)) = (0, 0)
      have hyr : r y = 0 := h₂ hy
      exact Prod.ext (show F (x - y) = 0 by rw [map_sub, he, sub_self])
        (show r (x - y) = 0 by rw [map_sub, show r x = 0 from hr, hyr, sub_zero])
    simpa using P.add_mem (h₁ hxy) hy
  · exact fun hx ↦ ⟨Submodule.mem_map_of_mem hx, h₂ hx⟩

private def planeFromLine (h : Function.Surjective (F.prod r))
    (B : Module.Grassmannian R A 1) : Module.Grassmannian R W 2 := by
  let g := lineProjection F r B.toSubmodule
  let e := g.quotKerEquivOfSurjective (lineProjection_surjective F r _ h)
  letI := B.finite_quotient
  letI := B.projective_quotient
  refine ⟨g.ker, Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, ?_⟩
  intro p
  let : Nontrivial R := p.nontrivial
  have he := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  rw [Module.rankAtStalk_prod, Pi.add_apply, Module.rankAtStalk_self,
    Pi.one_apply, B.rankAtStalk_eq] at he
  exact he

private theorem planeFromLine_submodule (h : Function.Surjective (F.prod r))
    (B : Module.Grassmannian R A 1) :
    (planeFromLine F r h B).toSubmodule = (lineProjection F r B.toSubmodule).ker := rfl

private theorem planeFromLine_bounds (h : Function.Surjective (F.prod r))
    (B : Module.Grassmannian R A 1) :
    (F.prod r).ker ≤ (planeFromLine F r h B).toSubmodule ∧
      (planeFromLine F r h B).toSubmodule ≤ r.ker := by
  rw [planeFromLine_submodule]
  constructor
  · intro x hx
    change (F x, r x) = (0, 0) at hx
    have he := Prod.mk.inj hx
    exact (mem_lineProjection_ker F r _ _).mpr ⟨he.1.symm ▸ B.toSubmodule.zero_mem, he.2⟩
  · exact fun x hx ↦ ((mem_lineProjection_ker F r _ x).mp hx).2

private theorem planeFromLine_map (h : Function.Surjective (F.prod r))
    (B : Module.Grassmannian R A 1) :
    (planeFromLine F r h B).toSubmodule.map F = B.toSubmodule := by
  rw [planeFromLine_submodule]
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ((mem_lineProjection_ker F r _ x).mp hx).1
  · intro hy
    obtain ⟨x, hx⟩ := h (y, 0)
    have he := Prod.mk.inj hx
    exact ⟨x, (mem_lineProjection_ker F r _ x).mpr ⟨he.1.symm ▸ hy, he.2⟩, he.1⟩

private def lineFromPlane (h : Function.Surjective (F.prod r))
    (P : Module.Grassmannian R W 2) (h₁ : (F.prod r).ker ≤ P.toSubmodule) (h₂ : P.toSubmodule ≤ r.ker) :
    Module.Grassmannian R A 1 := by
  let B := P.toSubmodule.map F
  let g := lineProjection F r B
  have hg : g.ker = P.toSubmodule := lineProjection_ker_map F r h₁ h₂
  let e := P.toSubmodule.quotEquivOfEq _ hg.symm ≪≫ₗ
    g.quotKerEquivOfSurjective (lineProjection_surjective F r B h)
  letI := P.finite_quotient
  letI := P.projective_quotient
  letI : Module.Finite R ((A ⧸ B) × R) := Module.Finite.equiv e
  letI : Module.Projective R ((A ⧸ B) × R) := Module.Projective.of_equiv e
  let l := LinearMap.fst R (A ⧸ B) R
  letI : Module.Finite R (A ⧸ B) := Module.Finite.of_surjective l (fun x ↦ ⟨(x, 0), rfl⟩)
  letI : Module.Projective R (A ⧸ B) :=
    Module.Projective.of_split (LinearMap.inl R _ _) l (LinearMap.ext fun _ ↦ rfl)
  refine ⟨B, inferInstance, inferInstance, ?_⟩
  intro p
  let : Nontrivial R := p.nontrivial
  have he := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  change Module.rankAtStalk (W ⧸ P.toSubmodule) p =
    Module.rankAtStalk ((A ⧸ B) × R) p at he
  have hr : Module.rankAtStalk ((A ⧸ B) × R) p = Module.rankAtStalk (A ⧸ B) p + 1 := by
    rw [Module.rankAtStalk_prod, Pi.add_apply, Module.rankAtStalk_self, Pi.one_apply]
  rw [P.rankAtStalk_eq p, hr] at he
  exact Nat.add_right_cancel (show Module.rankAtStalk (A ⧸ B) p + 1 = 1 + 1 from he.symm)

end GrassmannianComparison

section ScalarExtension

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R T : TestAlgebra ℂ} (a : R ⟶ T)

private theorem coordinates_extend (b : Module.Basis Index ℂ V)
    (x : Coefficients R V) (l : Index) :
    coordinates b T (tensorExtensionOfHom a x) l = a.hom (coordinates b R x l) := by
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    change (b.baseChange T).repr (a.hom u ⊗ₜ[ℂ] v) l =
      a.hom ((b.baseChange R).repr (u ⊗ₜ[ℂ] v) l)
    simp [Module.Basis.baseChange_repr_tmul]
  | add u v hu hv => simp [hu, hv]

private abbrev coefficientPairs (R : TestAlgebra ℂ) :
    Coefficients R (V × V) ≃ₗ[R] Coefficients R V × Coefficients R V :=
  TensorProduct.prodRight ℂ R R V V

private theorem pairs_extend (x : Coefficients R (V × V)) :
    coefficientPairs T (tensorExtensionOfHom a x) =
      Prod.map (tensorExtensionOfHom a) (tensorExtensionOfHom a) (coefficientPairs R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul u v => rfl
  | add u v hu hv =>
    simp only [map_add, hu, hv]
    exact Prod.ext (by simp) (by simp)

variable (b : Module.Basis Index ℂ V) {I : Pivot Index 1} (i : Inside I) (k : Outside I)

private theorem quotientCoordinates_extend (z : R) (x : Coefficients R (V × V)) :
    quotientCoordinates b i k T (a.hom z) (coefficientPairs T (tensorExtensionOfHom a x)) =
      tensorExtensionOfHom a (quotientCoordinates b i k R z (coefficientPairs R x)) := by
  apply coordinate_ext b i k T
  · rw [quotientCoordinates_i, coordinates_extend, quotientCoordinates_i, pairs_extend]
    exact coordinates_extend a b _ _
  · rw [quotientCoordinates_k, coordinates_extend, quotientCoordinates_k,
      residual_apply, residual_apply, pairs_extend, map_sub, map_mul]
    change coordinates b T (tensorExtensionOfHom a (coefficientPairs R x).2) k.val -
      a.hom z * coordinates b T (tensorExtensionOfHom a (coefficientPairs R x).2) i.val = _
    rw [coordinates_extend, coordinates_extend]

end ScalarExtension

section AffineComparison

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (b : Module.Basis Index ℂ V)
variable {I : Pivot Index 1} (i : Inside I) (k : Outside I)
variable (R : TestAlgebra ℂ)

include b in
private theorem lineRank : Module.finrank ℂ V - 1 = 1 := by
  rw [Module.finrank_eq_card_basis b]
  decide

include b in
private theorem planeRank : Module.finrank ℂ (V × V) - 2 = 2 := by
  let : Module.Finite ℂ V := Module.Finite.of_basis b
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b]
  decide

private def reindexRank {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {m n : ℕ} (h : m = n) (L : Module.Grassmannian R M m) : Module.Grassmannian R M n :=
  ⟨L.toSubmodule, L.finite_quotient, L.projective_quotient, fun p ↦ (L.rankAtStalk_eq p).trans h⟩

variable (p : Points (chartScheme (k := ℂ) I) R)

private abbrev parameter : R := matrixOfPoint I R p k i

private abbrev fibreMap : Coefficients R (V × V) →ₗ[R] Coefficients R V :=
  (quotientCoordinates b i k R (parameter i k R p)).comp (coefficientPairs R).toLinearMap

private abbrev firstEquation : Coefficients R (V × V) →ₗ[R] R :=
  (firstResidual b i k R (parameter i k R p)).comp (coefficientPairs R).toLinearMap

private theorem fibreMap_surjective :
    Function.Surjective ((fibreMap b i k R p).prod (firstEquation b i k R p)) :=
  (quotientCoordinates_prod_surjective b i k R (parameter i k R p)).comp
    (coefficientPairs R).surjective

variable (C : ChartSystem (k := ℂ) (V := V) b 1)

private abbrev firstLine : Submodule R (Coefficients R V) :=
  (C.affinePoints.hom.app R (p ≫ C.chart I)).toSubmodule

private theorem firstLine_ker :
    firstLine b R p C = (residual b i k R (parameter i k R p)).ker :=
  (C.coordinates_eq I R p).trans (graph_eq_ker b i k R _)

private theorem incidence_bounds (P : Submodule R (Coefficients R (V × V))) :
    ((⊥ : Submodule R (Coefficients R V)).prod (firstLine b R p C) ≤
      P.map (coefficientPairs R).toLinearMap ∧
      P.map (coefficientPairs R).toLinearMap ≤ (firstLine b R p C).prod ⊤) ↔
    ((fibreMap b i k R p).prod (firstEquation b i k R p)).ker ≤ P ∧
      P ≤ (firstEquation b i k R p).ker := by
  let e := coefficientPairs (V := V) R
  have hu := ker_firstResidual b i k R (parameter i k R p)
    (firstLine b R p C) (firstLine_ker b i k R p C)
  have hl := ker_quotientCoordinates_prod b i k R (parameter i k R p)
    (firstLine b R p C) (firstLine_ker b i k R p C)
  have hl' : ((fibreMap b i k R p).prod (firstEquation b i k R p)).ker =
      ((⊥ : Submodule R (Coefficients R V)).prod (firstLine b R p C)).comap e.toLinearMap := by
    rw [← hl, ← LinearMap.ker_comp]
    rfl
  have hu' : (firstEquation b i k R p).ker =
      ((firstLine b R p C).prod ⊤).comap e.toLinearMap := by
    rw [← hu, ← LinearMap.ker_comp]
  rw [hl', hu']
  let L := (⊥ : Submodule R (Coefficients R V)).prod (firstLine b R p C)
  have hL : L ≤ P.map e.toLinearMap ↔ L.comap e.toLinearMap ≤ P := by
    calc
      L ≤ P.map e.toLinearMap ↔ (L.comap e.toLinearMap).map e.toLinearMap ≤ P.map e.toLinearMap := by
        rw [Submodule.map_comap_eq_of_surjective e.surjective]
      _ ↔ L.comap e.toLinearMap ≤ P := by
        rw [Submodule.map_le_iff_le_comap, Submodule.comap_map_eq_of_injective e.injective]
  exact and_congr hL Submodule.map_le_iff_le_comap

private def lineFromTerminal (P : Plane ℂ (V × V) 2 R)
    (h₁ : ((fibreMap b i k R p).prod (firstEquation b i k R p)).ker ≤ P.toSubmodule)
    (h₂ : P.toSubmodule ≤ (firstEquation b i k R p).ker) :
    Plane ℂ V 1 R :=
  reindexRank (lineRank b).symm <|
    lineFromPlane (fibreMap b i k R p) (firstEquation b i k R p) (fibreMap_surjective b i k R p)
      (reindexRank (planeRank b) P) h₁ h₂

private def terminalFromLine (L : Plane ℂ V 1 R) : Plane ℂ (V × V) 2 R :=
  reindexRank (planeRank b).symm <|
    planeFromLine (fibreMap b i k R p) (firstEquation b i k R p) (fibreMap_surjective b i k R p)
      (reindexRank (lineRank b) L)

private theorem terminalFromLine_bounds (L : Plane ℂ V 1 R) :
    ((fibreMap b i k R p).prod (firstEquation b i k R p)).ker ≤
      (terminalFromLine b i k R p L).toSubmodule ∧
    (terminalFromLine b i k R p L).toSubmodule ≤ (firstEquation b i k R p).ker :=
  planeFromLine_bounds _ _ (fibreMap_surjective b i k R p) (reindexRank (lineRank b) L)

private theorem terminalFromLine_map (L : Plane ℂ V 1 R) :
    (terminalFromLine b i k R p L).toSubmodule.map (fibreMap b i k R p) = L.toSubmodule :=
  planeFromLine_map _ _ (fibreMap_surjective b i k R p) (reindexRank (lineRank b) L)

private theorem terminalFromLine_eq (P : Plane ℂ (V × V) 2 R)
    (h₁ : ((fibreMap b i k R p).prod (firstEquation b i k R p)).ker ≤ P.toSubmodule)
    (h₂ : P.toSubmodule ≤ (firstEquation b i k R p).ker)
    (L : Plane ℂ V 1 R) (hL : L.toSubmodule = P.toSubmodule.map (fibreMap b i k R p)) :
    terminalFromLine b i k R p L = P := by
  apply Module.Grassmannian.ext
  change (planeFromLine _ _ (fibreMap_surjective b i k R p) (reindexRank (lineRank b) L)).toSubmodule = _
  rw [planeFromLine_submodule]
  change (lineProjection _ _ L.toSubmodule).ker = _
  rw [hL]
  exact lineProjection_ker_map _ _ h₁ h₂

private theorem fibreMap_natural {T : TestAlgebra ℂ} (a : R ⟶ T)
    (x : Coefficients R (V × V)) :
    fibreMap b i k T (mapPoints a p) (tensorExtensionOfHom a x) =
      tensorExtensionOfHom a (fibreMap b i k R p x) := by
  change quotientCoordinates b i k T (matrixOfPoint I T (mapPoints a p) k i)
      (coefficientPairs T (tensorExtensionOfHom a x)) = _
  rw [matrixOfPoint_map]
  exact quotientCoordinates_extend a b i k (parameter i k R p) x

/-- The spans in the Grassmannian base-change formula allow arbitrary test algebra maps. -/
private theorem fibreMap_plane_natural {T : TestAlgebra ℂ} (a : R ⟶ T)
    (P : Plane ℂ (V × V) 2 R) :
    (Module.Grassmannian.map a.hom P).toSubmodule.map (fibreMap b i k T (mapPoints a p)) =
      Submodule.span T
        (tensorExtensionOfHom a '' (P.toSubmodule.map (fibreMap b i k R p) : Set (Coefficients R V))) := by
  rw [planeMap_eq_span_of_hom, Submodule.map_span]
  congr 1
  rw [Set.image_image, Submodule.map_coe, Set.image_image]
  congr 1
  funext x
  exact fibreMap_natural b i k R p a x

end AffineComparison

section SchemeComparison

variable {V : Type} [AddCommGroup V] [Module ℂ V] {κ : Type} [Fintype κ] [DecidableEq κ]
variable {b : Module.Basis Index ℂ V} {b₂ : Module.Basis κ ℂ (V × V)}
variable (C : ChartSystem (k := ℂ) (V := V) b 1)
variable (D : ChartSystem (k := ℂ) (V := V × V) b₂ 2)
variable {X : SchemeOver ℂ} (j : X ⟶ C.scheme ⨯ D.scheme)
variable {I : Pivot Index 1} (i : Inside I) (k : Outside I)

private abbrev firstProjection := j ≫ (prod.fst : C.scheme ⨯ D.scheme ⟶ C.scheme)

private abbrev chartPullback (I : Pivot Index 1) := pullback (firstProjection C D j) (C.chart I)

private abbrev chartProduct (I : Pivot Index 1) := chartScheme (k := ℂ) I ⨯ C.scheme

private abbrev chartBase (I : Pivot Index 1) :
    chartPullback C D j I ⟶ chartScheme (k := ℂ) I :=
  pullback.snd (firstProjection C D j) (C.chart I)

private abbrev chartInclusion (I : Pivot Index 1) : chartPullback C D j I ⟶ X :=
  pullback.fst (firstProjection C D j) (C.chart I)

private abbrev terminalProjection (I : Pivot Index 1) : chartPullback C D j I ⟶ D.scheme :=
  chartInclusion C D j I ≫ j ≫ prod.snd

private theorem chartPoint_bounds (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) :
    let p := q ≫ chartBase C D j I
    let P := (D.affinePoints.hom.app R (q ≫ terminalProjection C D j I)).toSubmodule
    ((fibreMap b i k R p).prod (firstEquation b i k R p)).ker ≤ P ∧
      P ≤ (firstEquation b i k R p).ker := by
  let u := q ≫ chartInclusion C D j I
  have hb := (H R (u ≫ j)).mp ⟨u, rfl⟩
  dsimp only [terminalPlane] at hb
  have he : (u ≫ j) ≫ prod.fst = (q ≫ chartBase C D j I) ≫ C.chart I := by
    simp only [u, Category.assoc, ← pullback.condition]
  rw [he] at hb
  exact (incidence_bounds b i k R (q ≫ chartBase C D j I) C _).mp hb

private def chartPointLine (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) : Plane ℂ V 1 R :=
  lineFromTerminal b i k R (q ≫ chartBase C D j I)
    (D.affinePoints.hom.app R (q ≫ terminalProjection C D j I))
    (chartPoint_bounds C D j i k H R q).1 (chartPoint_bounds C D j i k H R q).2

private theorem chartPointLine_submodule (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) :
    (chartPointLine C D j i k H R q).toSubmodule =
      (D.affinePoints.hom.app R (q ≫ terminalProjection C D j I)).toSubmodule.map
        (fibreMap b i k R (q ≫ chartBase C D j I)) := rfl

private theorem affinePlane_natural {U σ : Type} [AddCommGroup U] [Module ℂ U]
    [Fintype σ] [DecidableEq σ] {c : Module.Basis σ ℂ U} {d : ℕ}
    (E : ChartSystem (k := ℂ) (V := U) c d)
    {R T : TestAlgebra ℂ} (a : R ⟶ T) (p : Points E.scheme R) :
    E.affinePoints.hom.app T (mapPoints a p) =
      Module.Grassmannian.map a.hom (E.affinePoints.hom.app R p) :=
  ConcreteCategory.congr_hom (E.affinePoints.hom.naturality a) p

private theorem chartPointLine_natural (H : AffineIncidence C D j)
    {R T : TestAlgebra ℂ} (a : R ⟶ T) (q : Points (chartPullback C D j I) R) :
    chartPointLine C D j i k H T (mapPoints a q) =
      Module.Grassmannian.map a.hom (chartPointLine C D j i k H R q) := by
  apply Module.Grassmannian.ext
  rw [chartPointLine_submodule, planeMap_eq_span_of_hom, chartPointLine_submodule]
  have hb : mapPoints a q ≫ chartBase C D j I = mapPoints a (q ≫ chartBase C D j I) :=
    Category.assoc _ _ _
  have ht : mapPoints a q ≫ terminalProjection C D j I =
      mapPoints a (q ≫ terminalProjection C D j I) := Category.assoc _ _ _
  rw [hb, ht, affinePlane_natural]
  exact fibreMap_plane_natural b i k R _ a _

private def chartPointMap (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) : Points (chartProduct C I) R :=
  prod.lift (q ≫ chartBase C D j I)
    (C.affinePoints.inv.app R (chartPointLine C D j i k H R q))

private theorem chartPointMap_fst (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) :
    chartPointMap C D j i k H R q ≫ prod.fst = q ≫ chartBase C D j I := prod.lift_fst _ _

private theorem chartPointMap_snd (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) :
    chartPointMap C D j i k H R q ≫ prod.snd =
      C.affinePoints.inv.app R (chartPointLine C D j i k H R q) := prod.lift_snd _ _

private theorem chartPointMap_line (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) :
    C.affinePoints.hom.app R (chartPointMap C D j i k H R q ≫ prod.snd) =
      chartPointLine C D j i k H R q := by
  rw [chartPointMap_snd]
  exact ConcreteCategory.congr_hom (C.affinePoints.inv_hom_id_app R) _

private theorem chartPointMap_natural (H : AffineIncidence C D j)
    {R T : TestAlgebra ℂ} (a : R ⟶ T) (q : Points (chartPullback C D j I) R) :
    chartPointMap C D j i k H T (mapPoints a q) = mapPoints a (chartPointMap C D j i k H R q) := by
  apply prod.hom_ext
  · simp only [mapPoints, Category.assoc, chartPointMap_fst]
  · have h : mapPoints a (chartPointMap C D j i k H R q) ≫ prod.snd =
        mapPoints a (chartPointMap C D j i k H R q ≫ prod.snd) := Category.assoc _ _ _
    rw [h]
    apply (ConcreteCategory.bijective_of_isIso (C.affinePoints.hom.app T)).1
    rw [affinePlane_natural, chartPointMap_line, chartPointMap_line, chartPointLine_natural]

private theorem chartPointMap_injective (H : AffineIncidence C D j) [Mono j] (R : TestAlgebra ℂ) :
    Function.Injective (chartPointMap C D j i k H R) := by
  intro q q' h
  have hb : q ≫ chartBase C D j I = q' ≫ chartBase C D j I := by
    simpa only [chartPointMap_fst] using congrArg (· ≫ prod.fst) h
  have hl : chartPointLine C D j i k H R q = chartPointLine C D j i k H R q' := by
    rw [← chartPointMap_line C D j i k H R q, ← chartPointMap_line C D j i k H R q', h]
  have hterminal (v : Points (chartPullback C D j I) R) :
      terminalFromLine b i k R (v ≫ chartBase C D j I) (chartPointLine C D j i k H R v) =
        D.affinePoints.hom.app R (v ≫ terminalProjection C D j I) :=
    terminalFromLine_eq b i k R _ _ (chartPoint_bounds C D j i k H R v).1
      (chartPoint_bounds C D j i k H R v).2 _ (chartPointLine_submodule C D j i k H R v)
  have hp : q ≫ terminalProjection C D j I = q' ≫ terminalProjection C D j I := by
    apply (ConcreteCategory.bijective_of_isIso (D.affinePoints.hom.app R)).1
    rw [← hterminal q, ← hterminal q', hb, hl]
  refine pullback.hom_ext ?_ hb
  apply (cancel_mono j).mp
  apply prod.hom_ext
  · simpa only [Category.assoc, ← pullback.condition] using
      congrArg (· ≫ C.chart I) hb
  · simpa only [terminalProjection, Category.assoc] using hp

private theorem chartPointMap_surjective (H : AffineIncidence C D j) (R : TestAlgebra ℂ) :
    Function.Surjective (chartPointMap C D j i k H R) := by
  intro v
  let p := v ≫ prod.fst
  let L := C.affinePoints.hom.app R (v ≫ prod.snd)
  let P := terminalFromLine b i k R p L
  let t := D.affinePoints.inv.app R P
  have ht : D.affinePoints.hom.app R t = P :=
    ConcreteCategory.congr_hom (D.affinePoints.inv_hom_id_app R) _
  let a := prod.lift (p ≫ C.chart I) t
  have ha₁ : a ≫ prod.fst = p ≫ C.chart I := prod.lift_fst _ _
  have ha₂ : a ≫ prod.snd = t := prod.lift_snd _ _
  have hi := (incidence_bounds b i k R p C P.toSubmodule).mpr
    (terminalFromLine_bounds b i k R p L)
  obtain ⟨x, hx⟩ := (H R a).mpr (by
    dsimp only [terminalPlane]
    rw [ha₁, ha₂, ht]
    exact hi)
  have he : x ≫ firstProjection C D j = p ≫ C.chart I := by
    rw [← ha₁, ← hx, Category.assoc]
  let q : Points (chartPullback C D j I) R := pullback.lift x p he
  have hq₁ : q ≫ chartBase C D j I = p := pullback.lift_snd _ _ _
  have hq₂ : q ≫ terminalProjection C D j I = t := by
    dsimp only [terminalProjection]
    rw [← Category.assoc, ← Category.assoc, show q ≫ chartInclusion C D j I = x from
      pullback.lift_fst _ _ _, hx, ha₂]
  refine ⟨q, prod.hom_ext ?_ ?_⟩
  · rw [chartPointMap_fst, hq₁]
  · apply (ConcreteCategory.bijective_of_isIso (C.affinePoints.hom.app R)).1
    rw [chartPointMap_line]
    apply Module.Grassmannian.ext
    rw [chartPointLine_submodule, hq₁, hq₂, ht]
    exact terminalFromLine_map b i k R p L

set_option backward.isDefEq.respectTransparency false in
private theorem isoOfAffinePointMap {Y Z : SchemeOver ℂ} (F : pointsFunctor Y ⟶ pointsFunctor Z)
    (hF : ∀ R, Function.Bijective (F.app R)) :
    ∃ e : Y ≅ Z, ∀ (R : TestAlgebra ℂ) (q : Points Y R), q ≫ e.hom = F.app R q := by
  let h : Y ⟶ Z := (affineProbesEquiv Y Z).symm F
  have hh (R : TestAlgebra ℂ) (q : Points Y R) : q ≫ h = F.app R q :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app ((affineProbesEquiv Y Z).apply_symm_apply F) R) q
  let : IsIso F := (NatTrans.isIso_iff_isIso_app F).mpr fun R ↦ (CategoryTheory.isIso_iff_bijective _).mpr (hF R)
  let g : Z ⟶ Y := (affineProbesEquiv Z Y).symm (inv F)
  have hg (R : TestAlgebra ℂ) (q : Points Z R) : q ≫ g = (inv F).app R q :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app ((affineProbesEquiv Z Y).apply_symm_apply (inv F)) R) q
  refine ⟨⟨h, g, ?_, ?_⟩, hh⟩
  · apply hom_ext_on_affines
    intro R q
    calc
      q ≫ (h ≫ g) = (F.app R q) ≫ g := (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (hh R q))
      _ = (inv F).app R (F.app R q) := hg R _
      _ = q := ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.hom_inv_id F) R) q
      _ = q ≫ 𝟙 Y := (Category.comp_id _).symm
  · apply hom_ext_on_affines
    intro R q
    calc
      q ≫ (g ≫ h) = ((inv F).app R q) ≫ h := (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ h) (hg R q))
      _ = F.app R ((inv F).app R q) := hh R _
      _ = q := ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.inv_hom_id F) R) q
      _ = q ≫ 𝟙 Z := (Category.comp_id _).symm

private theorem chartIso (H : AffineIncidence C D j) [Mono j] :
    ∃ e : chartPullback C D j I ≅ chartProduct C I,
      e.hom ≫ prod.fst = chartBase C D j I ∧
      ∀ (R : TestAlgebra ℂ) (q : Points (chartPullback C D j I) R),
        C.affinePoints.hom.app R (q ≫ e.hom ≫ prod.snd) = chartPointLine C D j i k H R q := by
  let α : pointsFunctor (chartPullback C D j I) ⟶ pointsFunctor (chartProduct C I) :=
    { app := fun R ↦ ↾chartPointMap C D j i k H R
      naturality := by
        intro R T a
        apply ConcreteCategory.hom_ext
        intro q
        exact chartPointMap_natural C D j i k H a q }
  obtain ⟨e, he⟩ := isoOfAffinePointMap α (fun R ↦
    ⟨chartPointMap_injective C D j i k H R, chartPointMap_surjective C D j i k H R⟩)
  refine ⟨e, ?_, fun R q ↦ ?_⟩
  · apply hom_ext_on_affines
    intro R q
    rw [← Category.assoc, he]
    exact chartPointMap_fst C D j i k H R q
  · rw [← Category.assoc, he]
    exact chartPointMap_line C D j i k H R q

private theorem pivotQuotient_surjective_ker (R : TestAlgebra ℂ)
    (p : Points (chartScheme (k := ℂ) I) R) :
    let S := firstLine b R p C
    let Q := pivotQuotient b i k R (parameter i k R p) S
    Function.Surjective Q ∧
      Q.ker = ((⊥ : Submodule R (Coefficients R V)).prod S).comap (S.prod ⊤).subtype := by
  let S := firstLine b R p C
  let z := parameter i k R p
  have hs : S = (residual b i k R z).ker := firstLine_ker b i k R p C
  have hu := ker_firstResidual b i k R z S hs
  have hv := ker_quotientCoordinates_prod b i k R z S hs
  dsimp only
  change Function.Surjective (pivotQuotient b i k R z S) ∧ _
  rw [pivotQuotient_eq]
  constructor
  · intro v
    obtain ⟨x, hx⟩ := quotientCoordinates_prod_surjective b i k R z (v, 0)
    have he := Prod.mk.inj hx
    have hm : x ∈ S.prod ⊤ := hu ▸ (show x ∈ (firstResidual b i k R z).ker from he.2)
    exact ⟨⟨x, hm⟩, he.1⟩
  · rw [LinearMap.ker_comp, ← hv]
    ext x
    change quotientCoordinates b i k R z x.val = 0 ↔
      (quotientCoordinates b i k R z x.val, firstResidual b i k R z x.val) = (0, 0)
    rw [Prod.mk.injEq]
    have hr : firstResidual b i k R z x.val = 0 := show x.val ∈ (firstResidual b i k R z).ker from
      hu.symm ▸ x.property
    simp only [hr, and_true]

private theorem pivotQuotient_image (H : AffineIncidence C D j) (R : TestAlgebra ℂ)
    (q : Points (chartPullback C D j I) R) :
    let p := q ≫ chartBase C D j I
    let S := firstLine b R p C
    let P := terminalPlane D R (q ≫ terminalProjection C D j I)
    let Q := pivotQuotient b i k R (parameter i k R p) S
    (chartPointLine C D j i k H R q).toSubmodule = (P.comap (S.prod ⊤).subtype).map Q := by
  let p := q ≫ chartBase C D j I
  let S := firstLine b R p C
  let P := terminalPlane D R (q ≫ terminalProjection C D j I)
  have hP : P ≤ S.prod ⊤ :=
    ((incidence_bounds b i k R p C _).mpr (chartPoint_bounds C D j i k H R q)).2
  dsimp only
  rw [chartPointLine_submodule, Submodule.map_comp (coefficientPairs R).toLinearMap]
  let F := quotientCoordinates b i k R (parameter i k R p)
  have hmap : (P.comap (S.prod ⊤).subtype).map (S.prod ⊤).subtype = P := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hP]
  change P.map F = (P.comap (S.prod ⊤).subtype).map (pivotQuotient b i k R (parameter i k R p) S)
  rw [pivotQuotient_eq, Submodule.map_comp _ F, hmap]

end SchemeComparison

section Geometry

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Module.Basis Index ℂ V}
variable (C : ChartSystem (k := ℂ) (V := V) b 1)

private def pivotCover : C.scheme.left.OpenCover :=
  Scheme.Cover.mkOfCovers (Pivot Index 1) (fun I ↦ (chartScheme (k := ℂ) I).left)
    (fun I ↦ (C.chart I).left) C.cover C.openChart

private theorem smooth_chart (I : Pivot Index 1) : Smooth (chartScheme (k := ℂ) I).hom := by
  let n := Outside I × Inside I
  let B := CommRingCat.of ℂ
  let e := AffineSpace.SpecIso n B
  have he : e.inv ≫ (𝔸(n; Spec B) ↘ Spec B) = (chartScheme (k := ℂ) I).hom :=
    AffineSpace.SpecIso_inv_over (n := n) B
  exact he ▸ (inferInstance : Smooth (e.inv ≫ (𝔸(n; Spec B) ↘ Spec B)))

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_lines : Smooth C.scheme.hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (pivotCover C)
  intro I
  change Smooth ((C.chart I).left ≫ C.scheme.hom)
  rw [Over.w]
  exact smooth_chart I

private theorem reduced_lines : IsReduced C.scheme.left := by
  apply (IsReduced.iff_of_openCover _ (pivotCover C)).mpr
  intro I
  change IsReduced (Spec (CommRingCat.of (MvPolynomial (Outside I × Inside I) ℂ)))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem chartProduct_geometry (I : Pivot Index 1) :
    Smooth (chartProduct C I).hom ∧ IsReduced (chartProduct C I).left := by
  let n := Outside I × Inside I
  let K := CommRingCat.of ℂ
  let B := Spec K
  let e := AffineSpace.SpecIso n K
  let f := C.scheme.hom
  have hg : e.inv ≫ (𝔸(n; B) ↘ B) = (chartScheme (k := ℂ) I).hom :=
    AffineSpace.SpecIso_inv_over (n := n) K
  let h := AffineSpace.isPullback_map (n := n) f
  have h' : IsPullback (AffineSpace.map n f ≫ e.hom) (𝔸(n; C.scheme.left) ↘ C.scheme.left)
      (chartScheme (k := ℂ) I).hom f := by
    apply h.of_iso' (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simp [e]
    · simp
    · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using hg
    · simp
  let hp := Over.isPullback_of_binaryFan_isLimit _
    (prodIsProd (chartScheme (k := ℂ) I) C.scheme)
  let E := hp.isoIsPullback _ _ h'
  have hE : E.hom ≫ (𝔸(n; C.scheme.left) ↘ C.scheme.left) =
      (prod.snd : chartProduct C I ⟶ C.scheme).left := hp.isoIsPullback_hom_snd _ _ h'
  have hhom : (chartProduct C I).hom =
      E.hom ≫ (𝔸(n; C.scheme.left) ↘ C.scheme.left) ≫ C.scheme.hom := by
    rw [← Category.assoc, hE, Over.w]
  let : Smooth C.scheme.hom := smooth_lines C
  let : IsReduced C.scheme.left := reduced_lines C
  exact ⟨hhom.symm ▸ inferInstance, isReduced_of_isOpenImmersion E.hom⟩

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {b₂ : Module.Basis κ ℂ (V × V)}
variable (D : ChartSystem (k := ℂ) (V := V × V) b₂ 2)
variable {X : SchemeOver ℂ} (j : X ⟶ C.scheme ⨯ D.scheme)

set_option backward.isDefEq.respectTransparency false in
private theorem incidence_geometry
    (h : ∀ I : Pivot Index 1, Nonempty (chartPullback C D j I ≅ chartProduct C I)) :
    Smooth X.hom ∧ IsReduced X.left := by
  let U := (pivotCover C).pullback₁ (firstProjection C D j).left
  have ht (I : Pivot Index 1) :
      Smooth (U.f I ≫ X.hom) ∧ IsReduced (U.X I) := by
    obtain ⟨e⟩ := h I
    let e₁ := (Over.forget (Spec (CommRingCat.of ℂ))).mapIso e
    let e₂ : (chartPullback C D j I).left ≅ U.X I :=
      PreservesPullback.iso (Over.forget (Spec (CommRingCat.of ℂ)))
        (firstProjection C D j) (C.chart I)
    have he₂ : e₂.inv ≫ (chartInclusion C D j I).left = U.f I :=
      PreservesPullback.iso_inv_fst _ _ _
    let : Smooth (chartProduct C I).hom := (chartProduct_geometry C I).1
    let : IsReduced ((Over.forget (Spec (CommRingCat.of ℂ))).obj (chartProduct C I)) :=
      (chartProduct_geometry C I).2
    have he : U.f I ≫ X.hom = e₂.inv ≫ e₁.hom ≫ (chartProduct C I).hom := by
      rw [← he₂, Category.assoc, Over.w, ← Over.w e.hom]
      rfl
    exact ⟨he.symm ▸ inferInstance, isReduced_of_isOpenImmersion (e₂.inv ≫ e₁.hom)⟩
  exact ⟨IsZariskiLocalAtSource.of_openCover (P := @Smooth) U (fun I ↦ (ht I).1),
    (IsReduced.iff_of_openCover _ U).2 (fun I ↦ (ht I).2)⟩

end Geometry

/-- The first lattice projection is locally the product with the line Grassmannian. -/
theorem bundleCharts : BundleCharts := by
  intro V _ _ κ _ _ b b₂ C D X j hj H
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  have charts (I : Pivot Index 1) :
      ∃ e : chartPullback C D j I ≅ chartProduct C I,
        e.hom ≫ prod.fst = chartBase C D j I ∧
        ∀ (R : TestAlgebra ℂ) (q : Points (chartPullback C D j I) R)
          (i : Inside I) (k : Outside I),
          let p := q ≫ chartBase C D j I
          let S := firstLine b R p C
          let P := terminalPlane D R (q ≫ terminalProjection C D j I)
          let L := (C.affinePoints.hom.app R (q ≫ e.hom ≫ prod.snd)).toSubmodule
          let Q := pivotQuotient b i k R (parameter i k R p) S
          Function.Surjective Q ∧
            Q.ker = ((⊥ : Submodule R (Coefficients R V)).prod S).comap (S.prod ⊤).subtype ∧
            L = (P.comap (S.prod ⊤).subtype).map Q := by
    obtain ⟨⟨i⟩, ⟨k⟩⟩ := pivotIndices I
    obtain ⟨e, he, hL⟩ := chartIso C D j i k H
    refine ⟨e, he, fun R q i' k' ↦ ?_⟩
    have hi : i' = i := inside_eq i i'
    have hk : k' = k := by
      rcases indexCases i k k'.val with h | h
      · exact (k'.property (h.symm ▸ i.property)).elim
      · exact Subtype.ext h
    subst i'
    subst k'
    have hQ := pivotQuotient_surjective_ker C i k R (q ≫ chartBase C D j I)
    dsimp only at hQ ⊢
    exact ⟨hQ.1, hQ.2, (congrArg Module.Grassmannian.toSubmodule (hL R q)).trans
      (pivotQuotient_image C D j i k H R q)⟩
  exact ⟨charts, incidence_geometry C D j (fun I ↦ ⟨(charts I).choose⟩)⟩

end

end RepTheorySurvey.Geometric.ConvolutionBundleCharts
