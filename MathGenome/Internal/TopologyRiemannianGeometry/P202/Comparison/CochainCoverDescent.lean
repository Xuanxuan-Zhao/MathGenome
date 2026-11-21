import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.CochainCoverDescent
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Comparison.SmoothSingularComparison
/-! Conditional implementation of `paper.tex:2748–2813`. All conditional helpers
take the full prescribed smooth-singular comparison premise. No closed
original target, fake upstream theorem, or certificate is introduced. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace P202.CochainCoverDescent
open P202Specs.CochainCoverDescent
universe u v

@[simp] theorem fullSimplexD_zero (I : Type v) (f : FullSimplexRow I 0)
    (t : Fin 1 → I) : fullSimplexD I 0 f t = f Fin.elim0 := rfl

@[simp] theorem fullSimplexD_cons (I : Type v) (k : ℕ)
    (f : FullSimplexRow I (k+1)) (i : I) (t : Fin (k+1) → I) :
    fullSimplexD I (k+1) f (Fin.cons i t) =
      f t - fullSimplexD I k (fun s => f (Fin.cons i s)) t := by
  simp [fullSimplexD, Fin.tail_cons]

/-- Inserting a fixed vertex contracts the augmented full-simplex row. -/
theorem fullSimplex_contraction (I : Type v) (i : I) (k : ℕ)
    (f : FullSimplexRow I (k+1)) :
    fullSimplexD I k (fullSimplexH i k f) +
      fullSimplexH i (k+1) (fullSimplexD I (k+1) f) = f := by
  funext t
  change fullSimplexD I k (fun s => f (Fin.cons i s)) t +
    fullSimplexD I (k+1) f (Fin.cons i t) = f t
  rw [fullSimplexD_cons]
  ring

theorem fullSimplex_square (I : Type v) (k : ℕ) (f : FullSimplexRow I k) :
    fullSimplexD I (k+1) (fullSimplexD I k f) = 0 := by
  induction k with
  | zero =>
    funext t
    simp [fullSimplexD]
  | succ k ih =>
    funext t
    have ht : t = Fin.cons (t 0) (Fin.tail t) := (Fin.cons_self_tail t).symm
    rw [ht, fullSimplexD_cons]
    have heq : (fun s => fullSimplexD I (k+1) f (Fin.cons (t 0) s)) =
        f - fullSimplexD I k (fun s => f (Fin.cons (t 0) s)) := by
      funext s
      exact fullSimplexD_cons I k f (t 0) s
    rw [heq, map_sub, ih]
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
    simp

/-- The recursive map is exactly the alternating sum of restrictions. -/
theorem fullSimplexD_alternating (I : Type v) (k : ℕ)
    (f : FullSimplexRow I k) (t : Fin (k+1) → I) :
    fullSimplexD I k f t =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val * f (t ∘ j.succAbove) := by
  induction k with
  | zero =>
    rw [Fin.sum_univ_succ]
    simp only [fullSimplexD_zero, Fin.sum_univ_zero, add_zero, Fin.val_zero,
      pow_zero, one_mul]
    exact congrArg f (Subsingleton.elim _ _)
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
      Fin.val_succ, pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib]
    change f (Fin.tail t) -
      fullSimplexD I k (fun s => f (Fin.cons (t 0) s)) (Fin.tail t) = _
    rw [ih]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [Function.comp_def]
    · simp [Function.comp_def, Fin.tail]

/-- Exactness is coordinatewise; choosing primitives does not bound the
number of coordinates or the dimension of any cohomology space. -/
theorem productRows_exact {B : Type u} (I : B → Type v)
    (hne : ∀ b, Nonempty (I b)) :
    Function.Injective (productD I 0) ∧
    ∀ k (f : ProductRow I (k+1)),
      productD I (k+1) f = 0 ↔ ∃ g, productD I k g = f := by
  classical
  let vertex : (b : B) → I b := fun b => Classical.choice (hne b)
  constructor
  · intro f g hfg
    funext b t
    have h := congrFun (congrFun hfg b) (fun _ => vertex b)
    change f b Fin.elim0 = g b Fin.elim0 at h
    simpa only [show t = Fin.elim0 from Subsingleton.elim _ _] using h
  · intro k f
    constructor
    · intro hf
      refine ⟨fun b => fullSimplexH (vertex b) k (f b), ?_⟩
      funext b t
      have hb : fullSimplexD (I b) (k+1) (f b) = 0 := congrFun hf b
      have hc := congrFun (fullSimplex_contraction (I b) (vertex b) k (f b)) t
      rw [hb, map_zero] at hc
      change fullSimplexD (I b) k (fullSimplexH (vertex b) k (f b)) t = f b t
      simpa only [Pi.add_apply, Pi.zero_apply, add_zero] using hc
    · rintro ⟨g, rfl⟩
      funext b
      exact fullSimplex_square (I b) k (g b)

theorem alternatingFormula_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{v}) :
    alternatingFormula_type.{v} := fullSimplexD_alternating

theorem productRowsExact_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    productRowsExact_type.{u,v} := by
  intro B I hne
  exact productRows_exact I hne

theorem evaluatedCochainRowsExact_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    evaluatedCochainRowsExact_type.{u,v} := by
  intro n a M _ S ι U q
  apply productRows_exact
  intro σ
  obtain ⟨i, hi⟩ := σ.property.2
  exact ⟨⟨i, hi⟩⟩


section GeometricRows
open SmoothManifolds SmoothManifolds.AtlasData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ)

@[simp] theorem cochainRowEquiv_apply (k : ℕ)
    (f : IntersectionCochainRow S U q k) (σ : SmallSmoothSimplex S U q)
    (t : Fin k → ContainingIndex σ) :
    cochainRowEquiv S U q k f σ t =
      f (fun j => (t j).val) (Finsupp.single ⟨σ, fun j => (t j).property⟩ 1) := rfl

@[simp] theorem intersectionD_evaluation (k : ℕ)
    (f : IntersectionCochainRow S U q k) :
    cochainRowEquiv S U q (k+1) (intersectionD S U q k f) =
      productD (fun σ : SmallSmoothSimplex S U q => ContainingIndex σ) k
        (cochainRowEquiv S U q k f) := by
  simp only [intersectionD, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem intersectionD_alternating (k : ℕ) (f : IntersectionCochainRow S U q k)
    (t : Fin (k+1) → ι) (σ : IntersectionSimplex S U q (k+1) t) :
    intersectionD S U q k f t (Finsupp.single σ 1) =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val *
        f (t ∘ j.succAbove) (Finsupp.single (deleteIndex S U q σ j) 1) := by
  let vertices : Fin (k+1) → ContainingIndex σ.val :=
    fun j => ⟨t j, σ.property j⟩
  have h := congrFun (congrFun (intersectionD_evaluation S U q k f) σ.val) vertices
  change intersectionD S U q k f t (Finsupp.single σ 1) =
    fullSimplexD (ContainingIndex σ.val) k (cochainRowEquiv S U q k f σ.val) vertices at h
  rw [h, fullSimplexD_alternating]
  rfl

theorem intersectionD_square (k : ℕ) (f : IntersectionCochainRow S U q k) :
    intersectionD S U q (k+1) (intersectionD S U q k f) = 0 := by
  apply (cochainRowEquiv S U q (k+2)).injective
  rw [intersectionD_evaluation, intersectionD_evaluation, map_zero]
  funext σ
  exact fullSimplex_square (ContainingIndex σ) k _

theorem intersectionRows_exact :
    Function.Injective (intersectionD S U q 0) ∧
    (∀ k (f : IntersectionCochainRow S U q k),
      intersectionD S U q (k+1) (intersectionD S U q k f) = 0) ∧
    ∀ k (f : IntersectionCochainRow S U q (k+1)),
      intersectionD S U q (k+1) f = 0 ↔ ∃ g, intersectionD S U q k g = f := by
  have hne : ∀ σ : SmallSmoothSimplex S U q, Nonempty (ContainingIndex σ) := by
    intro σ
    obtain ⟨i, hi⟩ := σ.property.2
    exact ⟨⟨i, hi⟩⟩
  obtain ⟨hinj, hexact⟩ := productRows_exact _ hne
  refine ⟨?_, intersectionD_square S U q, ?_⟩
  · intro f g hfg
    apply (cochainRowEquiv S U q 0).injective
    apply hinj
    simpa only [← intersectionD_evaluation] using
      congrArg (cochainRowEquiv S U q 1) hfg
  · intro k f
    constructor
    · intro hf
      have hf' : productD (fun σ : SmallSmoothSimplex S U q => ContainingIndex σ)
          (k+1) (cochainRowEquiv S U q (k+1) f) = 0 := by
        rw [← intersectionD_evaluation, hf, map_zero]
      obtain ⟨g, hg⟩ := (hexact k _).mp hf'
      refine ⟨(cochainRowEquiv S U q k).symm g, ?_⟩
      apply (cochainRowEquiv S U q (k+1)).injective
      rw [intersectionD_evaluation, LinearEquiv.apply_symm_apply]
      exact hg
    · rintro ⟨g, rfl⟩
      exact intersectionD_square S U q k g
end GeometricRows

theorem intersectionAlternatingFormula_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    intersectionAlternatingFormula_type.{u,v} := by
  intro n a M _ S ι U q k f t σ
  exact intersectionD_alternating S U q k f t σ

theorem intersectionRowsExact_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    intersectionRowsExact_type.{u,v} := by
  intro n a M _ S ι U q
  exact intersectionRows_exact S U q

theorem productsPreserveExactness_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    productsPreserveExactness_type.{u,v} := by
  classical
  intro B V W Z _ _ _ _ _ _ f g hexact w
  constructor
  · intro hw
    have hv : ∀ b, ∃ v, f b v = w b :=
      fun b => (hexact b (w b)).mp (congrFun hw b)
    choose v hv using hv
    exact ⟨v, funext hv⟩
  · rintro ⟨v, hv⟩
    funext b
    exact (hexact b (w b)).mpr ⟨v b, congrFun hv b⟩


/-- Finite elimination along a decreasing filtration. This is the algebraic
lifting step for total-complex arguments: exactness on each successive
quotient supplies the next correction, and a finite filtration ends it.
There is no finite-dimensionality hypothesis on any of the modules. -/
theorem finiteFiltration_exact
    {E W Z : Type v} [AddCommGroup E] [AddCommGroup W] [AddCommGroup Z]
    [Module ℝ E] [Module ℝ W] [Module ℝ Z]
    (f : E →ₗ[ℝ] W) (g : W →ₗ[ℝ] Z) (hgf : g.comp f = 0)
    (F : ℕ → Submodule ℝ W) (hstart : F 0 = ⊤) (N : ℕ) (hend : F N = ⊥)
    (hlift : ∀ p x, x ∈ F p → g x = 0 → ∃ y, x - f y ∈ F (p+1)) :
    ∀ x, g x = 0 → ∃ y, f y = x := by
  intro x hx
  have hzero (y : E) : g (f y) = 0 := LinearMap.congr_fun hgf y
  have hstep : ∀ p, ∃ y, x - f y ∈ F p := by
    intro p
    induction p with
    | zero => exact ⟨0, by rw [hstart]; trivial⟩
    | succ p ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hlift p (x-f y) hy (by rw [map_sub, hx, hzero, sub_self])
      refine ⟨y+z, ?_⟩
      convert hz using 1
      simp only [map_add]
      abel
  obtain ⟨y, hy⟩ := hstep N
  rw [hend] at hy
  exact ⟨y, (sub_eq_zero.mp hy).symm⟩

section VerticalDifferential
open SmoothManifolds SmoothManifolds.AtlasData
open P202Specs.SingularChains
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

theorem intersectionBoundary_square (q k : ℕ) (t : Fin k → ι)
    (z : intersectionChainModule S U (q+2) k t) :
    intersectionBoundary S U q k t (intersectionBoundary S U (q+1) k t z) = 0 := by
  apply Subtype.ext
  exact congrArg (fun f => f z.val)
    ((complex ℝ ℝ (TopCat.of M)).d_comp_d (q+2) (q+1) q)

theorem intersectionV_square (q k : ℕ) (f : IntersectionCochainRow S U q k) :
    intersectionV S U (q+1) k (intersectionV S U q k f) = 0 := by
  ext t z
  simp only [intersectionV, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, intersectionBoundary_square, map_zero,
    LinearMap.zero_apply, Pi.zero_apply]

theorem intersectionChainBasisEquiv_symm_single (q k : ℕ) (t : Fin k → ι)
    (σ : IntersectionSimplex S U q k t) (r : ℝ) :
    ((intersectionChainBasisEquiv S U q k t).symm (Finsupp.single σ r)).val =
      Finsupp.single σ.val.val r := by
  simp only [intersectionChainBasisEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

theorem intersectionBoundary_basis (q k : ℕ) (t : Fin k → ι)
    (σ : IntersectionSimplex S U (q+1) k t) :
    intersectionChainBasisEquiv S U q k t
      (intersectionBoundary S U q k t
        ((intersectionChainBasisEquiv S U (q+1) k t).symm (Finsupp.single σ 1))) =
      ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
        Finsupp.single (intersectionFace S U σ j) 1 := by
  apply (intersectionChainBasisEquiv S U q k t).symm.injective
  rw [LinearEquiv.symm_apply_apply, map_sum]
  apply Subtype.ext
  simp only [map_zsmul, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    intersectionChainBasisEquiv_symm_single]
  change boundary ℝ ℝ (TopCat.of M) q
    (((intersectionChainBasisEquiv S U (q+1) k t).symm (Finsupp.single σ 1)).val) = _
  rw [intersectionChainBasisEquiv_symm_single,
    P202.SingularChains.boundary_single]
  rfl

theorem intersectionV_formula (q k : ℕ) (f : IntersectionCochainRow S U q k)
    (t : Fin k → ι) (σ : IntersectionSimplex S U (q+1) k t) :
    intersectionV S U q k f t (Finsupp.single σ 1) =
      ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
        f t (Finsupp.single (intersectionFace S U σ j) 1) := by
  change f t (intersectionChainBasisEquiv S U q k t
    (intersectionBoundary S U q k t
      ((intersectionChainBasisEquiv S U (q+1) k t).symm (Finsupp.single σ 1)))) = _
  rw [intersectionBoundary_basis, map_sum]
  simp only [map_zsmul]
  simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg,
    Int.cast_one, smul_eq_mul]

theorem intersectionD_V (q k : ℕ) (f : IntersectionCochainRow S U q k) :
    intersectionV S U q (k+1) (intersectionD S U q k f) =
      intersectionD S U (q+1) k (intersectionV S U q k f) := by
  funext t
  apply (Finsupp.llift ℝ ℝ ℝ _).symm.injective
  funext σ
  change intersectionV S U q (k+1) (intersectionD S U q k f) t (Finsupp.single σ 1) =
    intersectionD S U (q+1) k (intersectionV S U q k f) t (Finsupp.single σ 1)
  simp_rw [intersectionV_formula, intersectionD_alternating, intersectionV_formula, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hface : deleteIndex S U q (intersectionFace S U σ j) i =
      intersectionFace S U (deleteIndex S U (q+1) σ i) j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hface]
  ring

end VerticalDifferential

theorem cochainBicomplex_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    cochainBicomplex_type.{u,v} := by
  intro n a M _ S ι U
  exact ⟨intersectionV_square S U, intersectionD_V S U, intersectionV_formula S U⟩


set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace VectorRows
variable (I : Type v) (V : Type u) [AddCommGroup V] [Module ℝ V]
abbrev Row (k : ℕ) := (Fin k → I) → V
/-- The augmented alternating differential with any real vector-space coefficients. -/
def d : (k : ℕ) → Row I V k →ₗ[ℝ] Row I V (k+1)
  | 0 => {
    toFun := fun f _ => f Fin.elim0
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  | k+1 => {
    toFun := fun f t => f (Fin.tail t) - d k (fun s => f (Fin.cons (t 0) s)) (Fin.tail t)
    map_add' := by
      intro f g
      funext t
      change (f (Fin.tail t) + g (Fin.tail t)) -
        d k ((fun s => f (Fin.cons (t 0) s)) + (fun s => g (Fin.cons (t 0) s))) (Fin.tail t) = _
      rw [map_add]
      simp only [Pi.add_apply]
      change _ = (f (Fin.tail t) - _) + (g (Fin.tail t) - _)
      abel
    map_smul' := by
      intro r f
      funext t
      change r • f (Fin.tail t) -
        d k (r • (fun s => f (Fin.cons (t 0) s))) (Fin.tail t) = _
      rw [map_smul]
      exact (smul_sub _ _ _).symm }

def h (i : I) (k : ℕ) : Row I V (k+1) →ₗ[ℝ] Row I V k where
  toFun f t := f (Fin.cons i t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem d_cons (k : ℕ) (f : Row I V (k+1)) (i : I) (t : Fin (k+1) → I) :
    d I V (k+1) f (Fin.cons i t) = f t - d I V k (h I V i k f) t := by
  simp [d, h, Fin.tail_cons]

theorem contraction (i : I) (k : ℕ) (f : Row I V (k+1)) :
    d I V k (h I V i k f) + h I V i (k+1) (d I V (k+1) f) = f := by
  funext t
  change d I V k (h I V i k f) t + d I V (k+1) f (Fin.cons i t) = f t
  rw [d_cons]
  abel

theorem square (k : ℕ) (f : Row I V k) : d I V (k+1) (d I V k f) = 0 := by
  induction k with
  | zero => funext t; simp [d]
  | succ k ih =>
    funext t
    have ht : t = Fin.cons (t 0) (Fin.tail t) := (Fin.cons_self_tail t).symm
    rw [ht, d_cons]
    have heq : h I V (t 0) (k+1) (d I V (k+1) f) =
        f - d I V k (h I V (t 0) k f) := by
      funext s
      exact d_cons I V k f (t 0) s
    rw [heq, map_sub, ih]
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
    simp

theorem alternating (k : ℕ) (f : Row I V k) (t : Fin (k+1) → I) :
    d I V k f t = ∑ j : Fin (k+1), (-1 : ℝ)^j.val • f (t ∘ j.succAbove) := by
  induction k with
  | zero =>
    rw [Fin.sum_univ_succ]
    simp only [d, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_zero, add_zero,
      Fin.val_zero, pow_zero, one_smul]
    exact congrArg f (Subsingleton.elim _ _)
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    change f (Fin.tail t) - d I V k (h I V (t 0) k f) (Fin.tail t) = _
    rw [ih]
    simp only [← sub_eq_add_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply congrArg f
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [h, Function.comp_def]
    · simp [h, Function.comp_def, Fin.tail]

/-- Finite-support weights summing to one average the vertex insertions.
This identity uses no dimension assumption on the coefficients. -/
theorem weighted_contraction (ρ : I → ℝ) (s : Finset I)
    (hsum : ∑ i ∈ s, ρ i = 1) (k : ℕ) (f : Row I V (k+1)) :
    d I V k (∑ i ∈ s, ρ i • h I V i k f) +
      (∑ i ∈ s, ρ i • h I V i (k+1) (d I V (k+1) f)) = f := by
  rw [map_sum]
  simp only [map_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, contraction]
  rw [← Finset.sum_smul, hsum, one_smul]
end VectorRows

section Forms
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
  SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
  SmoothManifolds.TangentData SmoothManifolds.ModelData
open Filter Set
open scoped Topology
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S} {q : ℕ}
  (B : FormBundle C q) {ι : Type v} (U : ι → TopologicalSpace.Opens M)

/-- Evaluation over all covering members containing a fixed point. -/
def formAtPoint (x : M) (k : ℕ) :
    FormRow B U k →ₗ[ℝ]
      VectorRows.Row {i : ι // x ∈ U i} (Fiber (TangentData.TangentSpace S x) q) k where
  toFun f t := (f (fun j => (t j).val)).val ⟨x, fun j => (t j).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem formD_apply (k : ℕ) (f : FormRow B U k)
    (t : Fin (k+1) → ι) (x : tupleOpen U t) :
    (formD B U k f t).val x =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val •
        (f (t ∘ j.succAbove)).val ⟨x.val, fun l => x.property (j.succAbove l)⟩ := by
  simp only [formD, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
    Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, formRestriction]

theorem formAtPoint_D (x : M) (k : ℕ) (f : FormRow B U k) :
    formAtPoint B U x (k+1) (formD B U k f) =
      VectorRows.d _ _ k (formAtPoint B U x k f) := by
  funext t
  rw [VectorRows.alternating]
  exact formD_apply B U k f _ _

theorem formAtPoint_ext (k : ℕ) (f g : FormRow B U k)
    (he : ∀ x, formAtPoint B U x k f = formAtPoint B U x k g) : f = g := by
  funext t
  apply Subtype.ext
  funext x
  exact congrFun (he x.val) (fun j => ⟨t j, x.property j⟩)

theorem formD_square (k : ℕ) (f : FormRow B U k) :
    formD B U (k+1) (formD B U k f) = 0 := by
  apply formAtPoint_ext B U (k+2)
  intro x
  have h1 := formAtPoint_D B U x (k+1) (formD B U k f)
  have h2 := congrArg (VectorRows.d {i : ι // x ∈ U i}
    (Fiber (TangentData.TangentSpace S x) q) (k+1)) (formAtPoint_D B U x k f)
  exact (h1.trans h2).trans ((VectorRows.square _ _ k _).trans
    ((formAtPoint B U x (k+2)).map_zero).symm)

/-- Locally finite sums of genuine smooth restricted sections remain smooth.
The closed sets here control supports; the fibers may vary with the point. -/
theorem restricted_finsum_smooth (V : TopologicalSpace.Opens M)
    (f : ι → RestrictedField S V q) (K : ι → Set M)
    (hf : ∀ i, IsRestrictedForm B V (f i)) (hK : LocallyFinite K)
    (hc : ∀ i, IsClosed (K i))
    (hz : ∀ i (x : V), x.val ∉ K i → f i x = 0) :
    IsRestrictedForm B V (fun x => ∑ᶠ i, f i x) := by
  classical
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  intro x
  let s := (hK.point_finite x.val).toFinset
  have hsmooth : IsRestrictedForm B V (∑ i ∈ s, f i) := by
    have hmem : ∀ i ∈ s, f i ∈ formsOn B V := fun i _ => hf i
    exact (formsOn B V).sum_mem hmem
  apply manifoldContDiffAt_congr (hsmooth x)
  have he : ∀ᶠ y in nhds x, {i | y.val ∈ K i} ⊆ {i | x.val ∈ K i} :=
    continuous_subtype_val.continuousAt.eventually (hK.eventually_subset hc x.val)
  filter_upwards [he] with y hy
  apply congrArg (fun z => (⟨y.val,z⟩ : Bundle.TotalSpace (ModelData.Euclidean (n.choose q))
    (fun p => Fiber (TangentData.TangentSpace S p) q)))
  simp only [Finset.sum_apply]
  change (∑ i ∈ s, f i y) = ∑ᶠ i, f i y
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply (hK.point_finite x.val).mem_toFinset.mpr
  apply hy
  by_contra hn
  exact hi (hz i y hn)

/-- A single weighted insertion, extended smoothly by zero. -/
def formInsertion (ρ : ι → M → ℝ) (k : ℕ) (f : FormRow B U (k+1))
    (t : Fin k → ι) (i : ι) : RestrictedField S (tupleOpen U t) q :=
  fun x => zeroExtend (fun y : tupleOpen U (Fin.cons i t) => ρ i y.val •
    (f (Fin.cons i t)).val y) x.val

theorem formInsertion_zero (ρ : ι → M → ℝ) (k : ℕ) (f : FormRow B U (k+1))
    (t : Fin k → ι) (i : ι) (x : tupleOpen U t) (hx : ρ i x.val = 0) :
    formInsertion B U ρ k f t i x = 0 := by
  classical
  simp only [formInsertion, zeroExtend]
  split_ifs <;> simp [hx]

theorem formInsertion_smooth (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ)
    (k : ℕ) (f : FormRow B U (k+1)) (t : Fin k → ι) (i : ι) :
    IsRestrictedForm B (tupleOpen U t) (formInsertion B U ρ k f t i) := by
  apply weighted_extension B (tupleOpen U (Fin.cons i t)) (tupleOpen U t)
    (ρ i) (hρ.1 i) _ (f _).property
  intro x hx
  intro j
  refine Fin.cases ?_ (fun l => ?_) j
  · exact hsub i hx.1
  · exact hx.2 l

/-- The genuine partition-of-unity insertion operator on smooth forms. -/
def formH (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ)
    (k : ℕ) (f : FormRow B U (k+1)) : FormRow B U k :=
  fun t => ⟨fun x => ∑ᶠ i, formInsertion B U ρ k f t i x,
    restricted_finsum_smooth B (tupleOpen U t) _ (fun i => ModelData.sectionSupport (ρ i))
      (fun i => formInsertion_smooth B U ρ hρ hsub k f t i) hρ.2.2.1
      (fun _ => isClosed_closure) (by
        intro i x hx
        apply formInsertion_zero
        by_contra hn
        exact hx (subset_closure hn))⟩

section FormsContraction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
theorem formValue_congr {k : ℕ} (f : FormRow B U k) (x : M)
    {t t' : Fin k → ι} (he : t = t')
    (hx : x ∈ tupleOpen U t) (hx' : x ∈ tupleOpen U t') :
    (f t).val ⟨x,hx⟩ = (f t').val ⟨x,hx'⟩ := by
  subst t'
  rfl

def formVertex (x : M) (i0 : {i : ι // x ∈ U i}) (i : ι) : {i : ι // x ∈ U i} := by
  classical
  exact if hi : x ∈ U i then ⟨i,hi⟩ else i0

theorem formAtPoint_H_sum (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ)
    (x : M) (i0 : {i : ι // x ∈ U i}) (k : ℕ) (f : FormRow B U (k+1)) :
    let s := (hρ.2.2.1.point_finite x).toFinset
    formAtPoint B U x k (formH B U ρ hρ hsub k f) =
      ∑ i ∈ s, ρ i x • VectorRows.h _ _ (formVertex U x i0 i) k (formAtPoint B U x (k+1) f) := by
  classical
  dsimp only
  funext t
  change (∑ᶠ i, formInsertion B U ρ k f (fun j => (t j).val) i
    ⟨x,fun j => (t j).property⟩) = _
  rw [finsum_eq_sum_of_support_subset _ (s := (hρ.2.2.1.point_finite x).toFinset) ?_]
  · simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x ∈ U i
    · have hm : x ∈ tupleOpen U (Fin.cons i (fun j => (t j).val)) := by
        intro j
        exact Fin.cases hi (fun l => (t l).property) j
      simp only [formInsertion, zeroExtend, dite_eq_left hm, formVertex, dite_eq_left hi,
        VectorRows.h, LinearMap.coe_mk, AddHom.coe_mk, formAtPoint]
      have he : (fun j => ((Fin.cons ⟨i,hi⟩ t : Fin (k+1) → {i : ι // x ∈ U i}) j).val) =
          Fin.cons i (fun j => (t j).val) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      exact congrArg (fun z => ρ i x • z) (formValue_congr B U f x he.symm _ _)
    · have hz : ρ i x = 0 := by
        by_contra hn
        exact hi (hsub i (subset_closure hn))
      calc
        _ = 0 := formInsertion_zero B U ρ k f _ i _ hz
        _ = _ := by simp only [hz, zero_smul]
  · intro i hi
    apply (hρ.2.2.1.point_finite x).mem_toFinset.mpr
    by_contra hn
    exact hi (formInsertion_zero B U ρ k f _ i _ (by
      by_contra hne
      exact hn (subset_closure hne)))

section Contraction
attribute [local irreducible] formH formD formAtPoint formsOn VectorRows.d VectorRows.h

theorem VectorRows.weighted_contraction_map
    {I : Type v} {J : Type*} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (v : J → I) (ρ : J → ℝ) (s : Finset J) (hsum : ∑ i ∈ s, ρ i = 1)
    (k : ℕ) (f : VectorRows.Row I V (k+1)) :
    VectorRows.d I V k (∑ i ∈ s, ρ i • VectorRows.h I V (v i) k f) +
      (∑ i ∈ s, ρ i • VectorRows.h I V (v i) (k+1) (VectorRows.d I V (k+1) f)) = f := by
  rw [map_sum]
  simp only [map_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, VectorRows.contraction]
  rw [← Finset.sum_smul, hsum, one_smul]

set_option maxHeartbeats 20000000 in
theorem formH_contraction (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ)
    (hcover : ∀ x, ∃ i, x ∈ U i) (k : ℕ) (f : FormRow B U (k+1)) :
    @Eq (FormRow B U (k+1))
      (formD B U k (formH B U ρ hρ hsub k f) +
        formH B U ρ hρ hsub (k+1) (formD B U (k+1) f)) f := by
  classical
  apply formAtPoint_ext B U (k+1)
  intro x
  obtain ⟨i0,hi0⟩ := hcover x
  let I := {i : ι // x ∈ U i}
  let V := Fiber (TangentData.TangentSpace S x) q
  let v : ι → I := formVertex U x ⟨i0,hi0⟩
  let F : VectorRows.Row I V (k+1) := formAtPoint B U x (k+1) f
  let s := (hρ.2.2.1.point_finite x).toFinset
  have hsum : ∑ i ∈ s, ρ i x = 1 := by
    calc
      _ = ∑ᶠ i, ρ i x := (finsum_eq_sum_of_support_subset _ (fun i hi =>
        (hρ.2.2.1.point_finite x).mem_toFinset.mpr (subset_closure hi))).symm
      _ = 1 := hρ.2.2.2 x
  have hH : formAtPoint B U x k (formH B U ρ hρ hsub k f) =
      ∑ i ∈ s, ρ i x • VectorRows.h I V (v i) k F :=
    formAtPoint_H_sum B U ρ hρ hsub x ⟨i0,hi0⟩ k f
  have hHd0 := formAtPoint_H_sum B U ρ hρ hsub x ⟨i0,hi0⟩ (k+1) (formD B U (k+1) f)
  have hHd : formAtPoint B U x (k+1) (formH B U ρ hρ hsub (k+1) (formD B U (k+1) f)) =
      ∑ i ∈ s, ρ i x • VectorRows.h I V (v i) (k+1) (VectorRows.d I V (k+1) F) :=
    hHd0.trans (congrArg
      (fun z : VectorRows.Row I V (k+2) => ∑ i ∈ s, ρ i x • VectorRows.h I V (v i) (k+1) z)
      (formAtPoint_D B U x (k+1) f))
  have hDH : formAtPoint B U x (k+1) (formD B U k (formH B U ρ hρ hsub k f)) =
      VectorRows.d I V k (∑ i ∈ s, ρ i x • VectorRows.h I V (v i) k F) :=
    (formAtPoint_D B U x k (formH B U ρ hρ hsub k f)).trans
      (congrArg (VectorRows.d I V k) hH)
  calc
    _ = formAtPoint B U x (k+1) (formD B U k (formH B U ρ hρ hsub k f)) +
        formAtPoint B U x (k+1) (formH B U ρ hρ hsub (k+1) (formD B U (k+1) f)) :=
      map_add (formAtPoint B U x (k+1)) _ _
    _ = VectorRows.d I V k (∑ i ∈ s, ρ i x • VectorRows.h I V (v i) k F) +
        (∑ i ∈ s, ρ i x • VectorRows.h I V (v i) (k+1) (VectorRows.d I V (k+1) F)) :=
      congrArg₂ (fun z z' : VectorRows.Row I V (k+1) => z + z') hDH hHd
    _ = F := VectorRows.weighted_contraction_map v (fun i => ρ i x) s hsum k F

end Contraction

@[simp] theorem formH_zero (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ) (k : ℕ) :
    formH B U ρ hρ hsub k 0 = 0 := by
  unfold formH
  funext t
  apply Subtype.ext
  funext x
  change (∑ᶠ i, formInsertion B U ρ k 0 t i x) = 0
  calc
    _ = ∑ᶠ i : ι, (0 : Fiber (TangentData.TangentSpace S x.val) q) := by
      apply finsum_congr
      intro i
      simp only [formInsertion, zeroExtend]
      split_ifs <;> simp only [Pi.zero_apply, Submodule.coe_zero, smul_zero]
    _ = 0 := finsum_zero

theorem formD_zero_injective (hcover : ∀ x, ∃ i, x ∈ U i) :
    Function.Injective (formD B U 0) := by
  intro f g he
  apply formAtPoint_ext B U 0
  intro x
  obtain ⟨i0,hi0⟩ := hcover x
  have h := congrArg (formAtPoint B U x 1) he
  rw [formAtPoint_D, formAtPoint_D] at h
  funext t
  have hh := congrFun h (fun _ => ⟨i0,hi0⟩)
  change (formAtPoint B U x 0 f) Fin.elim0 = (formAtPoint B U x 0 g) Fin.elim0 at hh
  simpa only [Subsingleton.elim t Fin.elim0] using hh

theorem formRows_exact (hcover : ∀ x, ∃ i, x ∈ U i) :
    Function.Injective (formD B U 0) ∧
    (∀ k (f : FormRow B U k), formD B U (k+1) (formD B U k f) = 0) ∧
    ∀ k (f : FormRow B U (k+1)),
      formD B U (k+1) f = 0 ↔ ∃ g, formD B U k g = f := by
  have hpart : ∃ ρ : ι → M → ℝ,
      PartitionData.IsSmoothPartition S.smoothStructure.val ρ ∧
        PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ :=
    exists_smooth_partition S (fun i => (U i : Set M)) (fun i => (U i).isOpen) hcover
  obtain ⟨ρ,hρ,hsub⟩ := hpart
  refine ⟨formD_zero_injective B U hcover, formD_square B U, ?_⟩
  intro k f
  constructor
  · intro hf
    refine ⟨formH B U ρ hρ hsub k f, ?_⟩
    have h := formH_contraction B U ρ hρ hsub hcover k f
    simpa only [hf, formH_zero, add_zero] using h
  · rintro ⟨g,rfl⟩
    exact formD_square B U k g


end FormsContraction

section VerticalForms
variable {B} (C : CotangentBundle S) (B : ∀ q, FormBundle C q)

theorem exteriorOn_coordinates (V : TopologicalSpace.Opens M) (q : ℕ)
    (ω : formsOn (B q) V) :
    HasRestrictedDerivative C V ω.val (exteriorOn C B V q ω).val := by
  let D := formOpenCalculus C B V
  have hd := D.coordinates q ((openFormEquiv D q).symm ω)
  change HasRestrictedDerivative C V ω.val
    (D.field (q+1) (D.complex.d q ((openFormEquiv D q).symm ω)))
  convert hd using 1
  exact (congrArg Subtype.val ((openFormEquiv D q).apply_symm_apply ω)).symm

theorem exteriorOn_square (V : TopologicalSpace.Opens M) (q : ℕ)
    (ω : formsOn (B q) V) :
    exteriorOn C B V (q+1) (exteriorOn C B V q ω) = 0 := by
  simp only [exteriorOn, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Cochain.square, map_zero]

theorem exteriorOn_restriction (V W : TopologicalSpace.Opens M) (hWV : W ≤ V)
    (q : ℕ) (ω : formsOn (B q) V) :
    exteriorOn C B W q (formRestriction (B q) V W hWV ω) =
      formRestriction (B (q+1)) V W hWV (exteriorOn C B V q ω) := by
  apply Subtype.ext
  exact restricted_derivative_unique C W _ _ _
    (exteriorOn_coordinates C B W q _)
    (restricted_derivative_restrict C V W hWV _ _
      (exteriorOn_coordinates C B V q ω))

theorem formV_square (q k : ℕ) (f : FormRow (B q) U k) :
    formV C B U (q+1) k (formV C B U q k f) = 0 := by
  funext t
  exact exteriorOn_square C B (tupleOpen U t) q (f t)

set_option maxHeartbeats 5000000 in
theorem formD_V (q k : ℕ) (f : FormRow (B q) U k) :
    formV C B U q (k+1) (formD (B q) U k f) =
      formD (B (q+1)) U k (formV C B U q k f) := by
  funext t
  simp only [formV, formD, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul, exteriorOn_restriction]

end VerticalForms

end Forms

theorem formsRowsExact_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    formsRowsExact_type.{u,v} := by
  intro n a M _ S C q B ι U hcover
  exact formRows_exact B U hcover

theorem formsBicomplex_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    formsBicomplex_type.{u,v} := by
  intro n a M _ S C B ι U
  exact ⟨formV_square U C B, formD_V U C B,
    fun q k f t => exteriorOn_coordinates C B (tupleOpen U t) q (f t)⟩

namespace Augmentation
open P202Specs.CochainCoverDescent
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
  SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
  SmoothManifolds.TangentData SmoothManifolds.ModelData SmoothManifolds.MapData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S}
  {B : ∀ q, FormBundle C q}

/-- Recover a global field from the forms augmentation. -/
def globalField {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ)
    (ω : FormRow (B q) U 0) : Field S q :=
  fun x => (ω Fin.elim0).val ⟨x, fun j => Fin.elim0 j⟩

theorem globalField_smooth {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ)
    (ω : FormRow (B q) U 0) : IsForm (B q) (globalField U q ω) := by
  letI := (cotangentSpace C).topology
  letI := (B q).space.topology
  have hs := (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
    (B q).space.bundle.totalManifold.smoothStructure.val
    (fun p => (⟨p, globalField U q ω p⟩ : Bundle.TotalSpace (ModelData.Euclidean (n.choose q))
      (fun x => Fiber (TangentData.TangentSpace S x) q)))
    (tupleOpen U Fin.elim0) (tupleOpen U Fin.elim0).isOpen).mpr
      ((ω Fin.elim0).property)
  intro x
  exact hs x (fun j => Fin.elim0 j)

/-- Identification with the original global forms, rather than with a new calculus. -/
def formAugmentationEquiv (K : DeRhamData.Calculus C B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ) :
    FormRow (B q) U 0 ≃ₗ[ℝ] K.forms q where
  toFun ω := ⟨globalField U q ω, (K.mem_forms q _).mpr (globalField_smooth U q ω)⟩
  invFun ω t := ⟨fun p => ω.val p.val,
    restrict_smooth (B q) (tupleOpen U t) ω.val ((K.mem_forms q _).mp ω.property)⟩
  left_inv ω := by
    funext t
    have ht : t = Fin.elim0 := Subsingleton.elim _ _
    subst t
    apply Subtype.ext
    funext x
    rfl
  right_inv ω := by
    apply Subtype.ext
    funext x
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formAugmentationEquiv_d (K : DeRhamData.Calculus C B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ)
    (ω : FormRow (B q) U 0) :
    formAugmentationEquiv K U (q+1) (formV C B U q 0 ω) =
      K.d q (formAugmentationEquiv K U q ω) := by
  apply Subtype.ext
  funext x
  have hd := restricted_derivative_unique C (tupleOpen U Fin.elim0) _ _ _
    (exteriorOn_coordinates C B (tupleOpen U Fin.elim0) q (ω Fin.elim0))
    (global_derivative_restrict K q (formAugmentationEquiv K U q ω)
      (tupleOpen U Fin.elim0))
  exact congrFun hd ⟨x, fun j => Fin.elim0 j⟩

end Augmentation

theorem formsAugmentation_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    formsAugmentation_type.{u,v} := by
  intro n a M _ S C B K ι U
  exact ⟨Augmentation.formAugmentationEquiv K U, fun _ _ _ => rfl,
    Augmentation.formAugmentationEquiv_d K U⟩

end P202.CochainCoverDescent

namespace P202.CochainCoverDescent.TotalAlgebra.Data
universe v
variable {E : Type v} [AddCommGroup E] [Module ℝ E] (B : P202.CochainCoverDescent.TotalAlgebra.Data E)
/-- Exact horizontal rows imply acyclicity of the genuine signed total.
Only the common lower bounds and exactness of the rows are used. -/
theorem total_exact_of_rows_exact
    (hexact : ∀ p q z, z ∈ B.space p q → B.horizontal z = 0 →
      ∃ y, y ∈ B.space (p-1) q ∧ B.horizontal y = z)
    (n : ℤ) (x : B.total n) (hx : B.differential n x.val = 0) :
    ∃ y : B.total (n-1), B.differential (n-1) y.val = x.val := by
  have hstep : ∀ k : ℕ, ∃ y : B.total (n-1),
      ∀ q, q < k → (x.val - B.differential (n-1) y.val) q = 0 := by
    intro k
    induction k with
    | zero => exact ⟨0, fun q hq => by omega⟩
    | succ k ih =>
      obtain ⟨y, hy⟩ := ih
      let r := x.val - B.differential (n-1) y.val
      have hr : r ∈ B.total n := by
        apply (B.total n).sub_mem x.property
        convert B.differential_mem (n-1) y.property using 1
        congr 1
        omega
      have hrc : B.differential n r = 0 := by
        dsimp [r]
        rw [map_sub, hx]
        have hd := B.differential_square (n-1) y.val
        have he : n-1+1=n := by omega
        rw [he] at hd
        rw [hd, sub_self]
      obtain ⟨z, hz, hdz⟩ := hexact (n-k) k (r k) (hr k) (B.head_closed n hrc k hy)
      have hzm : Pi.single k z ∈ B.total (n-1) := by
        apply B.single_mem
        have he : (n-1)-(k:ℤ) = (n-k)-1 := by omega
        rw [he]
        exact hz
      refine ⟨y + ⟨Pi.single k z, hzm⟩, ?_⟩
      intro q hq
      change (x.val - B.differential (n-1) (y.val + Pi.single k z)) q = 0
      rw [map_add, sub_add_eq_sub_sub]
      change r q - B.differential (n-1) (Pi.single k z) q = 0
      by_cases he : q=k
      · subst q
        rw [B.differential_single_self, hdz, sub_self]
      · have hyq : r q = 0 := hy q (by omega)
        rw [hyq, B.differential_single_before (n-1) k z q (by omega), sub_self]
  obtain ⟨y, hy⟩ := hstep (n.toNat+1)
  refine ⟨y, ?_⟩
  have hr : x.val - B.differential (n-1) y.val ∈ B.total n := by
    apply (B.total n).sub_mem x.property
    convert B.differential_mem (n-1) y.property using 1
    congr 1
    omega
  have he : x.val - B.differential (n-1) y.val = 0 := by
    funext q
    by_cases hq : q < n.toNat+1
    · exact hy q hq
    · apply B.total_component_zero n hr q
      omega
  exact (sub_eq_zero.mp he).symm

end P202.CochainCoverDescent.TotalAlgebra.Data

namespace P202.CochainCoverDescent.ConeAlgebra.Map
universe v w
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  {F : Type w} [AddCommGroup F] [Module ℝ F]
  {C : Complex E} {D : Complex F} (f : Map C D)
/-- Acyclicity of the ordinary mapping cone gives surjectivity on actual
cycles modulo actual boundaries, including every integer degree. -/
theorem cohomologyMap_surjective_of_cone_acyclic (h : f.cone.Acyclic) (n : ℤ) :
    Function.Surjective (f.cohomologyMap n) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ b =>
    have hb : ((b.val,0) : F × E) ∈ f.cone.space n := ⟨b.property.1,(C.space _).zero_mem⟩
    have hclosed : f.cone.differential n (b.val,0) = 0 := by
      ext <;> simp [show D.differential n b.val = 0 from b.property.2]
    obtain ⟨y, hy, he⟩ := h n (b.val,0) hb hclosed
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change D.differential (n-1) y.1 + f.map (n-1+1) y.2 = b.val at he1
    change -C.differential (n-1+1) y.2 = 0 at he2
    change y.1 ∈ D.space (n-1) ∧ y.2 ∈ C.space (n-1+1) at hy
    have hn : n-1+1=n := by omega
    rw [hn] at he1 he2 hy
    have hcy : y.2 ∈ C.cycles n := ⟨hy.2, neg_eq_zero.mp he2⟩
    refine ⟨Submodule.Quotient.mk ⟨y.2,hcy⟩, ?_⟩
    change (Submodule.Quotient.mk (f.cycleMap n ⟨y.2,hcy⟩) : D.Cohomology n) = Submodule.Quotient.mk b
    apply (Submodule.Quotient.eq (D.boundaries n)).mpr
    apply (D.boundary_mem_iff n _).mpr
    refine ⟨-y.1, (D.space _).neg_mem hy.1, ?_⟩
    change D.differential (n-1) (-y.1) = f.map n y.2 - b.val
    rw [map_neg]
    calc
      -D.differential (n-1) y.1 = f.map n y.2 - (D.differential (n-1) y.1 + f.map n y.2) := by abel
      _ = f.map n y.2 - b.val := by rw [he1]

/-- Acyclicity of the ordinary mapping cone gives injectivity on actual
cycles modulo actual boundaries. -/
theorem cohomologyMap_injective_of_cone_acyclic (h : f.cone.Acyclic) (n : ℤ) :
    Function.Injective (f.cohomologyMap n) := by
  apply (injective_iff_map_eq_zero (f.cohomologyMap n)).mpr
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ a =>
    change (Submodule.Quotient.mk (f.cycleMap n a) : D.Cohomology n) = 0 at hq
    obtain ⟨b,hb,he⟩ := (D.boundary_mem_iff n _).mp ((Submodule.Quotient.mk_eq_zero _).mp hq)
    have hz : ((-b,a.val) : F × E) ∈ f.cone.space (n-1) := by
      constructor
      · exact (D.space _).neg_mem hb
      · change a.val ∈ C.space (n-1+1)
        have hn : n-1+1=n := by omega
        rw [hn]
        exact a.property.1
    have hclosed : f.cone.differential (n-1) (-b,a.val) = 0 := by
      have hn : n-1+1=n := by omega
      ext
      · simp only [cone_differential, Prod.fst, Prod.fst_zero, map_neg, hn]
        change -D.differential (n-1) b + f.map n a.val = 0
        rw [he]
        change -(f.map n a.val) + f.map n a.val = 0
        exact neg_add_cancel _
      · simp only [cone_differential, Prod.snd, Prod.snd_zero, hn]
        rw [show C.differential n a.val = 0 from a.property.2, neg_zero]
    obtain ⟨y,hy,he'⟩ := h (n-1) (-b,a.val) hz hclosed
    have hy2 : y.2 ∈ C.space (n-1) := by
      have ht : y.2 ∈ C.space (n-1-1+1) := hy.2
      have hn : n-1-1+1=n-1 := by omega
      rwa [hn] at ht
    have he2 := congrArg Prod.snd he'
    simp only [cone_differential, Prod.snd] at he2
    have hn : n-1-1+1=n-1 := by omega
    rw [hn] at he2
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (C.boundary_mem_iff n a).mpr
    refine ⟨-y.2,(C.space _).neg_mem hy2,?_⟩
    simpa only [map_neg] using he2

theorem cohomologyMap_bijective_of_cone_acyclic (h : f.cone.Acyclic) (n : ℤ) :
    Function.Bijective (f.cohomologyMap n) :=
  ⟨f.cohomologyMap_injective_of_cone_acyclic h n,
   f.cohomologyMap_surjective_of_cone_acyclic h n⟩

/-- Conversely, a genuine isomorphism on the cohomology quotients makes
the ordinary mapping cone acyclic. -/
theorem cone_acyclic_of_cohomologyMap_bijective
    (h : ∀ n, Function.Bijective (f.cohomologyMap n)) : f.cone.Acyclic := by
  intro n x hx hc
  change x.1 ∈ D.space n ∧ x.2 ∈ C.space (n+1) at hx
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  change D.differential n x.1 + f.map (n+1) x.2 = 0 at hc1
  change -C.differential (n+1) x.2 = 0 at hc2
  have ha : x.2 ∈ C.cycles (n+1) := ⟨hx.2,neg_eq_zero.mp hc2⟩
  let a : C.cycles (n+1) := ⟨x.2,ha⟩
  have hfa : f.cohomologyMap (n+1) (Submodule.Quotient.mk a) = 0 := by
    change (Submodule.Quotient.mk (f.cycleMap (n+1) a) : D.Cohomology (n+1)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (D.boundary_mem_iff (n+1) _).mpr
    have hi : n+1-1=n := by omega
    refine ⟨-x.1,?_,?_⟩
    · rw [hi]
      exact (D.space _).neg_mem hx.1
    · rw [hi,map_neg]
      change -D.differential n x.1 = f.map (n+1) x.2
      exact neg_eq_iff_add_eq_zero.mpr hc1
  have haz : (Submodule.Quotient.mk a : C.Cohomology (n+1)) = 0 :=
    (h (n+1)).1 (by simpa only [map_zero] using hfa)
  obtain ⟨e,hem,hee⟩ := (C.boundary_mem_iff (n+1) a).mp ((Submodule.Quotient.mk_eq_zero _).mp haz)
  have hi : n+1-1=n := by omega
  rw [hi] at hem hee
  have hz : x.1 + f.map n e ∈ D.cycles n := by
    constructor
    · exact (D.space _).add_mem hx.1 (f.map_mem n e hem)
    · change D.differential n (x.1 + f.map n e) = 0
      rw [map_add,f.commute,hee]
      exact hc1
  let z : D.cycles n := ⟨x.1 + f.map n e,hz⟩
  obtain ⟨u,hu⟩ := (h n).2 (Submodule.Quotient.mk z)
  obtain ⟨c,hcu⟩ := Submodule.Quotient.mk_surjective (C.boundaries n) u
  rw [←hcu] at hu
  change (Submodule.Quotient.mk (f.cycleMap n c) : D.Cohomology n) = Submodule.Quotient.mk z at hu
  have ht : z - f.cycleMap n c ∈ D.boundaries n := (Submodule.Quotient.eq _).mp hu.symm
  obtain ⟨t,htm,hte⟩ := (D.boundary_mem_iff n _).mp ht
  have hn : n-1+1=n := by omega
  refine ⟨(t,c.val-e),?_,?_⟩
  · change t ∈ D.space (n-1) ∧ c.val-e ∈ C.space (n-1+1)
    rw [hn]
    exact ⟨htm,(C.space n).sub_mem c.property.1 hem⟩
  · ext
    · change D.differential (n-1) t + f.map (n-1+1) (c.val-e) = x.1
      rw [hn,map_sub,hte]
      change (x.1+f.map n e-f.map n c.val) + (f.map n c.val-f.map n e) = x.1
      abel
    · change -C.differential (n-1+1) (c.val-e) = x.2
      rw [hn,map_sub,show C.differential n c.val=0 from c.property.2,hee]
      change -(0-x.2)=x.2
      abel

theorem cone_acyclic_iff_cohomologyMap_bijective :
    f.cone.Acyclic ↔ ∀ n, Function.Bijective (f.cohomologyMap n) :=
  ⟨fun h n => f.cohomologyMap_bijective_of_cone_acyclic h n,
    f.cone_acyclic_of_cohomologyMap_bijective⟩

end P202.CochainCoverDescent.ConeAlgebra.Map

namespace P202.CochainCoverDescent.TotalAlgebra.Data
universe v
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
variable (B : P202.CochainCoverDescent.TotalAlgebra.Data E)

theorem vertical_closed_of_next_zero (n : ℤ) {x : ℕ → E}
    (hx : B.differential n x = 0) (q : ℕ) (hnext : x (q+1) = 0) :
    B.vertical (x q) = 0 := by
  have h := congrFun hx (q+1)
  rw [B.differential_succ,hnext,map_zero,zero_add] at h
  exact (smul_eq_zero.mp h).resolve_left (zpow_ne_zero _ (by norm_num))

theorem differential_single_next (n : ℤ) (k : ℕ) (z : E) :
    B.differential n (Pi.single k z) (k+1) =
      (-1 : ℝ)^(n-k) • B.vertical z := by
  simp

theorem differential_single_after (n : ℤ) (k : ℕ) (z : E)
    (q : ℕ) (hq : k+1 < q) :
    B.differential n (Pi.single k z) q = 0 := by
  cases q with
  | zero => omega
  | succ q => simp [show k ≠ q+1 by omega,show k ≠ q by omega]

/-- Exact vertical columns imply acyclicity of the genuine signed total.
The proof removes the top remaining vertical component, hence proceeds
in increasing horizontal degree and terminates after finitely many steps. -/
theorem total_exact_of_columns_exact
    (hzero : ∀ p z, z ∈ B.space p 0 → B.vertical z = 0 → z = 0)
    (hexact : ∀ p q z, z ∈ B.space p (q+1) → B.vertical z = 0 →
      ∃ y, y ∈ B.space p q ∧ B.vertical y = z)
    (n : ℤ) (x : B.total n) (hx : B.differential n x.val = 0) :
    ∃ y : B.total (n-1), B.differential (n-1) y.val = x.val := by
  by_cases hn : 0 ≤ n
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hstep : ∀ k : ℕ, ∃ y : B.total ((n:ℤ)-1),
        ∀ q, n < q+k → (x.val-B.differential ((n:ℤ)-1) y.val) q = 0 := by
      intro k
      induction k with
      | zero =>
        refine ⟨0,?_⟩
        intro q hq
        simpa using B.total_component_zero n x.property q (by omega)
      | succ k ih =>
        obtain ⟨y,hy⟩ := ih
        let r := x.val-B.differential ((n:ℤ)-1) y.val
        have hr : r ∈ B.total n := by
          apply (B.total n).sub_mem x.property
          convert B.differential_mem ((n:ℤ)-1) y.property using 1
          congr 1
          omega
        have hrc : B.differential n r = 0 := by
          dsimp [r]
          rw [map_sub,hx]
          have hd := B.differential_square ((n:ℤ)-1) y.val
          have he : (n:ℤ)-1+1=n := by omega
          rw [he] at hd
          rw [hd,sub_self]
        by_cases hk : n < k
        · refine ⟨y,?_⟩
          intro q hq
          exact hy q (by omega)
        · have hnk : k ≤ n := by omega
          let t := n-k
          have hnext : r (t+1) = 0 := hy (t+1) (by dsimp [t];omega)
          have hvc := B.vertical_closed_of_next_zero n hrc t hnext
          cases ht : t with
          | zero =>
            have hr0 : r 0 = 0 := hzero n (r 0) (by simpa using hr 0) (by simpa [ht] using hvc)
            refine ⟨y,?_⟩
            intro q hq
            by_cases hq0 : q=0
            · subst q;exact hr0
            · exact hy q (by dsimp [t] at ht;omega)
          | succ j =>
            have htop : n=j+1+k := by dsimp [t] at ht;omega
            obtain ⟨z,hz,hdz⟩ := hexact ((n:ℤ)-(j+1)) j (r (j+1)) (hr (j+1))
              (by simpa [ht] using hvc)
            let s : ℝ := (-1 : ℝ)^((n:ℤ)-1-j)
            have hs : s ≠ 0 := zpow_ne_zero _ (by norm_num)
            let w : ℕ → E := Pi.single j (s⁻¹ • z)
            have hwm : w ∈ B.total ((n:ℤ)-1) := by
              apply B.single_mem
              apply (B.space (((n:ℤ)-1)-j) j).smul_mem
              have he : (n:ℤ)-(j+1)=((n:ℤ)-1)-j := by omega
              rw [he] at hz
              exact hz
            have hwd : B.differential ((n:ℤ)-1) w (j+1) = r (j+1) := by
              rw [differential_single_next,map_smul,hdz]
              change s • s⁻¹ • r (j+1) = r (j+1)
              rw [smul_smul,mul_inv_cancel₀ hs,one_smul]
            refine ⟨y+⟨w,hwm⟩,?_⟩
            intro q hq
            change (x.val-B.differential ((n:ℤ)-1) (y.val+w)) q=0
            rw [map_add,sub_add_eq_sub_sub]
            change r q-B.differential ((n:ℤ)-1) w q=0
            by_cases hqj : q=j+1
            · subst q;rw [hwd,sub_self]
            · have hrq : r q=0 := hy q (by omega)
              rw [hrq,B.differential_single_after ((n:ℤ)-1) j (s⁻¹ • z) q (by omega),sub_self]
    obtain ⟨y,hy⟩ := hstep (n+1)
    refine ⟨y,?_⟩
    have he : x.val-B.differential ((n:ℤ)-1) y.val = 0 := by
      funext q
      exact hy q (by omega)
    exact (sub_eq_zero.mp he).symm
  · refine ⟨0,?_⟩
    have hx0 : x.val=0 := by
      funext q
      exact B.total_component_zero n x.property q (by omega)
    simpa using hx0.symm

end P202.CochainCoverDescent.TotalAlgebra.Data

namespace P202.CochainCoverDescent.TotalAlgebra.Data
open P202.CochainCoverDescent.ConeAlgebra
universe v
variable {E : Type v} [AddCommGroup E] [Module ℝ E] (B : Data E)
/-- The actual augmentation cone is acyclic as soon as the augmented
horizontal rows are exact. This uses the explicit cone identification and
finite elimination, with no finite-cover or finite-dimensional hypothesis. -/
theorem augmentationCone_acyclic
    (hexact : ∀ p q z, z ∈ B.space p q → B.horizontal z = 0 →
      ∃ y, y ∈ B.space (p-1) q ∧ B.horizontal y = z) :
    B.augmentationMap.cone.Acyclic := by
  intro n x hx hclosed
  have hm : B.coneToTotalLinear n x ∈ B.total (n+1) := B.coneToTotal.map_mem n x hx
  have htc : B.differential (n+1) (B.coneToTotalLinear n x) = 0 := by
    have hc := B.coneToTotal.commute n x
    change B.differential (n+1) (B.coneToTotalLinear n x) =
      B.coneToTotalLinear (n+1) (B.augmentationMap.cone.differential n x) at hc
    rw [hclosed,map_zero] at hc
    exact hc
  have hyex : ∃ y : B.total n, B.differential n y.val = B.coneToTotalLinear n x := by
    have hy := B.total_exact_of_rows_exact hexact (n+1) ⟨B.coneToTotalLinear n x,hm⟩ htc
    have hn : n+1-1=n := by omega
    rw [hn] at hy
    exact hy
  obtain ⟨y,hy⟩ := hyex
  have hn : n-1+1=n := by omega
  have hym : y.val ∈ B.total (n-1+1) := by simpa only [hn] using y.property
  obtain ⟨w,hw,hwe⟩ := B.coneToTotal_surjective (n-1) ⟨y.val,hym⟩
  refine ⟨w,hw,?_⟩
  have hm' : B.augmentationMap.cone.differential (n-1) w - x ∈ B.augmentationMap.cone.space n := by
    apply (B.augmentationMap.cone.space n).sub_mem _ hx
    have hd := B.augmentationMap.cone.differential_mem (n-1) w hw
    simpa only [hn] using hd
  have hz : B.coneToTotalLinear n (B.augmentationMap.cone.differential (n-1) w - x) = 0 := by
    rw [map_sub]
    have hc := B.coneToTotal.commute (n-1) w
    change B.differential (n-1+1) (B.coneToTotalLinear (n-1) w) =
      B.coneToTotalLinear (n-1+1) (B.augmentationMap.cone.differential (n-1) w) at hc
    rw [hn] at hc
    rw [←hc,hwe,hy,sub_self]
  exact sub_eq_zero.mp (B.coneToTotal_injective n _ hm' hz)

/-- Exact augmented horizontal rows give an isomorphism on the actual
cohomology quotients in every degree. -/
theorem augmentation_quasiIso
    (hexact : ∀ p q z, z ∈ B.space p q → B.horizontal z = 0 →
      ∃ y, y ∈ B.space (p-1) q ∧ B.horizontal y = z)
    (n : ℤ) : Function.Bijective (B.augmentationMap.cohomologyMap n) :=
  B.augmentationMap.cohomologyMap_bijective_of_cone_acyclic
    (B.augmentationCone_acyclic hexact) n

end P202.CochainCoverDescent.TotalAlgebra.Data

namespace P202.CochainCoverDescent.CechTotals
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 5000000
open P202Specs.CochainCoverDescent P202.CochainCoverDescent.TotalAlgebra
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData SmoothManifolds.ModelData
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M}

/-- The actual augmented smooth-form bicomplex. Tuple length k has original
horizontal degree k-1, so the grid's vertical operator is minus exterior d. -/
def formData (C : CotangentBundle S) (B : ∀ q, FormBundle C q)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) :
    Data (GridEmbedding.Ambient (fun p q => FormRow (B q) U p)) :=
  GridEmbedding.data (fun p q => FormRow (B q) U p)
    (fun p q => formD (B q) U p) (fun p q => (-1 : ℝ) • formV C B U q p)
    (fun p q f => formD_square (B q) U p f)
    (by
      intro p q f
      simp only [LinearMap.smul_apply, map_smul, smul_smul, neg_mul_neg, one_mul, one_smul]
      exact formV_square U C B q p f)
    (by
      intro p q f
      simpa only [LinearMap.smul_apply, map_smul] using
        congrArg (fun z => (-1 : ℝ) • z) (formD_V U C B q p f).symm)

/-- The actual augmented smooth-cochain bicomplex, with the same shift/sign. -/
def cochainData (S : AtlasData.SmoothManifold n a M) {ι : Type v}
    (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι) :
    Data (GridEmbedding.Ambient (fun p q => IntersectionCochainRow S U q p)) :=
  GridEmbedding.data (fun p q => IntersectionCochainRow S U q p)
    (fun p q => intersectionD S U q p) (fun p q => (-1 : ℝ) • intersectionV S U q p)
    (fun p q f => intersectionD_square S U q p f)
    (by
      intro p q f
      simp only [LinearMap.smul_apply, map_smul, smul_smul, neg_mul_neg, one_mul, one_smul]
      exact intersectionV_square S U q p f)
    (by
      intro p q f
      simpa only [LinearMap.smul_apply, map_smul] using
        congrArg (fun z => (-1 : ℝ) • z) (intersectionD_V S U q p f).symm)

theorem formData_rows_exact (C : CotangentBundle S) (B : ∀ q, FormBundle C q)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∀ p q z, z ∈ (formData C B U).space p q →
      (formData C B U).horizontal z = 0 →
      ∃ y, y ∈ (formData C B U).space (p-1) q ∧ (formData C B U).horizontal y = z := by
  apply GridEmbedding.rows_exact
  · intro q
    exact (formRows_exact (B q) U hcover).1
  · intro p q z hz
    exact ((formRows_exact (B q) U hcover).2.2 p z).mp hz

theorem cochainData_rows_exact (S : AtlasData.SmoothManifold n a M) {ι : Type v}
    (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι) :
    ∀ p q z, z ∈ (cochainData S U).space p q →
      (cochainData S U).horizontal z = 0 →
      ∃ y, y ∈ (cochainData S U).space (p-1) q ∧ (cochainData S U).horizontal y = z := by
  apply GridEmbedding.rows_exact
  · intro q
    exact (intersectionRows_exact S U q).1
  · intro p q z hz
    exact ((intersectionRows_exact S U q).2.2 p z).mp hz

/-- Every cocycle in the actual augmented signed form total is a boundary. -/
theorem formTotal_exact (C : CotangentBundle S) (B : ∀ q, FormBundle C q)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (hcover : ∀ x, ∃ i, x ∈ U i)
    (m : ℤ) (x : (formData C B U).total m)
    (hx : (formData C B U).differential m x.val = 0) :
    ∃ y : (formData C B U).total (m-1),
      (formData C B U).differential (m-1) y.val = x.val :=
  (formData C B U).total_exact_of_rows_exact (formData_rows_exact C B U hcover) m x hx

/-- Every cocycle in the actual augmented signed smooth-cochain total is a boundary. -/
theorem cochainTotal_exact (S : AtlasData.SmoothManifold n a M) {ι : Type v}
    (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)
    (m : ℤ) (x : (cochainData S U).total m)
    (hx : (cochainData S U).differential m x.val = 0) :
    ∃ y : (cochainData S U).total (m-1),
      (cochainData S U).differential (m-1) y.val = x.val :=
  (cochainData S U).total_exact_of_rows_exact (cochainData_rows_exact S U) m x hx

end P202.CochainCoverDescent.CechTotals

namespace P202.CochainCoverDescent
open P202Specs.CochainCoverDescent
universe u v

theorem formsTotalAugmentation_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    formsTotalAugmentation_type.{u,v} := by
  intro n a M _ S C B ι U hcover
  refine ⟨CechTotals.formData C B U, rfl, rfl, rfl, ?_⟩
  intro m
  exact (CechTotals.formData C B U).augmentation_quasiIso
    (CechTotals.formData_rows_exact C B U hcover) m

theorem cochainTotalAugmentation_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    cochainTotalAugmentation_type.{u,v} := by
  intro n a M _ S ι U
  refine ⟨CechTotals.cochainData S U, rfl, rfl, rfl, ?_⟩
  intro m
  exact (CechTotals.cochainData S U).augmentation_quasiIso
    (CechTotals.cochainData_rows_exact S U) m

end P202.CochainCoverDescent

namespace P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.ConeAlgebra
universe v w
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  {F : Type w} [AddCommGroup F] [Module ℝ F]
namespace DataMap
variable {A : Data E} {B : Data F} (f : DataMap A B)
/-- The vertically shifted column cone, with vertical lower bound zero.
At vertical degree zero only the shifted source column remains. -/
def columnCone : Data (F × E) where
  space p q := match q with
    | 0 => (⊥ : Submodule ℝ F).prod (A.space p 0)
    | q+1 => (B.space p q).prod (A.space p (q+1))
  horizontal := B.horizontal.prodMap A.horizontal
  vertical := {
    toFun x := (B.vertical x.1 + f.linear x.2, -A.vertical x.2)
    map_add' _ _ := by ext <;> simp [map_add] <;> abel
    map_smul' _ _ := by ext <;> simp [map_smul,smul_add] }
  horizontal_mem p q x hx := by
    cases q with
    | zero =>
      constructor
      · change B.horizontal x.1=0
        rw [show x.1=0 from hx.1,map_zero]
      · exact A.horizontal_mem p 0 x.2 hx.2
    | succ q => exact ⟨B.horizontal_mem p q x.1 hx.1,A.horizontal_mem p (q+1) x.2 hx.2⟩
  vertical_mem p q x hx := by
    cases q with
    | zero =>
      constructor
      · change B.vertical x.1 + f.linear x.2 ∈ B.space p 0
        rw [show x.1=0 from hx.1,map_zero,zero_add]
        exact f.map_mem p 0 x.2 hx.2
      · exact (A.space _ _).neg_mem (A.vertical_mem p 0 x.2 hx.2)
    | succ q => exact ⟨(B.space _ _).add_mem (B.vertical_mem p q x.1 hx.1)
        (f.map_mem p (q+1) x.2 hx.2),(A.space _ _).neg_mem (A.vertical_mem p (q+1) x.2 hx.2)⟩
  horizontal_square x := by ext <;> simp [B.horizontal_square,A.horizontal_square]
  vertical_square x := by ext <;> simp [map_add,B.vertical_square,A.vertical_square,f.vertical_commute]
  commute x := by ext <;> simp [map_add,B.commute,A.commute,f.horizontal_commute]
  below p q hp := by
    cases q <;> ext x <;> simp [A.below p _ hp,B.below p _ hp]

@[simp] theorem columnCone_vertical (x : F × E) :
    f.columnCone.vertical x = (B.vertical x.1 + f.linear x.2,-A.vertical x.2) := rfl
@[simp] theorem columnCone_horizontal (x : F × E) :
    f.columnCone.horizontal x = (B.horizontal x.1,A.horizontal x.2) := rfl

 theorem columnCone_space_eq (p : ℤ) (q : ℕ) :
    (f.columnMap p).cone.space ((q:ℤ)-1) = f.columnCone.space p q := by
  cases q with
  | zero => ext x; simp [Map.cone,columnMap,Data.columnComplex,columnCone]
  | succ q =>
    have he : ((q+1:ℕ):ℤ)-1=(q:ℤ) := by omega
    rw [he]
    ext x
    simp [Map.cone,columnMap,Data.columnComplex,columnCone,show 0 ≤ (q:ℤ)+1 by omega]

 theorem columnCone_columns_exact
    (h : ∀ p n, Function.Bijective ((f.columnMap p).cohomologyMap n)) :
    (∀ p z, z ∈ f.columnCone.space p 0 → f.columnCone.vertical z=0 → z=0) ∧
    (∀ p q z, z ∈ f.columnCone.space p (q+1) → f.columnCone.vertical z=0 →
      ∃ y, y ∈ f.columnCone.space p q ∧ f.columnCone.vertical y=z) := by
  have hac (p : ℤ) : (f.columnMap p).cone.Acyclic :=
    (f.columnMap p).cone_acyclic_of_cohomologyMap_bijective (h p)
  constructor
  · intro p z hz hc
    have hm : z ∈ (f.columnMap p).cone.space (-1) := by
      have hs := f.columnCone_space_eq p 0
      norm_num at hs
      rwa [hs]
    obtain ⟨y,hy,he⟩ := hac p (-1) z hm hc
    have hy0 : y=0 := by
      change y.1 ∈ (B.columnComplex p).space (-2) ∧ y.2 ∈ (A.columnComplex p).space (-1) at hy
      have h1 : y.1=0 := by simpa [Data.columnComplex] using hy.1
      have h2 : y.2=0 := by simpa [Data.columnComplex] using hy.2
      exact Prod.ext h1 h2
    simpa only [hy0,map_zero] using he.symm
  · intro p q z hz hc
    have hm : z ∈ (f.columnMap p).cone.space (q:ℤ) := by
      rw [show (q:ℤ)=((q+1:ℕ):ℤ)-1 by omega,f.columnCone_space_eq p (q+1)]
      exact hz
    obtain ⟨y,hy,he⟩ := hac p (q:ℤ) z hm hc
    refine ⟨y,?_,he⟩
    rwa [f.columnCone_space_eq p q] at hy

private theorem sign_square (n : ℤ) : (-1:ℝ)^n * (-1:ℝ)^n = 1 := by
  rw [←mul_zpow]
  norm_num
private theorem sign_involutive (n : ℤ) (x : E) : (-1:ℝ)^n • ((-1:ℝ)^n • x) = x := by
  rw [smul_smul,sign_square,one_smul]
private theorem sign_next (n : ℤ) : (-1:ℝ)^(n+1) = -((-1:ℝ)^n) := by
  rw [zpow_add₀ (by norm_num),zpow_one]
  ring

/-- The concrete sign twist identifies the total of the shifted column cone
with the ordinary cone of the total map, shifted by one total degree. -/
def coneTwist (_f : DataMap A B) (n : ℤ) : (ℕ → F × E) →ₗ[ℝ] ((ℕ → F) × (ℕ → E)) where
  toFun x := (fun q => (x (q+1)).1,fun q => (-1:ℝ)^(n-q) • (x q).2)
  map_add' x y := by ext q <;> simp [smul_add]
  map_smul' r x := by ext q <;> simp [smul_comm r]

 theorem coneTwist_mem (n : ℤ) (x : f.columnCone.total n) :
    f.coneTwist n x.val ∈ f.totalMap.cone.space (n-1) := by
  constructor
  · intro q
    change (x.val (q+1)).1 ∈ B.space (n-1-q) q
    have h := (x.property (q+1)).1
    have he : n-((q+1:ℕ):ℤ)=n-1-q := by omega
    change (x.val (q+1)).1 ∈ B.space (n-((q+1:ℕ):ℤ)) q at h
    rwa [he] at h
  · have hn : n-1+1=n := by omega
    change (fun q : ℕ => (-1:ℝ)^(n-q) • (x.val q).2) ∈ A.total (n-1+1)
    rw [hn]
    intro q
    apply (A.space (n-q) q).smul_mem
    cases q with
    | zero => exact (x.property 0).2
    | succ q => exact (x.property (q+1)).2

 theorem coneTwist_injective (n : ℤ) (x : f.columnCone.total n)
    (he : f.coneTwist n x.val=0) : x.val=0 := by
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  funext q
  apply Prod.ext
  · cases q with
    | zero => exact (x.property 0).1
    | succ q => exact congrFun h1 q
  · have hq := congrFun h2 q
    change (-1:ℝ)^(n-q) • (x.val q).2 = 0 at hq
    exact (smul_eq_zero.mp hq).resolve_left (zpow_ne_zero _ (by norm_num))

 theorem coneTwist_surjective (n : ℤ) (z : f.totalMap.cone.space (n-1)) :
    ∃ x : f.columnCone.total n, f.coneTwist n x.val=z.val := by
  have hn : n-1+1=n := by omega
  have h1 : z.val.1 ∈ B.total (n-1) := z.property.1
  have h2 : z.val.2 ∈ A.total n := by
    have h := z.property.2
    change z.val.2 ∈ A.total (n-1+1) at h
    rwa [hn] at h
  let x : ℕ → F × E := fun q => match q with
    | 0 => (0,(-1:ℝ)^n • z.val.2 0)
    | q+1 => (z.val.1 q,(-1:ℝ)^(n-(q+1)) • z.val.2 (q+1))
  have hx : x ∈ f.columnCone.total n := by
    intro q
    cases q with
    | zero =>
      constructor
      · exact rfl
      · change (-1:ℝ)^n • z.val.2 0 ∈ A.space (n-0) 0
        exact (A.space _ _).smul_mem _ (h2 0)
    | succ q =>
      constructor
      · change z.val.1 q ∈ B.space (n-((q+1:ℕ):ℤ)) q
        have he : n-((q+1:ℕ):ℤ)=n-1-q := by omega
        rw [he]
        exact h1 q
      · exact (A.space _ _).smul_mem _ (h2 (q+1))
  refine ⟨⟨x,hx⟩,?_⟩
  apply Prod.ext
  · funext q
    rfl
  · funext q
    cases q <;> simp [coneTwist,x,sign_involutive]

/-- The sign twist intertwines the actual total and ordinary cone
coboundaries on every homogeneous element. -/
theorem coneTwist_commute (n : ℤ) (x : f.columnCone.total n) :
    f.coneTwist (n+1) (f.columnCone.differential n x.val) =
      f.totalMap.cone.differential (n-1) (f.coneTwist n x.val) := by
  have hn : n-1+1=n := by omega
  apply Prod.ext
  · funext q
    cases q with
    | zero =>
      change B.horizontal (x.val 1).1 + (-1:ℝ)^(n-0) • (B.vertical (x.val 0).1 + f.linear (x.val 0).2) =
        B.horizontal (x.val 1).1 + f.linear ((-1:ℝ)^(n-0) • (x.val 0).2)
      rw [show (x.val 0).1=0 from (x.property 0).1,map_zero,zero_add,map_smul]
    | succ q =>
      change B.horizontal (x.val (q+1+1)).1 + (-1:ℝ)^(n-(q+1)) •
        (B.vertical (x.val (q+1)).1 + f.linear (x.val (q+1)).2) =
        (B.horizontal (x.val (q+1+1)).1 + (-1:ℝ)^(n-1-q) • B.vertical (x.val (q+1)).1) +
          f.linear ((-1:ℝ)^(n-(q+1)) • (x.val (q+1)).2)
      have he : n-((q:ℤ)+1)=n-1-q := by omega
      rw [map_smul,smul_add]
      rw [he]
      abel
  · funext q
    cases q with
    | zero =>
      change (-1:ℝ)^(n+1-0) • A.horizontal (x.val 0).2 =
        -A.horizontal ((-1:ℝ)^(n-0) • (x.val 0).2)
      rw [map_smul]
      simp [sign_next]
    | succ q =>
      change (-1:ℝ)^(n+1-(q+1)) •
          (A.horizontal (x.val (q+1)).2 + (-1:ℝ)^(n-q) • (-A.vertical (x.val q).2)) =
        -(A.horizontal ((-1:ℝ)^(n-(q+1)) • (x.val (q+1)).2) +
          (-1:ℝ)^(n-1+1-q) • A.vertical ((-1:ℝ)^(n-q) • (x.val q).2))
      rw [hn]
      have he : n+1-((q:ℤ)+1)=n-q := by omega
      have hs : (-1:ℝ)^(n-q) = -((-1:ℝ)^(n-((q:ℤ)+1))) := by
        have ha : n-q=(n-((q:ℤ)+1))+1 := by omega
        rw [ha,sign_next]
      rw [he,map_smul,map_smul,smul_add,sign_involutive,sign_involutive]
      rw [hs]
      simp only [neg_smul,neg_add_rev]
      abel

/-- Columnwise quasi-isomorphisms induce total quasi-isomorphisms. The
column cohomology maps are the actual quotient maps; the shifted column cone
and its sign twist account for both lower bounds and the cone signs. -/
theorem totalMap_quasiIso
    (h : ∀ p n, Function.Bijective ((f.columnMap p).cohomologyMap n))
    (degree : ℤ) : Function.Bijective (f.totalMap.cohomologyMap degree) := by
  apply f.totalMap.cohomologyMap_bijective_of_cone_acyclic
  obtain ⟨hzero,hexact⟩ := f.columnCone_columns_exact h
  intro n z hz hc
  have hn : n+1-1=n := by omega
  have hzm : z ∈ f.totalMap.cone.space (n+1-1) := by rwa [hn]
  obtain ⟨x,hx⟩ := f.coneTwist_surjective (n+1) ⟨z,hzm⟩
  have hdx : f.columnCone.differential (n+1) x.val = 0 := by
    have hco := f.coneTwist_commute (n+1) x
    rw [hn,hx,hc] at hco
    exact f.coneTwist_injective (n+1+1)
      ⟨f.columnCone.differential (n+1) x.val,f.columnCone.differential_mem (n+1) x.property⟩ hco
  have hyex : ∃ y : f.columnCone.total n, f.columnCone.differential n y.val=x.val := by
    have hy := f.columnCone.total_exact_of_columns_exact hzero hexact (n+1) x hdx
    rw [hn] at hy
    exact hy
  obtain ⟨y,hy⟩ := hyex
  refine ⟨f.coneTwist n y.val,f.coneTwist_mem n y,?_⟩
  have hco := f.coneTwist_commute n y
  rw [hy,hx] at hco
  exact hco.symm

/-- The omitted columns in negative horizontal degrees are automatically
zero complexes, hence impose no additional assumption. -/
theorem columnMap_quasiIso_of_negative (p : ℤ) (hp : p<0) (n : ℤ) :
    Function.Bijective ((f.columnMap p).cohomologyMap n) := by
  apply (f.columnMap p).cohomologyMap_bijective_of_cone_acyclic
  intro k x hx hc
  have h1 : x.1=0 := by
    have hx1 : x.1 ∈ (B.columnComplex p).space k := hx.1
    by_cases hk : 0 ≤ k
    · simpa [Data.columnComplex,hk,B.below p _ hp] using hx1
    · simpa [Data.columnComplex,hk] using hx1
  have h2 : x.2=0 := by
    have hx2 : x.2 ∈ (A.columnComplex p).space (k+1) := hx.2
    by_cases hk : 0 ≤ k+1
    · simpa [Data.columnComplex,hk,A.below p _ hp] using hx2
    · simpa [Data.columnComplex,hk] using hx2
  refine ⟨0,((f.columnMap p).cone.space (k-1)).zero_mem,?_⟩
  rw [map_zero]
  exact (Prod.ext h1 h2).symm

/-- It suffices to assume quasi-isomorphisms in the original nonnegative
vertical columns. There is no finiteness restriction on the modules. -/
theorem totalMap_quasiIso_of_nonnegative_columns
    (h : ∀ p : ℕ, ∀ n, Function.Bijective ((f.columnMap (p:ℤ)).cohomologyMap n))
    (degree : ℤ) : Function.Bijective (f.totalMap.cohomologyMap degree) := by
  apply f.totalMap_quasiIso
  intro p n
  by_cases hp : 0 ≤ p
  · have he : (p.toNat:ℤ)=p := by omega
    have hm := h p.toNat n
    rw [he] at hm
    exact hm
  · exact f.columnMap_quasiIso_of_negative p (by omega) n

end DataMap
end P202.CochainCoverDescent.TotalAlgebra

namespace P202.CochainCoverDescent.TotalAlgebra.GridEmbedding
universe u v
variable {C : ℕ → ℕ → Type u} {D : ℕ → ℕ → Type v}
  [∀ p q, AddCommGroup (C p q)] [∀ p q, Module ℝ (C p q)]
  [∀ p q, AddCommGroup (D p q)] [∀ p q, Module ℝ (D p q)]

/-- A completely arbitrary family of bidegree maps acts coordinatewise on
the canonical product ambient spaces. -/
def mapAmbient (f : ∀ p q, C p q →ₗ[ℝ] D p q) : Ambient C →ₗ[ℝ] Ambient D where
  toFun x p q := f p q (x p q)
  map_add' _ _ := by funext p q; exact map_add _ _ _
  map_smul' _ _ := by funext p q; exact map_smul _ _ _

theorem mapAmbient_embed (f : ∀ p q, C p q →ₗ[ℝ] D p q)
    (p q : ℕ) (z : C p q) :
    mapAmbient f (embed C p q z) = embed D p q (f p q z) := by
  funext r s
  by_cases hr : r=p
  · subst r
    by_cases hs : s=q
    · subst s; simp [mapAmbient]
    · simp [mapAmbient,hs]
  · simp [mapAmbient,hr]

/-- The common ambient model represents every map of arbitrary dependent
bigraded vector-space families; no equality of their bidegree types is assumed. -/
def dataMap
    (hC : ∀ p q, C p q →ₗ[ℝ] C (p+1) q)
    (vC : ∀ p q, C p q →ₗ[ℝ] C p (q+1))
    (hhC : ∀ p q z, hC (p+1) q (hC p q z)=0)
    (vvC : ∀ p q z, vC p (q+1) (vC p q z)=0)
    (commC : ∀ p q z, hC p (q+1) (vC p q z)=vC (p+1) q (hC p q z))
    (hD : ∀ p q, D p q →ₗ[ℝ] D (p+1) q)
    (vD : ∀ p q, D p q →ₗ[ℝ] D p (q+1))
    (hhD : ∀ p q z, hD (p+1) q (hD p q z)=0)
    (vvD : ∀ p q z, vD p (q+1) (vD p q z)=0)
    (commD : ∀ p q z, hD p (q+1) (vD p q z)=vD (p+1) q (hD p q z))
    (f : ∀ p q, C p q →ₗ[ℝ] D p q)
    (fh : ∀ p q z, hD p q (f p q z)=f (p+1) q (hC p q z))
    (fv : ∀ p q z, vD p q (f p q z)=f p (q+1) (vC p q z)) :
    DataMap (data C hC vC hhC vvC commC) (data D hD vD hhD vvD commD) where
  linear := mapAmbient f
  map_mem p q x hx := by
    change x ∈ space C p q at hx
    change mapAmbient f x ∈ space D p q
    by_cases hp : 0 ≤ p
    · rw [space,if_pos hp] at hx ⊢
      obtain ⟨z,rfl⟩ := hx
      rw [mapAmbient_embed]
      exact ⟨f p.toNat q z,rfl⟩
    · rw [space,if_neg hp] at hx
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact (space D p q).zero_mem
  horizontal_commute x := by
    funext p q
    cases p with
    | zero => exact (f 0 q).map_zero.symm
    | succ p => exact fh p q (x p q)
  vertical_commute x := by
    funext p q
    cases q with
    | zero => exact (f p 0).map_zero.symm
    | succ q => exact fv p q (x p q)

end P202.CochainCoverDescent.TotalAlgebra.GridEmbedding

namespace P202.CochainCoverDescent
universe u v

theorem columnTotalComparison_conditional
    (_comparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    P202Specs.CochainCoverDescent.columnTotalComparison_type.{u,v} := by
  intro E F _ _ _ _ A B f h degree
  exact f.totalMap_quasiIso_of_nonnegative_columns h degree

end P202.CochainCoverDescent

namespace P202.CochainCoverDescent.CechTotals
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
open P202Specs.CochainCoverDescent P202.CochainCoverDescent.TotalAlgebra
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S}
  {B : ∀ q, FormBundle C q}

private theorem negative_one_cancel {E : Type*} [AddCommGroup E] [Module ℝ E] (x : E) :
    -((-1 : ℝ) • x) = x := by
  rw [neg_one_smul, neg_neg]

/-- The source of the actual smooth-form total augmentation is the original
space of global forms, in the original calculus. -/
def formGlobalAugmentationEquiv (K : DeRhamData.Calculus C B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ) :
    K.forms q ≃ₗ[ℝ] (formData C B U).augmentationComplex.space (q : ℤ) :=
  (Augmentation.formAugmentationEquiv K U q).symm.trans
    ((GridEmbedding.spaceEquiv (fun p q => FormRow (B q) U p) 0 q).trans
      (LinearEquiv.ofEq _ _ (by
        simp only [Data.augmentationComplex, if_pos (Int.natCast_nonneg q), Int.toNat_natCast]
        rfl)))

@[simp] theorem formGlobalAugmentationEquiv_val (K : DeRhamData.Calculus C B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ) (ω : K.forms q) :
    (formGlobalAugmentationEquiv K U q ω).val =
      GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 q
        ((Augmentation.formAugmentationEquiv K U q).symm ω) := rfl

/-- On the actual zero-th coordinate column, the stored augmentation
complex differential is exactly exterior differentiation. -/
theorem formData_augmentation_d_embed {ι : Type v} (U : ι → TopologicalSpace.Opens M)
    (q : ℕ) (f : FormRow (B q) U 0) :
    (formData C B U).augmentationComplex.differential (q : ℤ)
      (GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 q f) =
    GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 (q+1) (formV C B U q 0 f) := by
  simp only [Data.augmentationComplex, if_pos (Int.natCast_nonneg q), LinearMap.neg_apply]
  change -(GridEmbedding.vertical (fun p q => FormRow (B q) U p)
      (fun p q => (-1 : ℝ) • formV C B U q p)
      (GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 q f)) = _
  have hvertical := GridEmbedding.vertical_embed (fun p q => FormRow (B q) U p)
    (fun p q => (-1 : ℝ) • formV C B U q p) 0 q f
  have hscale := (GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 (q+1)).map_smul
    (-1 : ℝ) (formV C B U q 0 f)
  apply (congrArg Neg.neg hvertical).trans
  apply (congrArg Neg.neg hscale).trans
  let z := GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 (q+1) (formV C B U q 0 f)
  funext r s t
  apply Subtype.ext
  funext x
  change -((-1 : ℝ) • (z r s t).val x) = (z r s t).val x
  exact negative_one_cancel _

/-- Under this genuine source identification the augmentation differential
is precisely the original exterior derivative. -/
theorem formGlobalAugmentationEquiv_d (K : DeRhamData.Calculus C B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ) (ω : K.forms q) :
    (formData C B U).augmentationComplex.differential (q : ℤ)
        (formGlobalAugmentationEquiv K U q ω).val =
      (formGlobalAugmentationEquiv K U (q+1) (K.d q ω)).val := by
  let row := (Augmentation.formAugmentationEquiv K U q).symm ω
  have hrow : formV C B U q 0 row =
      (Augmentation.formAugmentationEquiv K U (q+1)).symm (K.d q ω) := by
    apply (Augmentation.formAugmentationEquiv K U (q+1)).injective
    exact (Augmentation.formAugmentationEquiv_d K U q row).trans
      ((congrArg (K.d q) ((Augmentation.formAugmentationEquiv K U q).apply_symm_apply ω)).trans
        ((Augmentation.formAugmentationEquiv K U (q+1)).apply_symm_apply (K.d q ω)).symm)
  calc
    _ = (formData C B U).augmentationComplex.differential (q : ℤ)
        (GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 q row) :=
      congrArg ((formData C B U).augmentationComplex.differential (q : ℤ))
        (formGlobalAugmentationEquiv_val K U q ω)
    _ = GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 (q+1)
        (formV C B U q 0 row) := formData_augmentation_d_embed U q row
    _ = GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 (q+1)
        ((Augmentation.formAugmentationEquiv K U (q+1)).symm (K.d q ω)) :=
      congrArg (GridEmbedding.embed (fun p q => FormRow (B q) U p) 0 (q+1)) hrow
    _ = (formGlobalAugmentationEquiv K U (q+1) (K.d q ω)).val :=
      (formGlobalAugmentationEquiv_val K U (q+1) (K.d q ω)).symm

/-- The source of the smooth-cochain total augmentation is the full
algebraic dual of the literal cover-small smooth chain submodule. -/
def cochainGlobalAugmentationEquiv (S : AtlasData.SmoothManifold n a M)
    {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ) :
    (smallSmoothModule S U q →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (cochainData S U).augmentationComplex.space (q : ℤ) :=
  (P202Specs.CochainCoverDescent.augmentationEquiv S U q).symm.trans
    ((GridEmbedding.spaceEquiv (fun p q => IntersectionCochainRow S U q p) 0 q).trans
      (LinearEquiv.ofEq _ _ (by
        simp only [Data.augmentationComplex, if_pos (Int.natCast_nonneg q), Int.toNat_natCast]
        rfl)))

@[simp] theorem cochainGlobalAugmentationEquiv_val (S : AtlasData.SmoothManifold n a M)
    {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ)
    (f : smallSmoothModule S U q →ₗ[ℝ] ℝ) :
    (cochainGlobalAugmentationEquiv S U q f).val =
      GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 q
        ((P202Specs.CochainCoverDescent.augmentationEquiv S U q).symm f) := rfl

/-- The actual augmentation differential is the ordinary smooth singular
coboundary, as transported through the already established basis/dual
augmentation equivalence. -/
theorem cochainGlobalAugmentationEquiv_d (S : AtlasData.SmoothManifold n a M)
    {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ)
    (f : smallSmoothModule S U q →ₗ[ℝ] ℝ) :
    (cochainData S U).augmentationComplex.differential (q : ℤ)
        (cochainGlobalAugmentationEquiv S U q f).val =
      (cochainGlobalAugmentationEquiv S U (q+1)
        (P202Specs.CochainCoverDescent.augmentationEquiv S U (q+1)
          (intersectionV S U q 0
            ((P202Specs.CochainCoverDescent.augmentationEquiv S U q).symm f)))).val := by
  rw [cochainGlobalAugmentationEquiv_val, cochainGlobalAugmentationEquiv_val]
  change (if 0 ≤ (q : ℤ) then
      -GridEmbedding.vertical (fun p q => IntersectionCochainRow S U q p)
        (fun p q => (-1 : ℝ) • intersectionV S U q p) else 0)
      (GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 q
        ((P202Specs.CochainCoverDescent.augmentationEquiv S U q).symm f)) = _
  rw [if_pos (Int.natCast_nonneg q), LinearMap.neg_apply, GridEmbedding.vertical_embed]
  simp only [LinearMap.smul_apply]
  rw [map_smul]
  simp only [LinearEquiv.symm_apply_apply]
  exact negative_one_cancel _

end P202.CochainCoverDescent.CechTotals

universe v8_closure_3a441764324fbfc4_u0 v8_closure_3a441764324fbfc4_u1
theorem _root_.«P202».«CochainCoverDescent».«alternatingFormula» : _root_.«P202Specs».«CochainCoverDescent».«alternatingFormula_type».{v8_closure_3a441764324fbfc4_u0} :=
  @_root_.«P202».«CochainCoverDescent».«alternatingFormula_conditional».{v8_closure_3a441764324fbfc4_u0} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«cochainBicomplex» : _root_.«P202Specs».«CochainCoverDescent».«cochainBicomplex_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«cochainBicomplex_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«cochainTotalAugmentation» : _root_.«P202Specs».«CochainCoverDescent».«cochainTotalAugmentation_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«cochainTotalAugmentation_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«columnTotalComparison» : _root_.«P202Specs».«CochainCoverDescent».«columnTotalComparison_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«columnTotalComparison_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«evaluatedCochainRowsExact» : _root_.«P202Specs».«CochainCoverDescent».«evaluatedCochainRowsExact_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«evaluatedCochainRowsExact_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«formsAugmentation» : _root_.«P202Specs».«CochainCoverDescent».«formsAugmentation_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«formsAugmentation_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«formsBicomplex» : _root_.«P202Specs».«CochainCoverDescent».«formsBicomplex_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«formsBicomplex_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«formsRowsExact» : _root_.«P202Specs».«CochainCoverDescent».«formsRowsExact_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«formsRowsExact_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«formsTotalAugmentation» : _root_.«P202Specs».«CochainCoverDescent».«formsTotalAugmentation_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«formsTotalAugmentation_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«intersectionAlternatingFormula» : _root_.«P202Specs».«CochainCoverDescent».«intersectionAlternatingFormula_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«intersectionAlternatingFormula_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«intersectionRowsExact» : _root_.«P202Specs».«CochainCoverDescent».«intersectionRowsExact_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«intersectionRowsExact_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«productRowsExact» : _root_.«P202Specs».«CochainCoverDescent».«productRowsExact_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«productRowsExact_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
theorem _root_.«P202».«CochainCoverDescent».«productsPreserveExactness» : _root_.«P202Specs».«CochainCoverDescent».«productsPreserveExactness_type».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} :=
  @_root_.«P202».«CochainCoverDescent».«productsPreserveExactness_conditional».{v8_closure_3a441764324fbfc4_u0, v8_closure_3a441764324fbfc4_u1} (@_root_.«P202».«SmoothSingularComparison».«smoothSingularComparison».{v8_closure_3a441764324fbfc4_u0})
