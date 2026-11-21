import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.EulerPoincare
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularComparison
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring

/-! Euler--Poincaré for the actual cellular complex. The algebraic argument
uses rank-nullity and the quotient of cycles by boundaries; the comparison
isomorphism then identifies this homology with singular homology. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202.Cellular P202Specs.SingularChains P202Specs.CellularChains
open P202Specs.EulerPoincare
universe u v w
namespace P202.Homology.EulerPoincare
section Algebra
variable {F : Type u} [Field F]
variable (S : ShortComplex (ModuleCat.{v} F)) [FiniteDimensional F S.X₂]

lemma shortComplexHomologyFinite : FiniteDimensional F S.homology := by
  let e := (CategoryTheory.Iso.toLinearEquiv S.moduleCatHomologyIso)
  haveI : FiniteDimensional F S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional F (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact e.symm.finiteDimensional

lemma shortComplexDimension :
    Module.finrank F S.X₂ = Module.finrank F S.homology +
      Module.finrank F (LinearMap.range S.f.hom) +
      Module.finrank F (LinearMap.range S.g.hom) := by
  let e := CategoryTheory.Iso.toLinearEquiv S.moduleCatHomologyIso
  have hq := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hg := S.g.hom.finrank_range_add_finrank_ker
  have hb : Module.finrank F (LinearMap.range S.moduleCatToCycles) =
      Module.finrank F (LinearMap.range S.f.hom) := by
    have hcomp : (LinearMap.ker S.g.hom).subtype.comp S.moduleCatToCycles = S.f.hom := rfl
    rw [← hcomp, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective (LinearMap.ker S.g.hom).subtype
      (Submodule.injective_subtype _) (LinearMap.range S.moduleCatToCycles)).finrank_eq
  have he := e.finrank_eq
  change Module.finrank F S.homology = Module.finrank F
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at he
  rw [← he, hb] at hq
  omega

variable (K : ChainComplex (ModuleCat.{v} F) ℕ)

def outgoingRank (n : ℕ) : ℕ := match n with
  | 0 => 0
  | n+1 => Module.finrank F (LinearMap.range (K.d (n+1) n).hom)

lemma chainDimension [∀ n, FiniteDimensional F (K.X n)] (n : ℕ) :
    Module.finrank F (K.X n) = Module.finrank F (K.homology n) +
      outgoingRank K (n+1) + outgoingRank K n := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  haveI : FiniteDimensional F (K.sc n).X₂ := by
    change FiniteDimensional F (K.X n)
    infer_instance
  have hh := shortComplexDimension (K.sc n)
  change Module.finrank F (K.X n) = Module.finrank F (K.homology n) +
    Module.finrank F (LinearMap.range (K.d ((ComplexShape.down ℕ).prev n) n).hom) +
    Module.finrank F (LinearMap.range (K.d n ((ComplexShape.down ℕ).next n)).hom) at hh
  rw [hp] at hh
  cases n with
  | zero =>
    have hn : (ComplexShape.down ℕ).next 0 = 0 := by
      apply ComplexShape.next_eq_self'
      intro j hj
      change j + 1 = 0 at hj
      omega
    rw [hn, K.shape 0 0 (by simp)] at hh
    rw [ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot, add_zero] at hh
    exact hh
  | succ n =>
    have hn : (ComplexShape.down ℕ).next (n+1) = n :=
      ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
    rw [hn] at hh
    exact hh

lemma alternatingTelescope (c h r : ℕ → ℤ)
    (hdim : ∀ n, c n = h n + r (n+1) + r n) (N : ℕ) :
    (∑ n ∈ Finset.range N, (-1 : ℤ)^n * c n) + (-1 : ℤ)^N * r N =
      (∑ n ∈ Finset.range N, (-1 : ℤ)^n * h n) + r 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, pow_succ]
    rw [hdim N]
    calc
      _ = ((∑ n ∈ Finset.range N, (-1 : ℤ)^n * c n) + (-1 : ℤ)^N * r N) +
        (-1 : ℤ)^N * h N := by ring
      _ = _ := by rw [ih]; ring

/-- Cancellation of boundary dimensions, including the bottom degree and
an empty index range. The top boundary vanishes because its source is zero. -/
lemma chainEulerFiniteSum [∀ n, FiniteDimensional F (K.X n)] (N : ℕ)
    (hz : IsZero (K.X N)) :
    (∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Module.finrank F (K.X n) : ℤ)) =
      ∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Module.finrank F (K.homology n) : ℤ) := by
  have hr : outgoingRank K N = 0 := by
    cases N with
    | zero => rfl
    | succ N =>
      haveI := ModuleCat.subsingleton_of_isZero hz
      have hh := (K.d (N+1) N).hom.finrank_range_le
      have hzero : Module.finrank F (K.X (N+1)) = 0 :=
        Module.finrank_zero_of_subsingleton
      exact Nat.eq_zero_of_le_zero (hzero ▸ hh)
  have hd (n : ℕ) : (Module.finrank F (K.X n) : ℤ) =
      (Module.finrank F (K.homology n) : ℤ) +
        (outgoingRank K (n+1) : ℤ) + (outgoingRank K n : ℤ) := by
    exact_mod_cast chainDimension K n
  have ht := alternatingTelescope
    (fun n => (Module.finrank F (K.X n) : ℤ))
    (fun n => (Module.finrank F (K.homology n) : ℤ))
    (fun n => (outgoingRank K n : ℤ)) hd N
  change (∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Module.finrank F (K.X n) : ℤ)) +
      (-1 : ℤ)^N * (outgoingRank K N : ℤ) =
      (∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Module.finrank F (K.homology n) : ℤ)) +
        (outgoingRank K 0 : ℤ) at ht
  rw [hr, show outgoingRank K 0 = 0 from rfl] at ht
  simpa only [Nat.cast_zero, mul_zero, add_zero] using ht

end Algebra

section Cells
variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (F : Type u) [Field F]

lemma cellsFinite [Finite (Σ n, Cell X n)] (n : ℕ) : Finite (Cell X n) :=
  Finite.of_injective (fun c : Cell X n => (⟨n, c⟩ : Σ m, Cell X m))
    (fun a b h => by simpa using h)

lemma cellsBounded [Finite (Σ n, Cell X n)] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsEmpty (Cell X n) := by
  classical
  letI := Fintype.ofFinite (Σ n, Cell X n)
  refine ⟨Finset.univ.sup (fun d : Σ n, Cell X n => d.1) + 1, ?_⟩
  intro n hn
  refine ⟨fun c => ?_⟩
  have hc : n ≤ Finset.univ.sup (fun d : Σ n, Cell X n => d.1) :=
    Finset.le_sup (f := fun d : Σ n, Cell X n => d.1) (Finset.mem_univ ⟨n,c⟩)
  omega

lemma cellularFinite [Finite (Cell X n)] :
    FiniteDimensional F ((cellularComplex X F F).X n) := by
  let e : (cellularComplex X F F).X n ≃ₗ[F] (Cell X n →₀ F) :=
    Classical.choice (P202.Homology.cellularCellGroups X F F n)
  exact e.symm.finiteDimensional

lemma cellularFinrank [Finite (Cell X n)] :
    Module.finrank F ((cellularComplex X F F).X n) = Nat.card (Cell X n) := by
  classical
  letI := Fintype.ofFinite (Cell X n)
  let e : (cellularComplex X F F).X n ≃ₗ[F] (Cell X n →₀ F) :=
    Classical.choice (P202.Homology.cellularCellGroups X F F n)
  rw [e.finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

lemma cellularZero (n : ℕ) [IsEmpty (Cell X n)] :
    IsZero ((cellularComplex X F F).X n) := by
  let e : (cellularComplex X F F).X n ≃ₗ[F] (Cell X n →₀ F) :=
    Classical.choice (P202.Homology.cellularCellGroups X F F n)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

lemma singularZero (n : ℕ) [IsEmpty (Cell X n)] :
    IsZero (homology F F (TopCat.of X) (n : ℤ)) := by
  have hc := HomologicalComplex.ExactAt.of_isZero (K := cellularComplex X F F)
    (cellularZero X F n)
  exact (P202.Homology.CellularComparison.comparisonIso X F F n).isZero_iff.mp
    hc.isZero_homology

lemma singularFinite [Finite (Cell X n)] :
    FiniteDimensional F (homology F F (TopCat.of X) (n : ℤ)) := by
  haveI : FiniteDimensional F ((cellularComplex X F F).X n) := cellularFinite X F
  haveI : FiniteDimensional F ((cellularComplex X F F).sc n).X₂ := cellularFinite X F
  haveI : FiniteDimensional F ((cellularComplex X F F).homology n) :=
    shortComplexHomologyFinite ((cellularComplex X F F).sc n)
  exact (P202.Homology.CellularComparison.comparisonIso X F F n).toLinearEquiv.finiteDimensional

lemma finiteType [Finite (Σ n, Cell X n)] : HomologyFiniteType F X := by
  haveI := fun n => cellsFinite X n
  constructor
  · intro n
    exact singularFinite X F
  · obtain ⟨N, hN⟩ := cellsBounded X
    refine ⟨N, fun n hn => ?_⟩
    haveI := hN n hn
    exact singularZero X F n

omit [CWStructure X] in
lemma homologicalSum (N : ℕ)
    (hz : ∀ n : ℕ, N ≤ n → IsZero (homology F F (TopCat.of X) (n : ℤ))) :
    homologicalEuler F X = ∑ n ∈ Finset.range N,
      (-1 : ℤ)^n * (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ) := by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra h
  have hnN : N ≤ n := by simpa using h
  haveI := ModuleCat.subsingleton_of_isZero (hz n hnN)
  exact hn (by simp [Module.finrank_zero_of_subsingleton])

lemma cellSum (N : ℕ) (hz : ∀ n : ℕ, N ≤ n → IsEmpty (Cell X n)) :
    cellEuler X = ∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ) := by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra h
  have hnN : N ≤ n := by simpa using h
  haveI := hz n hnN
  exact hn (by simp)

/-- Cell ranks and homology ranks have equal alternating sums on any
finite interval containing all cell dimensions. -/
lemma cellularEulerFiniteSum [Finite (Σ n, Cell X n)] (N : ℕ)
    (hz : ∀ n : ℕ, N ≤ n → IsEmpty (Cell X n)) :
    (∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ)) =
      ∑ n ∈ Finset.range N, (-1 : ℤ)^n *
        (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ) := by
  haveI := fun n => cellsFinite X n
  haveI := fun n => cellularFinite X F (n := n)
  haveI := hz N le_rfl
  have ht := chainEulerFiniteSum (cellularComplex X F F) N (cellularZero X F N)
  calc
    _ = ∑ n ∈ Finset.range N, (-1 : ℤ)^n *
        (Module.finrank F ((cellularComplex X F F).X n) : ℤ) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [cellularFinrank X F]
    _ = _ := ht
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [(P202.Homology.CellularComparison.comparisonIso X F F n).toLinearEquiv.finrank_eq]

lemma cellEuler_eq_homologicalEuler [Finite (Σ n, Cell X n)] :
    cellEuler X = homologicalEuler F X := by
  obtain ⟨N, hN⟩ := cellsBounded X
  rw [cellSum X N hN, homologicalSum X F N (fun n hn => by
    haveI := hN n hn
    exact singularZero X F n)]
  exact cellularEulerFiniteSum X F N hN

end Cells
/-- The canonical integer invariant requires a rational finite-type certificate. -/
def eulerCharacteristic : Expected.eulerCharacteristic_type.{w} :=
  Expected.eulerCharacteristic_value

theorem finiteSumFormula :
  ∀ (F : Type u) [Field F] (X : Type w) [TopologicalSpace X]
    (_h : HomologyFiniteType F X) (N : ℕ),
    (∀ n : ℕ, N ≤ n → IsZero (homology F F (TopCat.of X) (n : ℤ))) →
    homologicalEuler F X = ∑ n ∈ Finset.range N,
      (-1 : ℤ)^n * (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ) := by
  intro F _ X _ _ N hz
  exact homologicalSum X F N hz

theorem finiteCWFiniteType :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F], HomologyFiniteType F X := by
  intro X _ _ hfin F _
  letI := hfin
  exact finiteType X F

theorem eulerPoincare :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F],
    ∃ hQ : HomologyFiniteType ℚ X,
      HomologyFiniteType F X ∧ topologicalEuler X hQ = cellEuler X ∧
      cellEuler X = homologicalEuler F X := by
  intro X _ _ hfin F _
  letI := hfin
  refine ⟨finiteType X ℚ, finiteType X F, ?_, cellEuler_eq_homologicalEuler X F⟩
  exact (cellEuler_eq_homologicalEuler X ℚ).symm

theorem finiteCWFormula :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F] (N : ℕ),
    (∀ n : ℕ, N ≤ n → IsEmpty (Cell X n)) →
    ∃ hQ : HomologyFiniteType ℚ X,
      topologicalEuler X hQ = ∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ) ∧
      (∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ)) =
        ∑ n ∈ Finset.range N, (-1 : ℤ)^n *
          (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ) := by
  intro X _ _ hfin F _ N hz
  letI := hfin
  refine ⟨finiteType X ℚ, ?_, cellularEulerFiniteSum X F N hz⟩
  exact (cellEuler_eq_homologicalEuler X ℚ).symm.trans (cellSum X N hz)

theorem structureIndependence :
  ∀ (X : Type w) [t : TopologicalSpace X] (s₁ s₂ : CWStructure X),
    Finite (Σ n, @Cell X t s₁.toCellStructure n) →
    Finite (Σ n, @Cell X t s₂.toCellStructure n) →
    @cellEuler X t s₁.toCellStructure = @cellEuler X t s₂.toCellStructure := by
  intro X t s₁ s₂ h₁ h₂
  have e₁ : @cellEuler X t s₁.toCellStructure = homologicalEuler ℚ X := by
    letI := s₁
    letI := h₁
    exact cellEuler_eq_homologicalEuler X ℚ
  have e₂ : @cellEuler X t s₂.toCellStructure = homologicalEuler ℚ X := by
    letI := s₂
    letI := h₂
    exact cellEuler_eq_homologicalEuler X ℚ
  exact e₁.trans e₂.symm

theorem fieldIndependence :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F] (K : Type v) [Field K],
      homologicalEuler F X = homologicalEuler K X := by
  intro X _ _ hfin F _ K _
  letI := hfin
  exact (cellEuler_eq_homologicalEuler X F).symm.trans (cellEuler_eq_homologicalEuler X K)

theorem graphFormula :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → (∀ n : ℕ, 2 ≤ n → IsEmpty (Cell X n)) →
    ∃ hQ : HomologyFiniteType ℚ X,
      topologicalEuler X hQ = (Nat.card (Cell X 0) : ℤ) - (Nat.card (Cell X 1) : ℤ) := by
  intro X _ _ hfin hz
  letI := hfin
  refine ⟨finiteType X ℚ, ?_⟩
  calc
    topologicalEuler X _ = cellEuler X := (cellEuler_eq_homologicalEuler X ℚ).symm
    _ = _ := cellSum X 2 hz
    _ = _ := by simp [Finset.sum_range_succ, sub_eq_add_neg]

theorem zeroDimensionalFormula :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → (∀ n : ℕ, 1 ≤ n → IsEmpty (Cell X n)) →
    ∃ hQ : HomologyFiniteType ℚ X, topologicalEuler X hQ = (Nat.card (Cell X 0) : ℤ) := by
  intro X _ _ hfin hz
  letI := hfin
  refine ⟨finiteType X ℚ, ?_⟩
  calc
    topologicalEuler X _ = cellEuler X := (cellEuler_eq_homologicalEuler X ℚ).symm
    _ = _ := cellSum X 1 hz
    _ = _ := by simp

theorem emptyFormula :
  ∀ (X : Type w) [TopologicalSpace X] [IsEmpty X],
    ∃ hQ : HomologyFiniteType ℚ X, topologicalEuler X hQ = 0 := by
  intro X _ _
  have hz (n : ℕ) : IsZero (homology ℚ ℚ (TopCat.of X) (n : ℤ)) :=
    P202.SingularDegreeZero.emptyOrdinary ℚ ℚ (TopCat.of X) n
  have hQ : HomologyFiniteType ℚ X := by
    constructor
    · intro n
      haveI := ModuleCat.subsingleton_of_isZero (hz n)
      infer_instance
    · exact ⟨0, fun n _ => hz n⟩
  refine ⟨hQ, ?_⟩
  exact homologicalSum X ℚ 0 (fun n _ => hz n) |>.trans (by simp)

end P202.Homology.EulerPoincare

