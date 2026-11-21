import MathGenome.Internal.Specs.D07.Ch19.ResultantSpecialization
import MathGenome.Internal.D07.Ch19.ResultantBezout
import MathGenome.Internal.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
import Mathlib.Tactic.FinCases

universe u v w
namespace D07.Ch19.ResultantSpecialization
open Polynomial
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantSpecialization

theorem coefficientHomomorphism : CoefficientHomomorphism.{u,v} := by
  intro R S _ _ φ f g n m hf hg
  exact ResultantBezout.fixedResultant_map φ f g n m hf hg

theorem necessaryElimination : NecessaryElimination.{u,v} :=
  ResultantBezout.necessaryElimination

/-- The product over the full multiset of roots supplies a common root whenever
f retains its positive specified degree. In particular g need not be nonzero. -/
lemma commonRoot_of_left_degree {K : Type v} {L : Type w}
    [Field K] [Field L] [Algebra K L] (f g : K[X]) (n m : ℕ)
    (hn : 0 < n) (hf : f.natDegree = n) (hg : g.natDegree ≤ m)
    (hs : (f.map (algebraMap K L)).Splits)
    (hr : fixedResultant f g n m = 0) :
    ∃ x : L, aeval x f = 0 ∧ aeval x g = 0 := by
  have hf0 : f ≠ 0 := by
    intro hz
    simp [hz] at hf
    omega
  have hprod := ResultantProductDiscriminantPaddedRootProduct.paddedRootProduct K L f g n m
    hf0 hf hn hg hs
  rw [hr, map_zero] at hprod
  have ha : algebraMap K L f.leadingCoeff ^ m ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero (algebraMap K L)).mpr (leadingCoeff_ne_zero.mpr hf0))
  have hz : ((f.map (algebraMap K L)).roots.map (fun a => aeval a g)).prod = 0 :=
    (mul_eq_zero.mp hprod.symm).resolve_left ha
  obtain ⟨x, hx, hgx⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
  refine ⟨x, ?_, hgx⟩
  simpa [IsRoot, eval_map, aeval_def] using Polynomial.isRoot_of_mem_roots hx

theorem splittingFieldCriterion : SplittingFieldCriterion.{u,v,w} := by
  intro R K L _ _ _ _ φ f g n m hf hg hguard
  have hfn : (f.map φ).natDegree ≤ n :=
    natDegree_map_le.trans (natDegree_le_of_degree_le hf)
  have hgn : (g.map φ).natDegree ≤ m :=
    natDegree_map_le.trans (natDegree_le_of_degree_le hg)
  constructor
  · intro hr
    have hr' : fixedResultant (f.map φ) (g.map φ) n m = 0 := by
      rw [coefficientHomomorphism R K φ f g n m hf hg, hr]
    rcases hguard with ⟨hn, hfn', hs⟩ | ⟨hm, hgn', hs⟩
    · exact commonRoot_of_left_degree (f.map φ) (g.map φ) n m hn hfn' hgn hs hr'
    · have hswap : fixedResultant (g.map φ) (f.map φ) m n = 0 := by
        rw [ResultantDefinition.swapSign K (f.map φ) (g.map φ) n m hfn hgn, hr', mul_zero]
      obtain ⟨x, hgx, hfx⟩ :=
        commonRoot_of_left_degree (g.map φ) (f.map φ) m n hm hgn' hfn hs hswap
      exact ⟨x, hfx, hgx⟩
  · rintro ⟨x, hfx, hgx⟩
    have hpos : 0 < n + m := by
      rcases hguard with ⟨hn, _⟩ | ⟨hm, _⟩ <;> omega
    have hz := necessaryElimination R L ((algebraMap K L).comp φ) f g n m x hf hg hpos
      (by simpa [Polynomial.map_map, eval_map, aeval_def, eval₂_map] using hfx)
      (by simpa [Polynomial.map_map, eval_map, aeval_def, eval₂_map] using hgx)
    exact (algebraMap K L).injective (by simpa using hz)

theorem algebraicClosureCriterion : AlgebraicClosureCriterion.{u,v,w} := by
  intro R K L _ _ _ _ _ φ f g n m hf hg hguard
  apply splittingFieldCriterion R K L φ f g n m hf hg
  rcases hguard with ⟨hn, hfn⟩ | ⟨hm, hgn⟩
  · exact Or.inl ⟨hn, hfn, IsAlgClosed.splits _⟩
  · exact Or.inr ⟨hm, hgn, IsAlgClosed.splits _⟩

theorem emptyDeterminant : Specs.D07.Ch19.ResultantSpecialization.EmptyDeterminant.{u} := by
  intro R _ f g
  exact ⟨ResultantDefinition.emptyDeterminant R f g,
    ResultantDefinition.emptyDeterminant R 0 0⟩

theorem degreeDropCounterexample : DegreeDropCounterexample.{u} := by
  let f : ℚ[X][X] := C X * X + 1
  let g : ℚ[X][X] := C X * X + C 2
  let φ : ℚ[X] →+* ℚ := evalRingHom 0
  change f.natDegree = 1 ∧ g.natDegree = 1 ∧ _
  have hfn : f.natDegree = 1 := by simp [f]
  have hgn : g.natDegree = 1 := by simp [g]
  have hmatrix : descendingSylvester f g 1 1 = !![X, 1; X, 2] := by
    have hrow0 : rowPolynomial f g 1 1 (0 : Fin 2) = f := by
      simpa using (ResultantDefinition.rowBlocks ℚ[X] f g 1 1).1 (0 : Fin 1)
    have hrow1 : rowPolynomial f g 1 1 (1 : Fin 2) = g := by
      simpa using (ResultantDefinition.rowBlocks ℚ[X] f g 1 1).2 (0 : Fin 1)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [descendingSylvester, hrow0, hrow1, f, g, Fin.rev, Polynomial.coeff_one]
  have hr : fixedResultant f g 1 1 = X := by
    rw [fixedResultant, hmatrix, Matrix.det_fin_two]
    simp
    ring
  have hfm : f.map φ = C 1 := by simp [f, φ]
  have hgm : g.map φ = C 2 := by simp [g, φ]
  refine ⟨hfn, hgn, hmatrix, hr, hfm, hgm, ?_, ?_⟩
  · change φ (fixedResultant f g 1 1) = 0
    rw [hr]
    simp [φ]
  · intro L _ _ h
    rcases h with ⟨x, hx, _⟩
    simp at hx

end D07.Ch19.ResultantSpecialization
