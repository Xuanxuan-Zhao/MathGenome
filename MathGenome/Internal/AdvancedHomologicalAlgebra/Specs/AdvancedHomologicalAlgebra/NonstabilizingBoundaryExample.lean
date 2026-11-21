import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExhaustiveChainConvergence
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.PNat.Basic

/-! The example following HA-S02, source lines 500–509. Positive integers
index both copies of the direct sum. We use chain degrees `0,-1`; reversing
degrees gives exactly the source's cochain degrees `0,1`. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe u
namespace AdvancedHomologicalAlgebra.NonstabilizingBoundary
variable (k : Type u) [Field k]

abbrev V := ℕ+ →₀ k

def term (n : ℤ) : ModuleCat.{u} k :=
  if n = 0 ∨ n = -1 then ModuleCat.of k (V k) else ModuleCat.of k (Fin 0 → k)

def differential (i j : ℤ) : term k i ⟶ term k j :=
  if h : i = 0 ∧ j = -1 then
    eqToHom (by rcases h with ⟨rfl, rfl⟩; rfl) else 0

def complex : ChainComplex (ModuleCat.{u} k) ℤ where
  X := term k
  d := differential k
  shape i j h := by
    dsimp [differential]
    rw [dite_eq_right]
    intro hh
    rcases hh with ⟨rfl, rfl⟩
    exact h (by decide)
  d_comp_d' i j l _ _ := by
    dsimp [differential]
    split_ifs with h h' h'
    · omega
    all_goals simp

/-- In degree zero, filtration step `a` contains the `e_i` with `i ≤ a`. -/
def head (a : ℤ) : Submodule k (V k) :=
  Finsupp.supported k k {i | (i : ℤ) ≤ a}

def piece (a n : ℤ) : Submodule k ((complex k).X n) := by
  by_cases hn : n = 0
  · subst n; exact head k a
  · by_cases hn' : n = -1
    · subst n; exact if 0 ≤ a then ⊤ else ⊥
    · exact ⊤

@[simp] theorem piece_zero (a : ℤ) : piece k a 0 = head k a := by
  rfl
@[simp] theorem piece_neg_one (a : ℤ) : piece k a (-1) = if 0 ≤ a then ⊤ else ⊥ := by
  simp [piece]

def filtration : ExhaustiveChain.Filtration (complex k) where
  piece := piece k
  increasing n a b hab := by
    by_cases hn : n = 0
    · subst n
      change head k a ≤ head k b
      exact Finsupp.supported_mono (fun i hi => le_trans hi hab)
    · by_cases hn' : n = -1
      · subst n; simp only [piece_neg_one]
        split_ifs with ha hb hb
        all_goals first | exact le_rfl | exact bot_le | omega
      · simp [piece, hn, hn']
  preserved a n := by
    by_cases hn : n = 0
    · subst n
      change piece k a 0 ≤ (piece k a (-1)).comap (differential k 0 (-1)).hom
      by_cases ha : 0 ≤ a
      · rw [piece_neg_one, ite_eq_left ha, Submodule.comap_top]
        exact le_top
      · intro x hx
        have hx0 : x = 0 := by
          apply Finsupp.ext
          intro i
          apply (Finsupp.mem_supported' k x).1 hx
          change ¬ (i : ℤ) ≤ a
          have := i.pos
          omega
        subst x
        exact Submodule.zero_mem _
    · change piece k a n ≤ (piece k a (n-1)).comap (differential k n (n-1)).hom
      simp only [differential, hn, false_and, dite_false]
      exact fun x _ => Submodule.zero_mem _

/-- A concrete `Z_r/B_r`, with the same submodules as HA-S02's actual pages. -/
abbrev page (r : ℕ) :=
  (filtration k).pageCycles r 0 (-1) ⧸
    ((filtration k).pageBoundaries r 0 (-1)).comap
      ((filtration k).pageCycles r 0 (-1)).subtype

abbrev tail (r : ℕ) : Submodule k (V k) :=
  Finsupp.supported k k {i | r ≤ (i : ℕ)}

/-- The class of an actual f-vector, rather than an unspecified abstract
isomorphism class of a vector space. -/
def representative (r : ℕ) : V k →ₗ[k] (filtration k).pageCycles r 0 (-1) :=
  (((filtration k).gradedProjection 0 (-1)).comp
    (Submodule.topEquiv : (⊤ : Submodule k (V k)) ≃ₗ[k] V k).symm.toLinearMap).codRestrict _
      (fun x => by
        refine ⟨⟨x, by trivial⟩, ?_, rfl⟩
        refine ⟨by trivial, ?_⟩
        change (differential k (-1) (-2)).hom x ∈ piece k (0-(r:ℤ)) (-2)
        simp [differential])

abbrev classMap (r : ℕ) : V k →ₗ[k] page k r :=
  (((filtration k).pageBoundaries r 0 (-1)).comap
    ((filtration k).pageCycles r 0 (-1)).subtype).mkQ.comp (representative k r)

structure PageComputation (r : ℕ) where
  equiv : page k r ≃ₗ[k] tail k r
  representative_formula : ∀ x : V k,
    equiv (classMap k r x) = Finsupp.restrictDom k k {i : ℕ+ | r ≤ (i:ℕ)} x
  spanning_formula : Submodule.span k
    ((fun i : ℕ+ => classMap k r (Finsupp.single i 1)) '' {i | r ≤ (i:ℕ)}) = ⊤


namespace Specs
/-- The full example includes the fixed complex, its filtration, its actual
page subquotients, nonvanishing, the increasing nonstationary boundaries,
and the zero eventual quotient and homology. -/
def FullStatement : Prop := ∀ (k : Type u) [Field k],
  (∀ n, LinearMap.ker ((complex k).d n (n-1)).hom =
    LinearMap.range ((complex k).d (n+1) n).hom) ∧
  (filtration k).BoundedBelow ∧ (filtration k).Exhaustive ∧
  (∀ r : ℕ, 1 ≤ r → Nonempty (PageComputation k r)) ∧
  (∀ r : ℕ, 1 ≤ r → Nontrivial (page k r)) ∧
  (∀ r : ℕ, 1 ≤ r →
    (filtration k).pageBoundaries r 0 (-1) <
      (filtration k).pageBoundaries (r+1) 0 (-1)) ∧
  (∀ r : ℕ, (filtration k).pageCycles r 0 (-1) = (filtration k).limitCycles 0 (-1)) ∧
  (⨆ r : ℕ, (filtration k).pageBoundaries r 0 (-1)) = ⊤ ∧
  Subsingleton ((filtration k).infinity 0 (-1)) ∧
  Subsingleton ((filtration k).homology (-1)) ∧
  Nonempty (filtration k).SpectralSequence ∧
  (∀ (S : (filtration k).SpectralSequence) (r : ℕ),
    Nonempty ((S.page r 0 (-1)) ≃ₗ[k] page k r))
end Specs
end AdvancedHomologicalAlgebra.NonstabilizingBoundary
