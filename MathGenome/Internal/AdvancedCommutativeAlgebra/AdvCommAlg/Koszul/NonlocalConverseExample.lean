import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.NonlocalConverseExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.OrderExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Functoriality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.RegularAcyclicity
import Mathlib.Logic.Equiv.Fin.Rotate

/-! RK-13: a proper generating list with zero positive Koszul homology
which fails weak regularity in its given order. -/
open CategoryTheory
noncomputable section
universe u
namespace AdvCommAlg.Koszul.NonlocalConverseExample
open RegularSequence.OrderExample
variable (k : Type u) [Field k]

/-- All three generators vanish at the origin, so they generate a proper ideal. -/
theorem proper_ideal :
    Ideal.ofList ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) ≠ ⊤ := by
  have hle : Ideal.ofList ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) ≤
      RingHom.ker (MvPolynomial.eval (fun _ : Fin 3 => (0 : k))) := by
    apply Ideal.span_le.mpr
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [RingHom.mem_ker, X, Y, Z]
  intro htop
  have h1 := hle (htop ▸ (show (1 : Poly k) ∈ (⊤ : Ideal (Poly k)) from trivial))
  simp [RingHom.mem_ker] at h1

/-- Rotation preserves the coefficient complex, hence its homology. -/
theorem positive_homology_vanishes (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology (Poly k)
      ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) q) := by
  obtain ⟨e⟩ := coefficient_permutation_iso (Poly k)
    ([Y * (1 - X), Z * (1 - X), X] : List (Poly k))
    ([X, Y * (1 - X), Z * (1 - X)] : List (Poly k))
    (finRotate 3) (by intro j; fin_cases j <;> rfl)
  have : Subsingleton (homology (Poly k)
      ([X, Y * (1 - X), Z * (1 - X)] : List (Poly k)) q) :=
    weaklyRegular_acyclic (Poly k) _ (ordered_regular k).1 q hq
  let h : homology (Poly k)
      ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) q ≃ₗ[Poly k]
      homology (Poly k) ([X, Y * (1 - X), Z * (1 - X)] : List (Poly k)) q :=
    ((HomologicalComplex.homologyFunctor (ModuleCat (Poly k))
    (ComplexShape.down ℕ) q).mapIso e).toLinearEquiv
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩

/-- The second multiplication fails injectivity, as witnessed by the class of Y. -/
theorem not_weaklyRegular :
    ¬ RegularSequence.WeaklyRegular (Poly k)
      ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) :=
  rotated_not_weaklyRegular k

end AdvCommAlg.Koszul.NonlocalConverseExample
