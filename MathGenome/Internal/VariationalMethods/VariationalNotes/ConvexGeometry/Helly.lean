import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Radon
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Helly

namespace VariationalNotes.ConvexGeometry

/-- Finite Helly for indexed convex subsets of real coordinate space.
Repeated sets, dimension zero, and the case `m = d + 1` are included. -/
theorem helly :
    ∀ (d m : ℕ) (C : Fin m → Set (Fin d → ℝ)),
      d + 1 ≤ m →
      (∀ i, Convex ℝ (C i)) →
      (∀ I : Finset (Fin m), I.card = d + 1 → (⋂ i ∈ I, C i).Nonempty) →
      (⋂ i, C i).Nonempty := by
  intro d m C hm hC hI
  have hcard : Module.finrank ℝ (Fin d → ℝ) + 1 ≤
      (Finset.univ : Finset (Fin m)).card := by
    simpa only [Module.finrank_fin_fun, Finset.card_univ, Fintype.card_fin] using hm
  have hfull := Convex.helly_theorem (𝕜 := ℝ) (F := C) hcard
    (fun i _ => hC i) (fun I _ hcardI => hI I (by
      simpa only [Module.finrank_fin_fun] using hcardI))
  simpa only [Finset.mem_univ, Set.iInter_true] using hfull

end VariationalNotes.ConvexGeometry
