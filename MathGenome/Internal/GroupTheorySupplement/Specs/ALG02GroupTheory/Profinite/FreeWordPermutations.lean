import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.FreeGroup.Basic

namespace ALG02GroupTheory.Profinite.FreeWordPermutations

variable {α : Type*}

/-- Letters in action order, starting at the right-hand end of the word.
The sign `true` denotes a generator and `false` denotes its inverse. -/
def stepLetter (w : List (α × Bool)) (i : Fin w.length) : α × Bool :=
  w.get i.rev

/-- For step `i`, the endpoint is `i.castSucc` when the sign equals `leftSign`
and `i.succ` otherwise. The domain of the prescription uses `leftSign = true`,
and the range uses `leftSign = false`. -/
def stepEndpoint (w : List (α × Bool)) (leftSign : Bool) (i : Fin w.length) :
    Fin (w.length + 1) :=
  if (stepLetter w i).2 = leftSign then i.castSucc else i.succ

end ALG02GroupTheory.Profinite.FreeWordPermutations

namespace Specs.ALG02GroupTheory.Profinite.FreeWordPermutations

open _root_.ALG02GroupTheory.Profinite.FreeWordPermutations

/-- The prescribed domains and ranges are each distinct among the steps for a fixed generator. -/
def prescriptionsInjective : Prop :=
  ∀ {α : Type*} (w : List (α × Bool)), FreeGroup.IsReduced w → ∀ (s : α) (leftSign : Bool),
    Function.Injective (fun i : {i : Fin w.length // (stepLetter w i).1 = s} =>
      stepEndpoint w leftSign i.val)

/-- The signed letter at each step moves the preceding vertex to the next vertex. -/
def existsPathPermutations : Prop :=
  ∀ {α : Type*} (w : List (α × Bool)), w ≠ [] → FreeGroup.IsReduced w →
    ∃ σ : α → Equiv.Perm (Fin (w.length + 1)),
      (∀ i : Fin w.length,
        (if (stepLetter w i).2 then σ (stepLetter w i).1 else (σ (stepLetter w i).1)⁻¹)
          i.castSucc = i.succ) ∧
      (∀ s : α, (∀ b : Bool, (s, b) ∉ w) → σ s = 1)

end Specs.ALG02GroupTheory.Profinite.FreeWordPermutations
