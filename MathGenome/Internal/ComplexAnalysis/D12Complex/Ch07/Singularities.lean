import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Singularities

/-!
Exports of the shared isolated-singularity definitions (paper.tex:1670–1677).
As in Ch01.Basic, these aliases expose the canonical objects from the independent
Spec without creating competing definitions for later chapters.
-/

namespace D12Complex.Singularities

abbrev puncturedDisk : Specs.D12Complex.Ch07.Singularities.puncturedDisk_type :=
  _root_.D12Complex.puncturedDisk

abbrev IsolatedSingularityAt : Specs.D12Complex.Ch07.Singularities.IsolatedSingularityAt_type :=
  _root_.D12Complex.IsolatedSingularityAt

abbrev RemovableSingularityAt : Specs.D12Complex.Ch07.Singularities.RemovableSingularityAt_type :=
  _root_.D12Complex.RemovableSingularityAt

abbrev PoleOfOrderAt : Specs.D12Complex.Ch07.Singularities.PoleOfOrderAt_type :=
  _root_.D12Complex.PoleOfOrderAt

abbrev PoleAt : Specs.D12Complex.Ch07.Singularities.PoleAt_type :=
  _root_.D12Complex.PoleAt

abbrev EssentialSingularityAt : Specs.D12Complex.Ch07.Singularities.EssentialSingularityAt_type :=
  _root_.D12Complex.EssentialSingularityAt

end D12Complex.Singularities

namespace D12Complex

theorem removableSingularityAt_isolated (f : ℂ → ℂ) (a : ℂ)
    (h : RemovableSingularityAt f a) : IsolatedSingularityAt f a :=
  h.1

theorem poleOfOrderAt_isolated (f : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (h : PoleOfOrderAt f a m) : IsolatedSingularityAt f a :=
  h.2.1

theorem poleOfOrderAt_positive (f : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (h : PoleOfOrderAt f a m) : 1 ≤ m :=
  h.1

theorem essentialSingularityAt_isolated (f : ℂ → ℂ) (a : ℂ)
    (h : EssentialSingularityAt f a) : IsolatedSingularityAt f a :=
  h.1

end D12Complex
