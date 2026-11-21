import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-! Disk automorphisms in paper.tex:1492–1525. Functions are total representatives;
all assertions about their values and uniqueness are restricted to the open disk. -/
noncomputable section

namespace D12Complex

/-- The disk Möbius map taking `a` to zero. -/
def DiskPhi (a z : ℂ) : ℂ := (z - a) / (1 - star a * z)

/-- The explicit inverse of `DiskPhi a` on the disk. -/
def DiskPhiInv (a w : ℂ) : ℂ := (w + a) / (1 + star a * w)

end D12Complex

namespace Specs.D12Complex.Ch06.DiskAutomorphisms
open _root_.D12Complex Metric Set

def phi_type := ℂ → ℂ → ℂ
def phi_value : phi_type := fun a z => (z - a) / (1 - star a * z)
def phiInv_type := ℂ → ℂ → ℂ
def phiInv_value : phiInv_type := fun a w => (w + a) / (1 + star a * w)

def denominator_ne_zero_type : Prop :=
  ∀ a ∈ ball (0 : ℂ) 1, ∀ z ∈ ball (0 : ℂ) 1, 1 - star a * z ≠ 0

def inverse_denominator_ne_zero_type : Prop :=
  ∀ a ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1, 1 + star a * w ≠ 0

def phi_biholomorphicPair_type : Prop :=
  ∀ a ∈ ball (0 : ℂ) 1,
    BiholomorphicPair (ball 0 1) (ball 0 1) (DiskPhi a) (DiskPhiInv a)

def rotation_phi_automorphism_type : Prop :=
  ∀ a ∈ ball (0 : ℂ) 1, ∀ c : ℂ, ‖c‖ = 1 →
    IsBiholomorphism (ball 0 1) (ball 0 1) (fun z => c * DiskPhi a z)

/-- A unique pair `(a,c)`, with `a` the zero preimage and `c` unimodular.
Equality is on the disk, as required for maps whose domain is the disk. -/
def classification_type : Prop :=
  ∀ f : ℂ → ℂ, IsBiholomorphism (ball 0 1) (ball 0 1) f →
    ∃! p : ℂ × ℂ, p.1 ∈ ball (0 : ℂ) 1 ∧ ‖p.2‖ = 1 ∧
      EqOn f (fun z => p.2 * DiskPhi p.1 z) (ball 0 1)

def zero_preimage_type : Prop :=
  ∀ (f : ℂ → ℂ) (a c : ℂ), a ∈ ball (0 : ℂ) 1 → ‖c‖ = 1 →
    EqOn f (fun z => c * DiskPhi a z) (ball 0 1) →
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 ↔ z = a

end Specs.D12Complex.Ch06.DiskAutomorphisms
