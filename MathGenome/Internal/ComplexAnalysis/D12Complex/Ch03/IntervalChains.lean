import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations

/-!
Intrinsic piecewise C¹ paths and their free integral chains. A path is determined
by its two endpoints and its map on the closed parameter interval. The
clamped extension lets the intrinsic chain use the established contour integrals.
-/

noncomputable section
open Set

namespace D12Complex

namespace ComplexPath

/-- The unique representative obtained by extending the interval map by its endpoint values. -/
def clamp (γ : ComplexPath) : ComplexPath :=
  ofContinuousMap γ.a γ.b γ.ordered γ.onInterval

theorem clamp_apply (γ : ComplexPath) {t : ℝ} (ht : t ∈ Icc γ.a γ.b) :
    γ.clamp t = γ t :=
  ofContinuousMap_apply γ.a γ.b γ.ordered γ.onInterval ⟨t, ht⟩

theorem clamp_eq_of_eqOn {γ δ : ComplexPath} (ha : γ.a = δ.a) (hb : γ.b = δ.b)
    (h : EqOn γ δ (Icc γ.a γ.b)) : γ.clamp = δ.clamp := by
  rcases γ with ⟨a, b, hab, g, hg⟩
  rcases δ with ⟨a', b', hab', g', hg'⟩
  change a = a' at ha
  change b = b' at hb
  subst a'
  subst b'
  apply congrArg (ofContinuousMap a b hab)
  ext t
  exact h t.property

end ComplexPath

namespace PiecewiseC1Path

/-- Clamping leaves the regularity on each partition piece unchanged. -/
def clamp (γ : PiecewiseC1Path) : PiecewiseC1Path :=
  ⟨γ.path.clamp, ⟨{
    count := γ.partition.count
    node := γ.partition.node
    strictMono := γ.partition.strictMono
    first := γ.partition.first
    last := γ.partition.last
    smooth := fun i => (γ.partition.smooth i).congr
      (fun _ ht => γ.path.clamp_apply (γ.partition.piece_subset i ht)) }⟩⟩

@[simp] theorem clamp_a (γ : PiecewiseC1Path) : γ.clamp.path.a = γ.path.a := rfl

@[simp] theorem clamp_b (γ : PiecewiseC1Path) : γ.clamp.path.b = γ.path.b := rfl

theorem clamp_apply (γ : PiecewiseC1Path) {t : ℝ} (ht : t ∈ Icc γ.path.a γ.path.b) :
    γ.clamp t = γ t :=
  γ.path.clamp_apply ht

@[simp] theorem clamp_trace (γ : PiecewiseC1Path) : γ.clamp.trace = γ.trace := by
  change γ.path.clamp '' Icc γ.path.a γ.path.b = γ.path '' Icc γ.path.a γ.path.b
  exact image_congr (fun _ ht => γ.path.clamp_apply ht)

@[simp] theorem clamp_closed_iff (γ : PiecewiseC1Path) : γ.clamp.IsClosed ↔ γ.IsClosed := by
  change (γ.clamp γ.path.b = γ.clamp γ.path.a) ↔ (γ γ.path.b = γ γ.path.a)
  rw [γ.clamp_apply (right_mem_Icc.mpr γ.path.ordered),
    γ.clamp_apply (left_mem_Icc.mpr γ.path.ordered)]

theorem clamp_eq_of_eqOn {γ δ : PiecewiseC1Path} (ha : γ.path.a = δ.path.a)
    (hb : γ.path.b = δ.path.b) (h : EqOn γ δ (Icc γ.path.a γ.path.b)) :
    γ.clamp = δ.clamp :=
  Subtype.ext (ComplexPath.clamp_eq_of_eqOn ha hb h)

@[simp] theorem clamp_clamp (γ : PiecewiseC1Path) : γ.clamp.clamp = γ.clamp :=
  clamp_eq_of_eqOn rfl rfl (fun _ ht => γ.clamp_apply ht)

theorem clamp_integral (γ : PiecewiseC1Path) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) : γ.clamp.integral f = γ.integral f := by
  have hfc : ContinuousOn f γ.clamp.trace := by simpa only [clamp_trace] using hf
  rw [γ.clamp.integral_congr_representative γ f hfc (fun _ ht => γ.clamp_apply ht),
    γ.integral_congr_representative γ f hf (fun _ _ => rfl), clamp_a, clamp_b]

end PiecewiseC1Path

/-- A piecewise C¹ map on a compact interval, represented by its clamped extension. -/
abbrev IntervalPath := {γ : PiecewiseC1Path // γ.clamp = γ}

namespace IntervalPath

def ofRepresentative (γ : PiecewiseC1Path) : IntervalPath :=
  ⟨γ.clamp, γ.clamp_clamp⟩

/-- Equality uses precisely the endpoints and the values on the parameter interval. -/
theorem ofRepresentative_eq_iff {γ δ : PiecewiseC1Path} :
    ofRepresentative γ = ofRepresentative δ ↔
      γ.path.a = δ.path.a ∧ γ.path.b = δ.path.b ∧ EqOn γ δ (Icc γ.path.a γ.path.b) := by
  constructor
  · intro h
    have hc : γ.clamp = δ.clamp := congrArg Subtype.val h
    have ha := congrArg (fun p : PiecewiseC1Path => p.path.a) hc
    have hb := congrArg (fun p : PiecewiseC1Path => p.path.b) hc
    simp only [PiecewiseC1Path.clamp_a] at ha
    simp only [PiecewiseC1Path.clamp_b] at hb
    refine ⟨ha, hb, ?_⟩
    intro t ht
    have ht' : t ∈ Icc δ.path.a δ.path.b := by simpa only [ha, hb] using ht
    rw [← γ.clamp_apply ht, ← δ.clamp_apply ht', hc]
  · rintro ⟨ha, hb, h⟩
    exact Subtype.ext (PiecewiseC1Path.clamp_eq_of_eqOn ha hb h)

@[simp] theorem ofRepresentative_val (γ : IntervalPath) :
    ofRepresentative γ.val = γ :=
  Subtype.ext γ.property

/-- Construct an intrinsic path directly from a continuous interval map and its regularity. -/
def ofContinuousMap (a b : ℝ) (hab : a ≤ b) (g : C(Icc a b, ℂ))
    (hg : IsPiecewiseC1 (ComplexPath.ofContinuousMap a b hab g)) : IntervalPath :=
  ofRepresentative ⟨ComplexPath.ofContinuousMap a b hab g, hg⟩

end IntervalPath

/-- The free integral chain on intrinsic piecewise C¹ interval maps. -/
abbrev IntervalChain := IntervalPath →₀ ℤ

namespace IntervalChain

/-- Embed intrinsic chains by using the distinguished clamped representatives. -/
def toIntegralChain (Γ : IntervalChain) : IntegralChain :=
  Γ.mapDomain (fun γ : IntervalPath => γ.val)

def trace (Γ : IntervalChain) : Set ℂ := Γ.toIntegralChain.trace

def integral (Γ : IntervalChain) (f : ℂ → ℂ) : ℂ := Γ.toIntegralChain.integral f

def IsCycle (Γ : IntervalChain) : Prop := Γ.toIntegralChain.IsCycle

theorem mem_trace_iff (Γ : IntervalChain) (z : ℂ) :
    z ∈ Γ.trace ↔ ∃ γ ∈ Γ.support, z ∈ γ.val.trace := by
  classical
  change (∃ γ ∈ Γ.toIntegralChain.support, z ∈ γ.trace) ↔ _
  constructor
  · rintro ⟨δ, hδ, hz⟩
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hδ)
    exact ⟨γ, hγ, hz⟩
  · rintro ⟨γ, hγ, hz⟩
    refine ⟨γ.val, Finsupp.mem_support_iff.mpr ?_, hz⟩
    change (Γ.mapDomain (Subtype.val : IntervalPath → PiecewiseC1Path)) γ.val ≠ 0
    have hv : Function.Injective (Subtype.val : IntervalPath → PiecewiseC1Path) :=
      Subtype.val_injective
    exact (Finsupp.mapDomain_apply_of_injective hv Γ γ).trans_ne (Finsupp.mem_support_iff.mp hγ)

@[simp] theorem zero_trace : (0 : IntervalChain).trace = ∅ := by
  simp [trace, toIntegralChain, IntegralChain.zero_trace]

end IntervalChain

namespace IntegralChain

/-- Send each generator to its intrinsic path and add coefficients that coincide. -/
def toIntervalChain (Γ : IntegralChain) : IntervalChain :=
  Γ.mapDomain IntervalPath.ofRepresentative

@[simp] theorem toIntervalChain_single (γ : PiecewiseC1Path) (m : ℤ) :
    toIntervalChain (Finsupp.single γ m) =
      Finsupp.single (IntervalPath.ofRepresentative γ) m :=
  Finsupp.mapDomain_single

@[simp] theorem toIntervalChain_single_trace (γ : PiecewiseC1Path) :
    (toIntervalChain (Finsupp.single γ 1)).trace = γ.trace := by
  classical
  ext z
  rw [toIntervalChain_single, IntervalChain.mem_trace_iff]
  simp [IntervalPath.ofRepresentative]

@[simp] theorem toIntervalChain_add (Γ Δ : IntegralChain) :
    (Γ + Δ).toIntervalChain = Γ.toIntervalChain + Δ.toIntervalChain :=
  Finsupp.mapDomain_add

@[simp] theorem toIntervalChain_sub (Γ Δ : IntegralChain) :
    (Γ - Δ).toIntervalChain = Γ.toIntervalChain - Δ.toIntervalChain :=
  Finsupp.mapDomain_sub

theorem toIntervalChain_add_sub_eq (Γ : IntegralChain) {γ δ : PiecewiseC1Path}
    (ha : γ.path.a = δ.path.a) (hb : γ.path.b = δ.path.b)
    (h : EqOn γ δ (Icc γ.path.a γ.path.b)) (m : ℤ) :
    (Γ + Finsupp.single γ m - Finsupp.single δ m).toIntervalChain = Γ.toIntervalChain := by
  have he := IntervalPath.ofRepresentative_eq_iff.mpr ⟨ha, hb, h⟩
  simp only [toIntervalChain_add, toIntervalChain_sub, toIntervalChain_single, he, add_sub_cancel_right]

theorem toIntervalChain_trace_subset (Γ : IntegralChain) : Γ.toIntervalChain.trace ⊆ Γ.trace := by
  classical
  intro z hz
  obtain ⟨δ, hδ, hz⟩ := (IntervalChain.mem_trace_iff _ z).mp hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hδ)
  exact ⟨γ, hγ, by simpa only [IntervalPath.ofRepresentative, PiecewiseC1Path.clamp_trace] using hz⟩

theorem toIntervalChain_isCycle {Γ : IntegralChain} (hΓ : Γ.IsCycle) :
    Γ.toIntervalChain.IsCycle := by
  classical
  intro δ hδ
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hδ)
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hη)
  exact (PiecewiseC1Path.clamp_closed_iff γ).mpr (hΓ γ hγ)

theorem toIntervalChain_integral (Γ : IntegralChain) (f : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) : Γ.toIntervalChain.integral f = Γ.integral f := by
  classical
  have hmap : Γ.toIntervalChain.toIntegralChain = Γ.mapDomain PiecewiseC1Path.clamp := by
    rw [IntervalChain.toIntegralChain, toIntervalChain, ← Finsupp.mapDomain_comp]
    rfl
  change Γ.toIntervalChain.toIntegralChain.integral f = Γ.integral f
  rw [hmap]
  unfold IntegralChain.integral
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  apply Finset.sum_congr rfl
  intro γ hγ
  dsimp only
  rw [PiecewiseC1Path.clamp_integral γ f (hf.mono fun z hz => ⟨γ, hγ, hz⟩)]

end IntegralChain

namespace IntervalChain

@[simp] theorem toIntegralChain_toIntervalChain (Γ : IntervalChain) :
    Γ.toIntegralChain.toIntervalChain = Γ := by
  have hcomp : (IntervalPath.ofRepresentative ∘ (fun γ : IntervalPath => γ.val)) = id :=
    funext IntervalPath.ofRepresentative_val
  rw [IntegralChain.toIntervalChain, toIntegralChain, ← Finsupp.mapDomain_comp,
    hcomp, Finsupp.mapDomain_id]

end IntervalChain

def IntervalCycle := {Γ : IntervalChain // Γ.IsCycle}

namespace IntervalCycle

def chain (Γ : IntervalCycle) : IntervalChain := Γ.val

def toIntegralCycle (Γ : IntervalCycle) : IntegralCycle :=
  ⟨Γ.chain.toIntegralChain, Γ.property⟩

def trace (Γ : IntervalCycle) : Set ℂ := Γ.chain.trace

def integral (Γ : IntervalCycle) (f : ℂ → ℂ) : ℂ := Γ.chain.integral f

end IntervalCycle

namespace IntegralCycle

def toIntervalCycle (Γ : IntegralCycle) : IntervalCycle :=
  ⟨Γ.chain.toIntervalChain, IntegralChain.toIntervalChain_isCycle Γ.property⟩

end IntegralCycle

end D12Complex
