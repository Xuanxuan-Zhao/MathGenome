import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.InjectiveGlobalInverse
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
open Specs.D04.C04.InverseFunction (InverseNeighborhood)

/-- Global injectivity identifies the set-theoretic inverse with every local
inverse. Their open targets prove openness of the image, and their regularity
therefore gives regularity of the same global inverse. -/
private theorem globalize_inverse {n : ℕ} {r : ℕ∞ω}
    (U : Set (E n)) (f : E n → E n) (hinj : InjOn f U)
    (hloc : ∀ a ∈ U, ∃ X Y g,
      InverseNeighborhood U f a X Y g ∧ ContDiffOn ℝ r g Y) :
    IsOpen (f '' U) ∧ BijOn f U (f '' U) ∧
      ∃ g : E n → E n, MapsTo g (f '' U) U ∧
        LeftInvOn g f U ∧ RightInvOn g f (f '' U) ∧
        ContDiffOn ℝ r g (f '' U) := by
  have hsurj : SurjOn f U (f '' U) := fun _ hy => hy
  have hbij : BijOn f U (f '' U) := ⟨mapsTo_image f U, hinj, hsurj⟩
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨X, Y, g, hgeom, _⟩ := hloc a ha
    rcases hgeom with ⟨_, hY, _, hfa, hXU, hXY, _⟩
    apply mem_of_superset (hY.mem_nhds hfa)
    intro y hy
    obtain ⟨x, hx, hfx⟩ := hXY.surjOn hy
    exact ⟨x, hXU hx, hfx⟩
  let g := Function.invFunOn f U
  have hmap : MapsTo g (f '' U) U := hsurj.mapsTo_invFunOn
  have hleft : LeftInvOn g f U := hinj.leftInvOn_invFunOn
  have hright : RightInvOn g f (f '' U) := hsurj.rightInvOn_invFunOn
  refine ⟨hopen, hbij, g, hmap, hleft, hright, ?_⟩
  rintro y ⟨a, ha, hay⟩
  obtain ⟨X, Y, gi, hgeom, hgi⟩ := hloc a ha
  rcases hgeom with ⟨_, hY, _, hfa, hXU, hXY, hgiX, _, hgiR, _⟩
  have hyY : y ∈ Y := hay ▸ hfa
  have hYU : Y ⊆ f '' U := by
    intro z hz
    obtain ⟨x, hx, hfx⟩ := hXY.surjOn hz
    exact ⟨x, hXU hx, hfx⟩
  have heq : g =ᶠ[𝓝 y] gi := by
    filter_upwards [hY.mem_nhds hyY] with z hz
    exact hinj (hmap (hYU hz)) (hXU (hgiX hz))
      ((hright (hYU hz)).trans (hgiR hz).symm)
  exact ((hgi.contDiffAt (hY.mem_nhds hyY)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- Every positive finite regularity order has a global inverse on the image. -/
theorem injective_global_inverse_finite :
    Specs.D04.C04.InjectiveGlobalInverse.injective_global_inverse_finiteType := by
  intro n r U f hr hU hf hinj hD
  have hloc : ∀ a ∈ U, ∃ X Y g,
      InverseNeighborhood U f a X Y g ∧ ContDiffOn ℝ (r : ℕ∞ω) g Y := by
    intro a ha
    obtain ⟨A, hA⟩ := hD a ha
    obtain ⟨X, Y, g, hgeom, hg⟩ := inverse_function_finite r U f a A hr hU hf ha hA
    exact ⟨X, Y, g, hgeom, (crOn_iff_contDiffOn r Y g hgeom.2.1).mp hg⟩
  obtain ⟨hopen, hbij, g, hmap, hleft, hright, hg⟩ := globalize_inverse U f hinj hloc
  exact ⟨hopen, hbij, g, hmap, hleft, hright,
    (crOn_iff_contDiffOn r (f '' U) g hopen).mpr hg⟩

/-- Smooth data give one smooth global inverse on the image. -/
theorem injective_global_inverse_smooth :
    Specs.D04.C04.InjectiveGlobalInverse.injective_global_inverse_smoothType := by
  intro n U f hU hf hinj hD
  have hloc : ∀ a ∈ U, ∃ X Y g,
      InverseNeighborhood U f a X Y g ∧ ContDiffOn ℝ ∞ g Y := by
    intro a ha
    obtain ⟨A, hA⟩ := hD a ha
    obtain ⟨X, Y, g, hgeom, hg⟩ := inverse_function_smooth U f a A hU hf ha hA
    exact ⟨X, Y, g, hgeom, (smoothOn_iff_contDiffOn Y g hgeom.2.1).mp hg⟩
  obtain ⟨hopen, hbij, g, hmap, hleft, hright, hg⟩ := globalize_inverse U f hinj hloc
  exact ⟨hopen, hbij, g, hmap, hleft, hright,
    (smoothOn_iff_contDiffOn (f '' U) g hopen).mpr hg⟩

end D04
