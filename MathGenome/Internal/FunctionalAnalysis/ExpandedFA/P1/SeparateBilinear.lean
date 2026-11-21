import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeparateBilinear
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsUbp

open Set Filter TopologicalSpace
open scoped Topology

namespace ExpandedFA.P1

/-- Banach–Steinhaus controls the moving first argument uniformly over a
convergent sequence in the second argument. -/
theorem separately_continuous_bilinear_seqContinuous :
    SeparateBilinearSpec.SequentialJointContinuity := by
  intro 𝕜 E F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE B hleft hright
  let : Module ℝ E := Module.compHom E (algebraMap ℝ 𝕜)
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_compHom ℝ 𝕜 E
  let : Module ℝ G := Module.compHom G (algebraMap ℝ 𝕜)
  let : IsScalarTower ℝ 𝕜 G := IsScalarTower.of_compHom ℝ 𝕜 G
  intro z p hp
  have hx : Tendsto (fun n => (z n).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hp
  have hy : Tendsto (fun n => (z n).2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hp
  let A : ℕ → E →L[𝕜] G := fun n => ⟨B.flip ((z n).2), hleft ((z n).2)⟩
  have hA (x : E) : Bounded (range fun n => A n x) := by
    exact convergent_sequence_bounded 𝕜 G (fun n => B x ((z n).2)) (B x p.2)
      (((hright x).tendsto p.2).comp hy)
  have heq := fspace_banach_steinhaus 𝕜 E G ℕ hE A hA
  have hxzero : Tendsto (fun n => (z n).1 - p.1) atTop (𝓝 (0 : E)) := by
    simpa using hx.sub (show Tendsto (fun _ : ℕ => p.1) atTop (𝓝 p.1) from
      tendsto_const_nhds)
  have hzero : Tendsto (fun n => A n ((z n).1 - p.1)) atTop (𝓝 (0 : G)) := by
    apply Filter.tendsto_def.mpr
    intro V hV
    obtain ⟨U, hU, hAU⟩ := heq V hV
    filter_upwards [hxzero hU] with n hn
    exact hAU n (mem_image_of_mem _ hn)
  have hfixed : Tendsto (fun n => B p.1 ((z n).2)) atTop (𝓝 (B p.1 p.2)) :=
    ((hright p.1).tendsto p.2).comp hy
  have hsum := hzero.add hfixed
  change Tendsto (fun n => B ((z n).1 - p.1) ((z n).2) + B p.1 ((z n).2))
    atTop (𝓝 (0 + B p.1 p.2)) at hsum
  simpa only [LinearMap.map_sub₂, sub_add_cancel, zero_add, Function.comp_def] using hsum

/-- A product of metrizable spaces is sequential, so sequential joint
continuity suffices for joint continuity. -/
theorem separately_continuous_bilinear_continuous :
    SeparateBilinearSpec.JointContinuity := by
  intro 𝕜 E F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE B hleft hright
  let : MetrizableSpace E := hE.choose_spec.2.1
  exact (separately_continuous_bilinear_seqContinuous hE B hleft hright).continuous

end ExpandedFA.P1
