import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Kantorovich
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.KantorovichLargerUniqueness

noncomputable section
universe u v w
namespace NumAnalysis206.Newton
open Set Metric Filter Majorant

/-- W77 in one statement: exact well-defined Newton iterates, semilocal
convergence, all three error bounds (also at the critical parameter), and
the conditional quadratic rate and larger closed-ball uniqueness. -/
theorem kantorovich : Specs.NumAnalysis206.Newton.Kantorovich.Statement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ A η L hU hF hx₀ hA hη hL hb hres hball hLip x
  have hs := kantorovich_steps 𝕜 X Y F U x₀ A η L
    hU hF hx₀ hA hη hL hb hres hball hLip
  obtain ⟨_, _, q, hqmem, hFq, _, hqerror⟩ :=
    kantorovich_existence 𝕜 X Y F U x₀ A η L
      hU hF hx₀ hA hη hL hb hres hball hLip
  obtain ⟨p, hpmem, hFp, hlim, huniq, hlinear, hquadratic⟩ :=
    (kantorovich_rates_uniqueness 𝕜 X Y F U x₀ A η L
      hU hF hx₀ hA hη hL hb hres hball hLip).2
  have hqp : q = p := huniq q hqmem hFq
  subst q
  refine ⟨⟨rfl, operatorNewtonIterates_succ F x₀⟩, ?_,
    p, hpmem, hFp, hlim, huniq, ?_, hquadratic, ?_⟩
  · intro n
    have hn := hs.2.2.2.2 n
    exact ⟨hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.2.2⟩
  · exact fun n => ⟨hqerror n, hlinear n⟩
  · intro hb' ρ hρ hρupper hlargeball hlargeLip
    obtain ⟨_, r, hrmem, hFr, _, hruniq⟩ :=
      kantorovich_larger_uniqueness 𝕜 X Y F U x₀ A η L ρ
        hU hF hx₀ hA hη hL hb' hres hρ hρupper hlargeball hlargeLip
    intro y hy hFy
    exact (hruniq y hy hFy).trans (huniq r hrmem hFr)

end NumAnalysis206.Newton
