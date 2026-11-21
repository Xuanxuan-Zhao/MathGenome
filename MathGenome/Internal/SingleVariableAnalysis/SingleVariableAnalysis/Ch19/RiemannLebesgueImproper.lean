import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.RiemannLebesgue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Absolute
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open private regularIntegral_agreement regularIntegral_symm from
  MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
open private phase_norm realIntegral_congr from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.OscillatoryBound

/-- The omitted left tail is bounded by the corresponding omitted absolute tail. -/
theorem left_truncation_remainder_bound {f : ℝ → ℂ}
    {a : WithBot ℝ} {b : WithTop ℝ}
    (hf : LocallyIntegrable .complex f a b)
    (hn : LocallyIntegrable .real (fun x => ‖f x‖) a b)
    (c u : RegularPoint a b) (huc : u.val ≤ c.val)
    {L : ℂ} {A : ℝ}
    (hL : LeftHasIntegral .complex f a c.val L)
    (hA : LeftHasIntegral .real (fun x => ‖f x‖) a c.val A)
    (hp : ComplexIntegrable f u.val c.val)
    (hpn : RealIntegrable (fun x => ‖f x‖) u.val c.val) :
    ‖L - complexIntegral f hp‖ ≤ |realIntegral _ hpn - A| := by
  have hLf := left_change_split .complex f hf c u L hL
  have hAn := left_change_split .real (fun x => ‖f x‖) hn c u A hA
  rw [regularIntegral_symm .complex f hf u c,
    regularIntegral_agreement .complex f hf u c huc hp] at hLf
  rw [regularIntegral_symm .real (fun x => ‖f x‖) hn u c,
    regularIntegral_agreement .real (fun x => ‖f x‖) hn u c huc hpn] at hAn
  exact (left_norm_bound .complex f a u.val _ _ hLf hAn).trans
    (by change A + -realIntegral _ hpn ≤ |realIntegral _ hpn - A|
        have hh := neg_le_abs (realIntegral _ hpn - A)
        linarith only [hh])

/-- The right tail has the same bound, with an independent cutoff. -/
theorem right_truncation_remainder_bound {f : ℝ → ℂ}
    {a : WithBot ℝ} {b : WithTop ℝ}
    (hf : LocallyIntegrable .complex f a b)
    (hn : LocallyIntegrable .real (fun x => ‖f x‖) a b)
    (c v : RegularPoint a b) (hcv : c.val ≤ v.val)
    {L : ℂ} {A : ℝ}
    (hL : RightHasIntegral .complex f c.val b L)
    (hA : RightHasIntegral .real (fun x => ‖f x‖) c.val b A)
    (hp : ComplexIntegrable f c.val v.val)
    (hpn : RealIntegrable (fun x => ‖f x‖) c.val v.val) :
    ‖L - complexIntegral f hp‖ ≤ |realIntegral _ hpn - A| := by
  have hLf := right_change_split .complex f hf c v L hL
  have hAn := right_change_split .real (fun x => ‖f x‖) hn c v A hA
  rw [regularIntegral_agreement .complex f hf c v hcv hp] at hLf
  rw [regularIntegral_agreement .real (fun x => ‖f x‖) hn c v hcv hpn] at hAn
  exact (right_norm_bound .complex f v.val b _ _ hLf hAn).trans
    (by change A - realIntegral _ hpn ≤ |realIntegral _ hpn - A|
        simpa only [neg_sub] using neg_le_abs (realIntegral _ hpn - A))


/-- The phase has unit norm, so every weighted norm integral is the original
absolute integral, including its two independent endpoint limits. -/
theorem oscillatory_norm_function (f : ℝ → ℂ) (lam : ℝ) :
    (fun x => ‖f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))‖) =
      (fun x => ‖f x‖) := by
  funext x
  rw [norm_mul, phase_norm, mul_one]

theorem oscillatory_locally_integrable {f : ℝ → ℂ}
    {a : WithBot ℝ} {b : WithTop ℝ}
    (hf : LocallyIntegrable .complex f a b) (lam : ℝ) :
    LocallyIntegrable .complex
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b := by
  intro u v hau huv hvb
  exact oscillatory_product_integrable (hf u v hau huv hvb) lam

theorem oscillatory_absolute_converges {f : ℝ → ℂ}
    {a : WithBot ℝ} {b : WithTop ℝ}
    (hf : LocallyIntegrable .complex f a b) (ha : AbsoluteConverges .complex f a b)
    (lam : ℝ) :
    Converges .complex
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b ∧
    AbsoluteConverges .complex
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b := by
  have habs : AbsoluteConverges .complex
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b := by
    change Converges .real
      (fun x => ‖f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))‖) a b
    rw [oscillatory_norm_function]
    exact ha
  exact ⟨absolute_converges .complex _ a b (oscillatory_locally_integrable hf lam) habs,
    habs⟩

/-- A single regular truncation approximates every frequency, uniformly.
The left and right cutoffs are chosen from separate absolute endpoint limits. -/
theorem oscillatory_uniform_truncation {f : ℝ → ℂ}
    {a : WithBot ℝ} {b : WithTop ℝ}
    (hf : LocallyIntegrable .complex f a b) (ha : AbsoluteConverges .complex f a b)
    (H : ∀ lam : ℝ, Converges .complex
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u v : RegularPoint a b, ∃ hp : ComplexIntegrable f u.val v.val,
      ∀ lam : ℝ,
        ‖@Sub.sub ℂ _ (integral .complex _ a b (H lam))
          (complexIntegral _ (oscillatory_product_integrable hp lam))‖ < ε := by
  obtain ⟨A, hn, c, Al, Ar, hAl, hAr, _⟩ := ha
  change ℝ at A Al Ar
  obtain ⟨hnleft, hleft⟩ := hAl
  obtain ⟨hnright, hright⟩ := hAr
  obtain ⟨r, hr⟩ := hleft (ε / 2) (half_pos hε)
  obtain ⟨s, hs⟩ := hright (ε / 2) (half_pos hε)
  obtain ⟨u, hur, _⟩ := left_earlier r r
  obtain ⟨v, hsv, _⟩ := right_later s s
  let up : RegularPoint a b := ⟨u.val, u.property.1,
    (WithTop.coe_le_coe.mpr u.property.2.le).trans_lt c.property.2⟩
  let vp : RegularPoint a b := ⟨v.val,
    c.property.1.trans_le (WithBot.coe_le_coe.mpr v.property.1.le), v.property.2⟩
  have huv : u.val ≤ v.val := u.property.2.le.trans v.property.1.le
  let hp : ComplexIntegrable f u.val v.val := hf _ _ u.property.1 huv v.property.2
  have hsmallL : |realIntegral _ (hnleft.2 u) - Al| < ε / 2 := hr u hur
  have hsmallR : |realIntegral _ (hnright.2 v) - Ar| < ε / 2 := hs v hsv
  refine ⟨up, vp, hp, fun lam => ?_⟩
  let g := fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))
  have hg : LocallyIntegrable .complex g a b := oscillatory_locally_integrable hf lam
  have hgn : (fun x => ‖g x‖) = (fun x => ‖f x‖) := oscillatory_norm_function f lam
  have hng : LocallyIntegrable .real (fun x => ‖g x‖) a b := by rw [hgn]; exact hn
  obtain ⟨l, q, hl, hq, heq⟩ :=
    ((hasIntegral_at_every_split .complex g a b c _).mp
      (integral_hasValue .complex g a b (H lam))).2
  change ℂ at l q
  have hAgl : LeftHasIntegral .real (fun x => ‖g x‖) a c.val Al := by rw [hgn]; exact ⟨hnleft, hleft⟩
  have hAgr : RightHasIntegral .real (fun x => ‖g x‖) c.val b Ar := by rw [hgn]; exact ⟨hnright, hright⟩
  let hpl : ComplexIntegrable g u.val c.val :=
    oscillatory_product_integrable (hf _ _ u.property.1 u.property.2.le c.property.2) lam
  let hpr : ComplexIntegrable g c.val v.val :=
    oscillatory_product_integrable (hf _ _ c.property.1 v.property.1.le v.property.2) lam
  have hnl : RealIntegrable (fun x => ‖g x‖) u.val c.val := by rw [hgn]; exact hnleft.2 u
  have hnr : RealIntegrable (fun x => ‖g x‖) c.val v.val := by rw [hgn]; exact hnright.2 v
  have hbL := left_truncation_remainder_bound hg hng c up u.property.2.le hl hAgl hpl hnl
  have hbR := right_truncation_remainder_bound hg hng c vp v.property.1.le hq hAgr hpr hnr
  have heL : realIntegral _ hnl = realIntegral _ (hnleft.2 u) :=
    realIntegral_congr hnl (hnleft.2 u) hgn
  have heR : realIntegral _ hnr = realIntegral _ (hnright.2 v) :=
    realIntegral_congr hnr (hnright.2 v) hgn
  rw [heL] at hbL
  rw [heR] at hbR
  have hsplit := scalar_integral_split .complex g u.property.2.le v.property.1.le
    (oscillatory_product_integrable hp lam) hpl hpr
  let W : ℂ := integral .complex g a b (H lam)
  have heq' : W = l + q := heq
  have hsplit' : complexIntegral g (oscillatory_product_integrable hp lam) =
      complexIntegral g hpl + complexIntegral g hpr := hsplit
  change ‖W - complexIntegral g (oscillatory_product_integrable hp lam)‖ < ε
  rw [heq', hsplit']
  have hid : l + q - (complexIntegral g hpl + complexIntegral g hpr) =
      (l - complexIntegral g hpl) + (q - complexIntegral g hpr) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt
    (by have h1 := hbL.trans_lt hsmallL; have h2 := hbR.trans_lt hsmallR; linarith)

/-- Improper Riemann–Lebesgue for complex amplitudes and finite endpoints. -/
theorem riemann_lebesgue_improper_complex :
    Specs.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper.complexRiemannLebesgueImproper := by
  intro f a b hf ha
  let H := fun lam => (oscillatory_absolute_converges hf ha lam).1
  refine ⟨H, fun lam => (oscillatory_absolute_converges hf ha lam).2, ?_⟩
  intro ε hε
  obtain ⟨u, v, hp, herr⟩ := oscillatory_uniform_truncation hf ha H (half_pos hε)
  obtain ⟨K, hK⟩ := riemann_lebesgue_complex f hp
  obtain ⟨R, hR, hsmall⟩ := hK (ε / 2) (half_pos hε)
  refine ⟨R, hR, fun lam hlam => ?_⟩
  have hproper : ‖complexIntegral _ (oscillatory_product_integrable hp lam)‖ < ε / 2 :=
    hsmall lam hlam
  have herror := herr lam
  have htri := norm_add_le
    (@Sub.sub ℂ _ (integral .complex _ (a : WithBot ℝ) (b : WithTop ℝ) (H lam))
      (complexIntegral _ (oscillatory_product_integrable hp lam)))
    (complexIntegral _ (oscillatory_product_integrable hp lam))
  rw (transparency := .all) [sub_add_cancel] at htri
  exact htri.trans_lt (by linarith)

/-- Real amplitudes use the same theorem through the canonical embedding. -/
theorem riemann_lebesgue_improper_real :
    Specs.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper.realRiemannLebesgueImproper := by
  intro f a b hf ha
  have hfc : LocallyIntegrable .complex (fun x => (f x : ℂ))
      (a : WithBot ℝ) (b : WithTop ℝ) := by
    intro u v hau huv hvb
    exact ⟨hf u v hau huv hvb, (real_zero_value huv).choose⟩
  have hac : AbsoluteConverges .complex (fun x => (f x : ℂ))
      (a : WithBot ℝ) (b : WithTop ℝ) := by
    change Converges .real (fun x => ‖(f x : ℂ)‖) _ _
    change Converges .real (fun x => ‖f x‖) (a : WithBot ℝ) (b : WithTop ℝ) at ha
    simpa only [Complex.norm_real] using ha
  exact riemann_lebesgue_improper_complex _ a b hfc hac

end SingleVariableAnalysis.Riemann.Improper
