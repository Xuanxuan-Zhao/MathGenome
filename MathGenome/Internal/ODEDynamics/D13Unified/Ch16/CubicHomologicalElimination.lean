import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.CubicHomologicalElimination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace D13Unified.Ch16.CubicHomologicalElimination

open Complex
open scoped ComplexConjugate
open Specs.D13Unified.Ch16.CubicHomologicalElimination

/-- The imaginary part alone detects every divisor which is divided by. -/
theorem divisor_ne_zero (a b : ℝ) (hb : b ≠ 0) (j k : ℕ)
    (hjk : (j : ℤ) - k - 1 ≠ 0) : divisor a b j k ≠ 0 := by
  intro h
  have hIm := congrArg Complex.im h
  have hw : (j : ℝ) - k - 1 ≠ 0 := by exact_mod_cast hjk
  simp [divisor, hw, hb] at hIm

theorem nonzeroDivisors : NonzeroDivisors := by
  intro a b hb
  constructor
  · intro j k hjk
    apply divisor_ne_zero a b (ne_of_gt hb) j k
    omega
  · intro j k hjk hpair
    apply divisor_ne_zero a b (ne_of_gt hb) j k
    intro hw
    apply hpair
    apply Prod.ext <;> omega

theorem neighborhoodDivisors : NeighborhoodDivisors := by
  intro a b hb hb0
  have hn : ∀ᶠ μ in nhds (0 : ℝ), 0 < b μ := hb.eventually (lt_mem_nhds hb0)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨ε, hε, fun μ hμ => nonzeroDivisors (a μ) (b μ) ?_⟩
  apply he
  simpa [Real.dist_eq] using hμ

/-- The homological operator is computed using the real derivative, so the
conjugate variable acquires the conjugate eigenvalue. -/
theorem quadratic_homological (a b : ℝ) (h : Quadratic) (z : ℂ) :
    h.directional z (eigenvalue a b * z) - eigenvalue a b * h.eval z =
      divisor a b 2 0 * h.c20 * z ^ 2 +
      divisor a b 1 1 * h.c11 * z * conj z +
      divisor a b 0 2 * h.c02 * conj z ^ 2 := by
  simp [Quadratic.directional, Quadratic.eval, eigenvalue, divisor,
    map_add, map_mul]
  ring

theorem cubic_homological (a b : ℝ) (h : Cubic) (z : ℂ) :
    h.directional z (eigenvalue a b * z) - eigenvalue a b * h.eval z =
      divisor a b 3 0 * h.c30 * z ^ 3 +
      divisor a b 2 1 * h.c21 * z ^ 2 * conj z +
      divisor a b 1 2 * h.c12 * z * conj z ^ 2 +
      divisor a b 0 3 * h.c03 * conj z ^ 3 := by
  simp [Cubic.directional, Cubic.eval, eigenvalue, divisor,
    map_add, map_mul]
  ring

theorem quadratic_change_solves (a b : ℝ) (q : Quadratic) (hb : 0 < b) (z : ℂ) :
    (quadraticChange a b q).directional z (eigenvalue a b * z) -
      eigenvalue a b * (quadraticChange a b q).eval z = q.eval z := by
  have hd := (nonzeroDivisors a b hb).1
  rw [quadratic_homological]
  simp [quadraticChange, Quadratic.eval,
    mul_div_cancel₀, hd 2 0 (by decide), hd 1 1 (by decide), hd 0 2 (by decide)]

/-- This expansion includes both conjugate coefficients; it does not treat
z and its conjugate as independent complex differentiable variables. -/
theorem cubic_after_quadratic_eval (q : Quadratic) (p : Cubic) (h : Quadratic) (z : ℂ) :
    (cubicAfterQuadratic q p h).eval z = p.eval z + q.directional z (h.eval z) := by
  simp [cubicAfterQuadratic, Cubic.eval, Quadratic.directional, Quadratic.eval,
    map_add, map_mul, map_pow]
  ring

theorem cubic_change_solves (a b : ℝ) (g : Cubic) (hb : 0 < b) (z : ℂ) :
    (cubicChange a b g).directional z (eigenvalue a b * z) -
      eigenvalue a b * (cubicChange a b g).eval z =
        g.eval z - g.c21 * z ^ 2 * conj z := by
  have hd := (nonzeroDivisors a b hb).2
  rw [cubic_homological]
  simp [cubicChange, Cubic.eval, mul_div_cancel₀,
    hd 3 0 (by decide) (by decide), hd 1 2 (by decide) (by decide),
    hd 0 3 (by decide) (by decide)]
  ring

theorem finiteElimination : FiniteElimination := by
  intro a b q p hb
  dsimp only
  let h := quadraticChange a b q
  let g := cubicAfterQuadratic q p h
  let t := cubicChange a b g
  have hq (z : ℂ) := quadratic_change_solves a b q hb z
  have hg (z : ℂ) := cubic_after_quadratic_eval q p h z
  have ht (z : ℂ) := cubic_change_solves a b g hb z
  refine ⟨?_, hg, ?_, ?_⟩
  · intro z
    linear_combination -hq z
  · intro z
    have heq : eigenvalue a b * h.eval z + q.eval z =
        h.directional z (eigenvalue a b * z) := by linear_combination -hq z
    rw [heq]
    linear_combination -hg z
  · intro z
    change g.eval z + eigenvalue a b * t.eval z -
      t.directional z (eigenvalue a b * z) = g.c21 * z ^ 2 * conj z
    linear_combination -ht z

variable {n : WithTop ℕ∞}

theorem quadratic_contDiff (q : Quadratic) : ContDiff ℝ n q.eval := by
  have hc : ContDiff ℝ n (conj : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold Quadratic.eval
  fun_prop

theorem cubic_contDiff (p : Cubic) : ContDiff ℝ n p.eval := by
  have hc : ContDiff ℝ n (conj : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold Cubic.eval
  fun_prop

theorem quadratic_fderiv (q : Quadratic) (z v : ℂ) :
    fderiv ℝ q.eval z v = q.directional z v := by
  have hi := hasFDerivAt_id (𝕜 := ℝ) z
  have hc := Complex.conjCLE.hasFDerivAt (x := z)
  have hd := (((hi.pow 2).const_mul q.c20).add
    ((hi.const_mul q.c11).mul hc)).add ((hc.pow 2).const_mul q.c02)
  change HasFDerivAt q.eval _ z at hd
  rw [hd.fderiv]
  simp [Quadratic.directional, smul_eq_mul]
  ring

theorem cubic_fderiv (p : Cubic) (z v : ℂ) :
    fderiv ℝ p.eval z v = p.directional z v := by
  have hi := hasFDerivAt_id (𝕜 := ℝ) z
  have hc := Complex.conjCLE.hasFDerivAt (x := z)
  have hd := ((((hi.pow 3).const_mul p.c30).add
    (((hi.pow 2).const_mul p.c21).mul hc)).add
    ((hi.const_mul p.c12).mul (hc.pow 2))).add ((hc.pow 3).const_mul p.c03)
  change HasFDerivAt p.eval _ z at hd
  rw [hd.fderiv]
  simp [Cubic.directional, smul_eq_mul]
  ring

theorem quadratic_fderiv_zero (q : Quadratic) : fderiv ℝ q.eval 0 = 0 := by
  ext v
  simp [quadratic_fderiv, Quadratic.directional]

theorem cubic_fderiv_zero (p : Cubic) : fderiv ℝ p.eval 0 = 0 := by
  ext v
  simp [cubic_fderiv, Cubic.directional]

theorem spatialLocalInverses : SpatialLocalInverses := by
  have inv (f : ℂ → ℂ) (h0 : f 0 = 0) (hf : ContDiff ℝ ⊤ f)
      (hd : fderiv ℝ f 0 = 0) :
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        (e : ℂ → ℂ) = (fun z => z + f z) ∧ 0 ∈ e.source ∧
        ContDiff ℝ ⊤ (e : ℂ → ℂ) ∧ ContDiffAt ℝ ⊤ e.symm 0 := by
    have hs : ContDiff ℝ ⊤ (fun z => z + f z) := contDiff_id.add hf
    have hd0 : HasFDerivAt (fun z => z + f z)
        (ContinuousLinearEquiv.refl ℝ ℂ : ℂ →L[ℝ] ℂ) 0 := by
      simpa [hd] using (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).fun_add
        (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
    let e := hs.contDiffAt.toOpenPartialHomeomorph _ hd0 (by simp)
    refine ⟨e, rfl, hs.contDiffAt.mem_toOpenPartialHomeomorph_source hd0 (by simp), hs, ?_⟩
    have hInv := hs.contDiffAt.to_localInverse hd0 (by simp)
    change ContDiffAt ℝ ⊤ (hs.contDiffAt.localInverse hd0 (by simp)) 0
    simpa [h0] using hInv
  constructor
  · intro q
    exact inv q.eval (by simp [Quadratic.eval]) (quadratic_contDiff q) (quadratic_fderiv_zero q)
  · intro p
    exact inv p.eval (by simp [Cubic.eval]) (cubic_contDiff p) (cubic_fderiv_zero p)

theorem divisor_contDiffAt (a b : ℝ → ℝ) (μ : ℝ)
    (ha : ContDiffAt ℝ n a μ) (hb : ContDiffAt ℝ n b μ) (j k : ℕ) :
    ContDiffAt ℝ n (fun ν => divisor (a ν) (b ν) j k) μ := by
  have ha' := Complex.ofRealCLM.contDiff.contDiffAt.comp μ ha
  have hb' := Complex.ofRealCLM.contDiff.contDiffAt.comp μ hb
  unfold divisor
  exact (contDiffAt_const.mul ha').add (contDiffAt_const.mul hb')

theorem quadratic_change_regular (a b : ℝ → ℝ) (q : ℝ → Quadratic) (μ : ℝ)
    (ha : ContDiffAt ℝ n a μ) (hb : ContDiffAt ℝ n b μ) (hpos : 0 < b μ)
    (hq : QuadraticRegular n q μ) :
    QuadraticRegular n (fun ν => quadraticChange (a ν) (b ν) (q ν)) μ := by
  rcases hq with ⟨h20, h11, h02⟩
  have hdiv := divisor_contDiffAt a b μ ha hb
  have hn := (nonzeroDivisors (a μ) (b μ) hpos).1
  unfold QuadraticRegular quadraticChange
  simp only [div_eq_mul_inv]
  exact ⟨h20.mul ((hdiv 2 0).inv (hn 2 0 rfl)),
    h11.mul ((hdiv 1 1).inv (hn 1 1 rfl)), h02.mul ((hdiv 0 2).inv (hn 0 2 rfl))⟩

theorem cubic_after_quadratic_regular (q h : ℝ → Quadratic) (p : ℝ → Cubic) (μ : ℝ)
    (hq : QuadraticRegular n q μ) (hh : QuadraticRegular n h μ)
    (hp : CubicRegular n p μ) :
    CubicRegular n (fun ν => cubicAfterQuadratic (q ν) (p ν) (h ν)) μ := by
  rcases hq with ⟨q20, q11, q02⟩
  rcases hh with ⟨h20, h11, h02⟩
  rcases hp with ⟨p30, p21, p12, p03⟩
  have hc20 := Complex.conjCLE.contDiff.contDiffAt.comp μ h20
  have hc11 := Complex.conjCLE.contDiff.contDiffAt.comp μ h11
  have hc02 := Complex.conjCLE.contDiff.contDiffAt.comp μ h02
  unfold CubicRegular cubicAfterQuadratic
  exact ⟨(p30.add ((contDiffAt_const.mul q20).mul h20)).add (q11.mul hc02),
    (((p21.add ((contDiffAt_const.mul q20).mul h11)).add (q11.mul h20)).add
      (q11.mul hc11)).add ((contDiffAt_const.mul q02).mul hc02),
    (((p12.add ((contDiffAt_const.mul q20).mul h02)).add (q11.mul h11)).add
      (q11.mul hc20)).add ((contDiffAt_const.mul q02).mul hc11),
    (p03.add (q11.mul h02)).add ((contDiffAt_const.mul q02).mul hc20)⟩

theorem cubic_change_regular (a b : ℝ → ℝ) (g : ℝ → Cubic) (μ : ℝ)
    (ha : ContDiffAt ℝ n a μ) (hb : ContDiffAt ℝ n b μ) (hpos : 0 < b μ)
    (hg : CubicRegular n g μ) :
    CubicRegular n (fun ν => cubicChange (a ν) (b ν) (g ν)) μ := by
  rcases hg with ⟨h30, _, h12, h03⟩
  have hdiv := divisor_contDiffAt a b μ ha hb
  have hn := (nonzeroDivisors (a μ) (b μ) hpos).2
  unfold CubicRegular cubicChange
  simp only [div_eq_mul_inv]
  exact ⟨h30.mul ((hdiv 3 0).inv (hn 3 0 rfl (by decide))), contDiffAt_const,
    h12.mul ((hdiv 1 2).inv (hn 1 2 rfl (by decide))),
    h03.mul ((hdiv 0 3).inv (hn 0 3 rfl (by decide)))⟩

theorem parameterCoefficients : ParameterCoefficients := by
  intro n a b q p μ ha hb hpos hq hp
  have hh := quadratic_change_regular a b q μ ha hb hpos hq
  have hg := cubic_after_quadratic_regular q _ p μ hq hh hp
  exact ⟨hh, hg, cubic_change_regular a b _ μ ha hb hpos hg, hg.2.1⟩

theorem quadratic_family_contDiffAt (q : ℝ → Quadratic) (μ : ℝ)
    (hq : QuadraticRegular n q μ) :
    ContDiffAt ℝ n (quadraticFamilyChange q) (μ, (0 : ℂ)) := by
  rcases hq with ⟨q20, q11, q02⟩
  have h20 := q20.comp (μ, (0 : ℂ)) contDiffAt_fst
  have h11 := q11.comp (μ, (0 : ℂ)) contDiffAt_fst
  have h02 := q02.comp (μ, (0 : ℂ)) contDiffAt_fst
  have hc : ContDiffAt ℝ n (fun x : ℝ × ℂ => conj x.2) (μ, (0 : ℂ)) :=
    Complex.conjCLE.contDiff.contDiffAt.comp _ contDiffAt_snd
  unfold quadraticFamilyChange Quadratic.eval
  exact contDiffAt_fst.prodMk (contDiffAt_snd.add
    (((h20.mul (contDiffAt_snd.pow 2)).add ((h11.mul contDiffAt_snd).mul hc)).add
      (h02.mul (hc.pow 2))))

theorem cubic_family_contDiffAt (p : ℝ → Cubic) (μ : ℝ)
    (hp : CubicRegular n p μ) :
    ContDiffAt ℝ n (cubicFamilyChange p) (μ, (0 : ℂ)) := by
  rcases hp with ⟨p30, p21, p12, p03⟩
  have h30 := p30.comp (μ, (0 : ℂ)) contDiffAt_fst
  have h21 := p21.comp (μ, (0 : ℂ)) contDiffAt_fst
  have h12 := p12.comp (μ, (0 : ℂ)) contDiffAt_fst
  have h03 := p03.comp (μ, (0 : ℂ)) contDiffAt_fst
  have hc : ContDiffAt ℝ n (fun x : ℝ × ℂ => conj x.2) (μ, (0 : ℂ)) :=
    Complex.conjCLE.contDiff.contDiffAt.comp _ contDiffAt_snd
  unfold cubicFamilyChange Cubic.eval
  exact contDiffAt_fst.prodMk (contDiffAt_snd.add
    ((((h30.mul (contDiffAt_snd.pow 3)).add
      ((h21.mul (contDiffAt_snd.pow 2)).mul hc)).add
      ((h12.mul contDiffAt_snd).mul (hc.pow 2))).add (h03.mul (hc.pow 3))))

theorem quadratic_family_hasFDerivAt (q : ℝ → Quadratic) (μ : ℝ) (hn : n ≠ 0)
    (hq : QuadraticRegular n q μ) :
    HasFDerivAt (quadraticFamilyChange q)
      (ContinuousLinearEquiv.refl ℝ (ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℝ × ℂ) (μ, (0 : ℂ)) := by
  rcases hq with ⟨q20, q11, q02⟩
  have hf : HasFDerivAt (@Prod.fst ℝ ℂ) (ContinuousLinearMap.fst ℝ ℝ ℂ) (μ, (0 : ℂ)) :=
    hasFDerivAt_fst
  have hz : HasFDerivAt (@Prod.snd ℝ ℂ) (ContinuousLinearMap.snd ℝ ℝ ℂ) (μ, (0 : ℂ)) :=
    hasFDerivAt_snd
  have hc := (Complex.conjCLE.hasFDerivAt (x := (0 : ℂ))).comp (μ, (0 : ℂ)) hz
  have h20 := (q20.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have h11 := (q11.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have h02 := (q02.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have hq0 : HasFDerivAt (fun x : ℝ × ℂ => (q x.1).eval x.2) (0 : (ℝ × ℂ) →L[ℝ] ℂ) (μ, (0 : ℂ)) := by
    unfold Quadratic.eval
    convert
      (((h20.fun_mul (hz.pow 2)).fun_add ((h11.fun_mul hz).fun_mul hc)).fun_add
        (h02.fun_mul (hc.pow 2))) using 1 <;> ext v <;> simp
  have hj := hf.prodMk (hz.fun_add hq0)
  unfold quadraticFamilyChange
  convert hj using 1 <;> ext v <;> simp

theorem cubic_family_hasFDerivAt (p : ℝ → Cubic) (μ : ℝ) (hn : n ≠ 0)
    (hp : CubicRegular n p μ) :
    HasFDerivAt (cubicFamilyChange p)
      (ContinuousLinearEquiv.refl ℝ (ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℝ × ℂ) (μ, (0 : ℂ)) := by
  rcases hp with ⟨p30, p21, p12, p03⟩
  have hf : HasFDerivAt (@Prod.fst ℝ ℂ) (ContinuousLinearMap.fst ℝ ℝ ℂ) (μ, (0 : ℂ)) :=
    hasFDerivAt_fst
  have hz : HasFDerivAt (@Prod.snd ℝ ℂ) (ContinuousLinearMap.snd ℝ ℝ ℂ) (μ, (0 : ℂ)) :=
    hasFDerivAt_snd
  have hc := (Complex.conjCLE.hasFDerivAt (x := (0 : ℂ))).comp (μ, (0 : ℂ)) hz
  have h30 := (p30.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have h21 := (p21.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have h12 := (p12.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have h03 := (p03.differentiableAt hn).hasFDerivAt.comp (μ, (0 : ℂ)) hf
  have hp0 : HasFDerivAt (fun x : ℝ × ℂ => (p x.1).eval x.2) (0 : (ℝ × ℂ) →L[ℝ] ℂ) (μ, (0 : ℂ)) := by
    unfold Cubic.eval
    convert
      ((((h30.fun_mul (hz.pow 3)).fun_add ((h21.fun_mul (hz.pow 2)).fun_mul hc)).fun_add
        ((h12.fun_mul hz).fun_mul (hc.pow 2))).fun_add (h03.fun_mul (hc.pow 3)))
      using 1 <;> ext v <;> simp
  have hj := hf.prodMk (hz.fun_add hp0)
  unfold cubicFamilyChange
  convert hj using 1 <;> ext v <;> simp

/-- Applying IFT on the product proves actual dependence of the inverse on μ. -/
theorem joint_inverse (f : ℝ × ℂ → ℝ × ℂ) (μ : ℝ) (hn : n ≠ 0)
    (hf : ContDiffAt ℝ n f (μ, 0))
    (hd : HasFDerivAt f (ContinuousLinearEquiv.refl ℝ (ℝ × ℂ) :
      (ℝ × ℂ) →L[ℝ] ℝ × ℂ) (μ, 0))
    (h0 : f (μ, 0) = (μ, 0)) (hparam : ∀ x, (f x).1 = x.1) :
    JointInverseAt n f μ := by
  let e := hf.toOpenPartialHomeomorph f hd hn
  refine ⟨e, rfl, hf.mem_toOpenPartialHomeomorph_source hd hn, hf, ?_, ?_⟩
  · change ContDiffAt ℝ n (hf.localInverse hd hn) (μ, 0)
    simpa only [h0] using hf.to_localInverse hd hn
  · intro y hy
    have he := congrArg Prod.fst (e.right_inv hy)
    change (f (e.symm y)).1 = y.1 at he
    rwa [hparam] at he

theorem parameterLocalInverses : ParameterLocalInverses := by
  intro n hn
  constructor
  · intro q μ hq
    exact joint_inverse (quadraticFamilyChange q) μ hn
      (quadratic_family_contDiffAt q μ hq) (quadratic_family_hasFDerivAt q μ hn hq)
      (by simp [quadraticFamilyChange, Quadratic.eval]) (fun _ => rfl)
  · intro p μ hp
    exact joint_inverse (cubicFamilyChange p) μ hn
      (cubic_family_contDiffAt p μ hp) (cubic_family_hasFDerivAt p μ hn hp)
      (by simp [cubicFamilyChange, Cubic.eval]) (fun _ => rfl)

theorem realPolynomialDerivatives : RealPolynomialDerivatives :=
  ⟨quadratic_fderiv, cubic_fderiv⟩

/-- An explicit triangular real linear equivalence with nonzero second diagonal. -/
noncomputable def triangularEquiv (d e : ℝ) (he : e ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => ⟨z.re + d * z.im, e * z.im⟩
      invFun := fun z => ⟨z.re - d * (z.im / e), z.im / e⟩
      map_add' := by intro z w; apply Complex.ext <;> simp <;> ring
      map_smul' := by intro c z; apply Complex.ext <;> simp [mul_add] <;> ring
      left_inv := by intro z; apply Complex.ext <;> simp [he]
      right_inv := by intro z; apply Complex.ext <;> simp [mul_div_cancel₀, he] }

theorem realLinearCoordinates : RealLinearCoordinates := by
  intro r s t u a b hb htrace hdet
  have hb0 := ne_of_gt hb
  have hu : u = 2 * a - r := by linarith
  have ht0 : t ≠ 0 := by
    intro h
    have hd := hdet
    rw [hu, h, mul_zero, sub_zero] at hd
    have hsq : (r - a) ^ 2 + b ^ 2 = 0 := by nlinarith [hd]
    nlinarith [sq_nonneg (r - a), sq_pos_of_pos hb]
  let d := (r - a) / b
  let e := t / b
  have he : e ≠ 0 := div_ne_zero ht0 hb0
  have h1 : d * b = r - a := div_mul_cancel₀ _ hb0
  have h2 : e * b = t := div_mul_cancel₀ _ hb0
  have h3 : r * d + s * e = -b + d * a := by
    dsimp [d, e]
    field_simp
    rw [hu] at hdet
    nlinarith [hdet]
  have h4 : t * d + u * e = e * a := by
    dsimp [d, e]
    field_simp
    linarith [htrace]
  refine ⟨triangularEquiv d e he, rfl, ?_, ?_⟩
  · rfl
  · intro z
    change planarLinearField r s t u ⟨z.re + d * z.im, e * z.im⟩ =
      ⟨(eigenvalue a b * z).re + d * (eigenvalue a b * z).im,
        e * (eigenvalue a b * z).im⟩
    apply Complex.ext
    · simp only [planarLinearField, eigenvalue, mul_re, mul_im, add_re, add_im,
        ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, one_mul,
        add_zero, zero_add, sub_zero]
      linear_combination -z.re * h1 + z.im * h3
    · simp only [planarLinearField, eigenvalue, mul_re, mul_im, add_re, add_im,
        ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, one_mul,
        add_zero, zero_add, sub_zero]
      linear_combination -z.re * h2 + z.im * h4

theorem linearCoordinatesRegular : LinearCoordinatesRegular := by
  intro n r t a b μ hr ht ha hb hb0 ht0
  have hd := (hr.sub ha).div hb hb0
  have he := ht.div hb hb0
  have he0 : t μ / b μ ≠ 0 := div_ne_zero ht0 hb0
  have hd' := hd.comp (μ, (0 : ℂ)) contDiffAt_fst
  have he' := he.comp (μ, (0 : ℂ)) contDiffAt_fst
  have hx : ContDiffAt ℝ n (fun x : ℝ × ℂ => x.2.re) (μ, 0) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ contDiffAt_snd
  have hy : ContDiffAt ℝ n (fun x : ℝ × ℂ => x.2.im) (μ, 0) :=
    Complex.imCLM.contDiff.contDiffAt.comp _ contDiffAt_snd
  have hi := hy.div he' he0
  constructor
  · unfold linearCoordinateForward
    exact contDiffAt_fst.prodMk
      (Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp _
        ((hx.add (hd'.mul hy)).prodMk (he'.mul hy)))
  · unfold linearCoordinateInverse
    exact contDiffAt_fst.prodMk
      (Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp _
        ((hx.sub (hd'.mul hi)).prodMk hi))

theorem real_linear_map_eq_entries (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = planarLinearField (A 1).re (A I).re (A 1).im (A I).im z := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul] 
  rw [hz, map_add, map_smul, map_smul]
  apply Complex.ext <;> simp [planarLinearField, Complex.real_smul] <;> ring

theorem real_matrix_charpoly_eval (r s t u : ℝ) (l : ℂ) :
    (!![(r : ℂ), (s : ℂ); (t : ℂ), (u : ℂ)]).charpoly.eval l =
      l ^ 2 - (r + u : ℝ) * l + (r * u - s * t : ℝ) := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.det_fin_two, map_add, map_sub, map_mul]

theorem real_matrix_root_invariants (r s t u a b : ℝ) (hb : 0 < b)
    (hroot : (!![(r : ℂ), (s : ℂ); (t : ℂ), (u : ℂ)]).charpoly.IsRoot
      (eigenvalue a b)) :
    r + u = 2 * a ∧ r * u - s * t = a ^ 2 + b ^ 2 := by
  rw [Polynomial.IsRoot, real_matrix_charpoly_eval] at hroot
  have hr := congrArg Complex.re hroot
  have hi := congrArg Complex.im hroot
  simp [eigenvalue, pow_two] at hr hi
  have ht : r + u = 2 * a := by nlinarith [ne_of_gt hb]
  refine ⟨ht, ?_⟩
  rw [ht] at hr
  nlinarith [hr]

theorem real_matrix_eigenvalues (r s t u a b : ℝ)
    (htrace : r + u = 2 * a) (hdet : r * u - s * t = a ^ 2 + b ^ 2) (l : ℂ) :
    Module.End.HasEigenvalue (!![(r : ℂ), (s : ℂ); (t : ℂ), (u : ℂ)]).toLin' l ↔
      l = eigenvalue a b ∨ l = conj (eigenvalue a b) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Polynomial.IsRoot, real_matrix_charpoly_eval, htrace, hdet]
  have heq : l ^ 2 - (2 * a : ℝ) * l + (a ^ 2 + b ^ 2 : ℝ) =
      (l - eigenvalue a b) * (l - conj (eigenvalue a b)) := by
    simp [eigenvalue, map_add, map_mul]
    ring_nf
    simp
  rw [heq, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem linearization_contDiffAt (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hF : ContDiffAt ℝ 5 F (μ, 0)) : ContDiffAt ℝ 4 (linearization F) μ := by
  exact hF.fderiv (g := fun _ : ℝ => (0 : ℂ)) contDiffAt_const (by norm_num)

theorem linearization_entries_regular (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hA : ContDiffAt ℝ n (linearization F) μ) :
    ContDiffAt ℝ n (fun ν => ((linearization F ν) 1).re) μ ∧
    ContDiffAt ℝ n (fun ν => ((linearization F ν) I).re) μ ∧
    ContDiffAt ℝ n (fun ν => ((linearization F ν) 1).im) μ ∧
    ContDiffAt ℝ n (fun ν => ((linearization F ν) I).im) μ := by
  have h1 := hA.clm_apply (contDiffAt_const (c := (1 : ℂ)))
  have hI := hA.clm_apply (contDiffAt_const (c := I))
  exact ⟨Complex.reCLM.contDiff.contDiffAt.comp μ h1,
    Complex.reCLM.contDiff.contDiffAt.comp μ hI,
    Complex.imCLM.contDiff.contDiffAt.comp μ h1,
    Complex.imCLM.contDiff.contDiffAt.comp μ hI⟩

theorem spectralFamilyCoordinates : SpectralFamilyCoordinates := by
  intro F ω hF hω heig
  let r : ℝ → ℝ := fun μ => ((linearization F μ) 1).re
  let s : ℝ → ℝ := fun μ => ((linearization F μ) I).re
  let t : ℝ → ℝ := fun μ => ((linearization F μ) 1).im
  let u : ℝ → ℝ := fun μ => ((linearization F μ) I).im
  let a := spectralReal F
  let b := spectralImag F
  let Q : ℝ → ℝ := fun μ => r μ * u μ - s μ * t μ - a μ ^ 2
  have heig' : (!![(r 0 : ℂ), (s 0 : ℂ); (t 0 : ℂ), (u 0 : ℂ)]).charpoly.IsRoot
      (eigenvalue 0 ω) := by
    simpa only [Matrix.charpoly_toLin', complexifiedLinearization, r, s, t, u] using
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig
  obtain ⟨htrace0, hdet0⟩ := real_matrix_root_invariants _ _ _ _ _ _ hω heig'
  have ha0 : a 0 = 0 := by
    change (r 0 + u 0) / 2 = 0
    rw [htrace0]; norm_num
  have hQ0 : Q 0 = ω ^ 2 := by dsimp [Q]; rw [hdet0, ha0]; ring
  have hb0 : b 0 = ω := by
    change Real.sqrt (Q 0) = ω
    rw [hQ0, Real.sqrt_sq (le_of_lt hω)]
  have hA := linearization_contDiffAt F 0 hF
  obtain ⟨hr, hs, ht, hu⟩ := linearization_entries_regular F 0 hA
  have ha : ContDiffAt ℝ 4 a 0 :=
    (hr.add hu).div contDiffAt_const (by norm_num)
  have hQ : ContDiffAt ℝ 4 Q 0 :=
    ((hr.mul hu).sub (hs.mul ht)).sub (ha.pow 2)
  have hQpos : 0 < Q 0 := by rw [hQ0]; positivity
  have hb : ContDiffAt ℝ 4 b 0 := hQ.sqrt (ne_of_gt hQpos)
  have hQevent : ∀ᶠ μ in nhds (0 : ℝ), 0 < Q μ :=
    hQ.continuousAt.eventually (lt_mem_nhds hQpos)
  have hevent : ∀ᶠ μ in nhds (0 : ℝ),
      0 < Q μ ∧ ContDiffAt ℝ 4 (linearization F) μ ∧
        ContDiffAt ℝ 4 a μ ∧ ContDiffAt ℝ 4 b μ :=
    hQevent.and ((hA.eventually (by norm_num)).and
      ((ha.eventually (by norm_num)).and (hb.eventually (by norm_num))))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ha0, hb0, ε, hε, ?_⟩
  intro μ hμ
  obtain ⟨hQμ, hAμ, haμ, hbμ⟩ := he (by simpa [Real.dist_eq] using hμ)
  have hbpos : 0 < b μ := Real.sqrt_pos.mpr hQμ
  have htrace : r μ + u μ = 2 * a μ := by
    change r μ + u μ = 2 * ((r μ + u μ) / 2)
    ring
  have hsq : b μ ^ 2 = Q μ := Real.sq_sqrt (le_of_lt hQμ)
  have hdet : r μ * u μ - s μ * t μ = a μ ^ 2 + b μ ^ 2 := by
    rw [hsq]; dsimp [Q]; ring
  have ht0 : t μ ≠ 0 := by
    intro ht0
    have hu' : u μ = 2 * a μ - r μ := by linarith [htrace]
    rw [hu', ht0, mul_zero, sub_zero] at hdet
    nlinarith [sq_nonneg (r μ - a μ), sq_pos_of_pos hbpos]
  obtain ⟨hrμ, _, htμ, _⟩ := linearization_entries_regular F μ hAμ
  have hreg := linearCoordinatesRegular 4 r t a b μ hrμ htμ haμ hbμ
    (ne_of_gt hbpos) ht0
  refine ⟨hbpos, haμ, hbμ, ?_, ?_, hreg⟩
  · exact real_matrix_eigenvalues _ _ _ _ _ _ htrace hdet
  · obtain ⟨S, hS, hSinv, hinter⟩ := realLinearCoordinates _ _ _ _ _ _ hbpos htrace hdet
    refine ⟨S, hS, hSinv, fun z => ?_⟩
    rw [real_linear_map_eq_entries]
    exact hinter z

theorem quadraticOfReal_eval (X Y Z : ℂ) (z : ℂ) :
    (quadraticOfReal X Y Z).eval z =
      X * (z.re : ℂ) ^ 2 + Y * z.re * z.im + Z * (z.im : ℂ) ^ 2 := by
  apply Complex.ext <;>
    simp [quadraticOfReal, Quadratic.eval,
      pow_two] <;> ring

theorem cubicOfReal_eval (X Y Z W : ℂ) (z : ℂ) :
    (cubicOfReal X Y Z W).eval z =
      X * (z.re : ℂ) ^ 3 + Y * (z.re : ℂ) ^ 2 * z.im +
      Z * z.re * (z.im : ℂ) ^ 2 + W * (z.im : ℂ) ^ 3 := by
  apply Complex.ext <;>
    simp [cubicOfReal, Cubic.eval,
      pow_succ] <;> ring

theorem bilinear_diagonal (B : ℂ [×2]→L[ℝ] ℂ) (z : ℂ) :
    B (fun _ => z) = (z.re : ℂ) ^ 2 * B ![1, 1] +
      (z.re : ℂ) * z.im * (B ![1, I] + B ![I, 1]) +
      (z.im : ℂ) ^ 2 * B ![I, I] := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hvec : (fun _ : Fin 2 => z) = ![z.re • (1 : ℂ) + z.im • I,
      z.re • (1 : ℂ) + z.im • I] := by ext i; fin_cases i <;> exact hz
  rw [hvec]
  simp only [Matrix.vecCons, ← ContinuousMultilinearMap.curryLeft_apply, map_add, map_smul,
    add_apply, smul_apply]
  simp only [Complex.real_smul]
  ring

theorem trilinear_diagonal (C : ℂ [×3]→L[ℝ] ℂ) (z : ℂ) :
    C (fun _ => z) = (z.re : ℂ) ^ 3 * C ![1, 1, 1] +
      (z.re : ℂ) ^ 2 * z.im * (C ![1, 1, I] + C ![1, I, 1] + C ![I, 1, 1]) +
      (z.re : ℂ) * (z.im : ℂ) ^ 2 * (C ![1, I, I] + C ![I, 1, I] + C ![I, I, 1]) +
      (z.im : ℂ) ^ 3 * C ![I, I, I] := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hvec : (fun _ : Fin 3 => z) = ![z.re • (1 : ℂ) + z.im • I,
      z.re • (1 : ℂ) + z.im • I, z.re • (1 : ℂ) + z.im • I] := by
    ext i; fin_cases i <;> exact hz
  rw [hvec]
  simp only [Matrix.vecCons, ← ContinuousMultilinearMap.curryLeft_apply, map_add, map_smul,
    add_apply, smul_apply]
  simp only [Complex.real_smul]
  ring

theorem homogeneousJetRepresentation : HomogeneousJetRepresentation := by
  constructor
  · intro B z
    rw [quadraticOfBilinear, quadraticOfReal_eval, bilinear_diagonal]
    ring
  · intro C z
    rw [cubicOfTrilinear, cubicOfReal_eval, trilinear_diagonal]
    ring

theorem multilinear_family_eval_regular {d : ℕ}
    (B : ℝ → (ℝ × ℂ) [×d]→L[ℝ] ℂ) (v : Fin d → ℝ → ℝ × ℂ) (μ : ℝ)
    (hB : ContDiffAt ℝ n B μ) (hv : ∀ i, ContDiffAt ℝ n (v i) μ) :
    ContDiffAt ℝ n (fun ν => B ν (fun i => v i ν)) μ := by
  have he : ContDiff ℝ n (fun v : Fin d → ℝ × ℂ =>
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin d => ℝ × ℂ) ℂ v) := by
    exact ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (E := fun _ : Fin d => ℝ × ℂ) (F := ((ℝ × ℂ) [×d]→L[ℝ] ℂ) →L[ℝ] ℂ)
      (ContinuousLinearMap.id ℝ ((ℝ × ℂ) [×d]→L[ℝ] ℂ)).flipMultilinear
  exact (he.contDiffAt.comp μ (contDiffAt_pi.mpr hv)).clm_apply hB

theorem normalized_spatial_jet_eval_regular {d : ℕ}
    (F : ℝ × ℂ → ℂ) (S T : ℝ → ℂ →L[ℝ] ℂ) (μ : ℝ)
    (hF : ContDiffAt ℝ 5 F (μ, 0)) (hS : ContDiffAt ℝ 4 S μ)
    (hT : ContDiffAt ℝ 4 T μ) (hnd : n + d ≤ 5) (hn : n ≤ 4) (v : Fin d → ℂ) :
    ContDiffAt ℝ n (fun ν => normalizedSpatialJet F S T d ν v) μ := by
  have hD := (hF.iteratedFDeriv_right hnd).comp μ
    (contDiffAt_id.prodMk (contDiffAt_const (c := (0 : ℂ))))
  have hv (i : Fin d) : ContDiffAt ℝ n (fun ν => ((0 : ℝ), S ν (v i))) μ :=
    contDiffAt_const.prodMk ((hS.of_le hn).clm_apply contDiffAt_const)
  exact (hT.of_le hn).clm_apply (multilinear_family_eval_regular _ _ μ hD hv)

theorem taylorFamilyCoefficients : TaylorFamilyCoefficients := by
  intro F S T μ hF hS hT
  have h2 := normalized_spatial_jet_eval_regular (n := 3) F S T μ hF hS hT
    (d := 2) (by norm_num) (by norm_num)
  have h3 := normalized_spatial_jet_eval_regular (n := 2) F S T μ hF hS hT
    (d := 3) (by norm_num) (by norm_num)
  have qX := (h2 ![1, 1]).div_const 2
  have qY := ((h2 ![1, I]).add (h2 ![I, 1])).div_const 2
  have qZ := (h2 ![I, I]).div_const 2
  have pX := (h3 ![1, 1, 1]).div_const 6
  have pY := (((h3 ![1, 1, I]).add (h3 ![1, I, 1])).add (h3 ![I, 1, 1])).div_const 6
  have pZ := (((h3 ![1, I, I]).add (h3 ![I, 1, I])).add (h3 ![I, I, 1])).div_const 6
  have pW := (h3 ![I, I, I]).div_const 6
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold QuadraticRegular familyQuadratic quadraticOfBilinear quadraticOfReal
    exact ⟨((qX.sub (contDiffAt_const.mul qY)).sub qZ).div_const 4,
      (qX.add qZ).div_const 2, ((qX.add (contDiffAt_const.mul qY)).sub qZ).div_const 4⟩
  · unfold CubicRegular familyCubic cubicOfTrilinear cubicOfReal
    exact ⟨(((pX.sub (contDiffAt_const.mul pY)).sub pZ).add
        (contDiffAt_const.mul pW)).div_const 8,
      ((((contDiffAt_const.mul pX).sub (contDiffAt_const.mul pY)).add pZ).sub
        (contDiffAt_const.mul pW)).div_const 8,
      ((((contDiffAt_const.mul pX).add (contDiffAt_const.mul pY)).add pZ).add
        (contDiffAt_const.mul pW)).div_const 8,
      (((pX.add (contDiffAt_const.mul pY)).sub pZ).sub
        (contDiffAt_const.mul pW)).div_const 8⟩
  · intro z
    exact homogeneousJetRepresentation.1 _ z
  · intro z
    exact homogeneousJetRepresentation.2 _ z

theorem affine_spatial_iteratedFDeriv (F : ℝ × ℂ → ℂ)
    (g : ℂ →ᴬ[ℝ] ℝ × ℂ) (hF : ContDiffAt ℝ 5 F (g 0)) (d : ℕ) (hd : d ≤ 5) :
    iteratedFDeriv ℝ d (F ∘ g) 0 =
      (iteratedFDeriv ℝ d F (g 0)).compContinuousLinearMap (fun _ => g.contLinear) := by
  obtain ⟨U, hU, hxU, hFU⟩ := (hF.contDiffWithinAt (s := Set.univ)).contDiffOn' (m := 5) le_rfl (by norm_num)
  have hFU' : ContDiffOn ℝ 5 F U := by simpa using hFU
  have hV := hU.preimage g.continuous
  have hxV : (0 : ℂ) ∈ g ⁻¹' U := hxU
  have hcomp := (hFU'.ftaylorSeriesWithin hU.uniqueDiffOn).comp_continuousAffineMap g
  have hj := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := d)
    (by exact_mod_cast hd) hV.uniqueDiffOn hxV
  rw [iteratedFDerivWithin_of_isOpen d hV hxV] at hj
  change (iteratedFDerivWithin ℝ d F U (g 0)).compContinuousLinearMap _ = _ at hj
  rw [iteratedFDerivWithin_of_isOpen d hU hxU] at hj
  exact hj.symm

theorem normalizedTaylorJets : NormalizedTaylorJets := by
  intro F S T μ hF d hd
  let L := (ContinuousLinearMap.inr ℝ ℝ ℂ).comp (S μ)
  let g : ℂ →ᴬ[ℝ] ℝ × ℂ :=
    ContinuousAffineMap.const ℝ ℂ (μ, 0) + L.toContinuousAffineMap
  have hg (z : ℂ) : g z = (μ, S μ z) := by simp [g, L, ContinuousAffineMap.add_apply]
  have hgL : g.contLinear = L := by simp [g]
  have hg0 : g 0 = (μ, 0) := by simp [hg]
  have hFg : ContDiffAt ℝ 5 (F ∘ g) 0 := by
    have hinner : ContDiffAt ℝ 5 (fun z : ℂ => (μ, S μ z)) 0 :=
      contDiffAt_const.prodMk (S μ).contDiff.contDiffAt
    have hF' : ContDiffAt ℝ 5 F (μ, S μ 0) := by simpa using hF
    simpa only [Function.comp_def, hg] using hF'.comp 0 hinner
  suffices iteratedFDeriv ℝ d ((T μ) ∘ (F ∘ g)) 0 = normalizedSpatialJet F S T d μ by
    simpa only [linearNormalizedFamily, Function.comp_def, hg] using this
  rw [(T μ).iteratedFDeriv_comp_left hFg (by exact_mod_cast hd)]
  rw [affine_spatial_iteratedFDeriv F g (by simpa only [hg0] using hF) d hd, hgL, hg0]
  rfl

@[simp] theorem coordinateForwardCLM_apply (r t a b : ℝ) (z : ℂ) :
    coordinateForwardCLM r t a b z = linearCoordinateForward r t a b z := by
  apply Complex.ext <;> simp [coordinateForwardCLM, linearCoordinateForward, Complex.real_smul,
    mul_comm]

@[simp] theorem coordinateInverseCLM_apply (r t a b : ℝ) (z : ℂ) :
    coordinateInverseCLM r t a b z = linearCoordinateInverse r t a b z := by
  apply Complex.ext <;> simp [coordinateInverseCLM, linearCoordinateInverse,
    Complex.real_smul, div_eq_mul_inv] <;> ring

theorem coordinate_CLM_regular (r t a b : ℝ → ℝ) (μ : ℝ)
    (hr : ContDiffAt ℝ n r μ) (ht : ContDiffAt ℝ n t μ)
    (ha : ContDiffAt ℝ n a μ) (hb : ContDiffAt ℝ n b μ) (hb0 : b μ ≠ 0) (ht0 : t μ ≠ 0) :
    ContDiffAt ℝ n (fun ν => coordinateForwardCLM (r ν) (t ν) (a ν) (b ν)) μ ∧
    ContDiffAt ℝ n (fun ν => coordinateInverseCLM (r ν) (t ν) (a ν) (b ν)) μ := by
  have hd := (hr.sub ha).div hb hb0
  have he := ht.div hb hb0
  have he0 : t μ / b μ ≠ 0 := div_ne_zero ht0 hb0
  have hfor := Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp μ (hd.prodMk he)
  have hback := Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp μ
    ((hd.neg.div he he0).prodMk ((contDiffAt_const (c := (1 : ℝ))).div he he0))
  exact ⟨contDiffAt_const.add (contDiffAt_const.smulRight hfor),
    contDiffAt_const.add (contDiffAt_const.smulRight hback)⟩

theorem sourceTaylorData : SourceTaylorData := by
  intro F ω hF hω heig
  obtain ⟨_, _, ε₁, hε₁, hspec⟩ := spectralFamilyCoordinates F ω hF hω heig
  have hinc : ContinuousAt (fun μ : ℝ => (μ, (0 : ℂ))) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hFnear : ∀ᶠ μ in nhds (0 : ℝ), ContDiffAt ℝ 5 F (μ, (0 : ℂ)) :=
    hinc.tendsto.eventually (hF.eventually (by norm_num))
  obtain ⟨ε₂, hε₂, hdiff⟩ := Metric.eventually_nhds_iff.mp hFnear
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro μ hμ
  have hμ₁ := lt_of_lt_of_le hμ (min_le_left _ _)
  have hμ₂ := lt_of_lt_of_le hμ (min_le_right _ _)
  have hFμ := hdiff (by simpa [Real.dist_eq] using hμ₂)
  obtain ⟨hbpos, ha, hb, _, ⟨S, hS, hSinv, hinter⟩, _⟩ := hspec μ hμ₁
  obtain ⟨hr, _, ht, _⟩ := linearization_entries_regular F μ
    (linearization_contDiffAt F μ hFμ)
  have hfor (z : ℂ) : sourceForwardCLM F μ z = S z := by
    change coordinateForwardCLM _ _ _ _ z = S z
    rw [coordinateForwardCLM_apply]
    exact (congrFun hS z).symm
  have hback (z : ℂ) : sourceInverseCLM F μ z = S.symm z := by
    change coordinateInverseCLM _ _ _ _ z = S.symm z
    rw [coordinateInverseCLM_apply]
    exact (congrFun hSinv z).symm
  have ht0 : ((linearization F μ) 1).im ≠ 0 := by
    intro hzero
    have hsource : sourceForwardCLM F μ I = sourceForwardCLM F μ
        (⟨(((linearization F μ) 1).re - spectralReal F μ) / spectralImag F μ, 0⟩ : ℂ) := by
      simp [sourceForwardCLM, linearCoordinateForward, hzero]
    rw [hfor, hfor] at hsource
    have := congrArg Complex.im (S.injective hsource)
    simp at this
  obtain ⟨hSreg, hTreg⟩ := coordinate_CLM_regular _ _ _ _ μ hr ht ha hb
    (ne_of_gt hbpos) ht0
  obtain ⟨hq, hp, hqeval, hpeval⟩ := taylorFamilyCoefficients F
    (sourceForwardCLM F) (sourceInverseCLM F) μ hFμ hSreg hTreg
  refine ⟨hFμ, hbpos, hSreg, hTreg, hq, hp, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [normalizedTaylorJets F _ _ μ hFμ 2 (by decide)]
    exact hqeval z
  · intro z
    rw [normalizedTaylorJets F _ _ μ hFμ 3 (by decide)]
    exact hpeval z
  · intro z
    rw [hfor, hback]
    exact S.symm_apply_apply z
  · intro z
    rw [hback, hfor]
    exact S.apply_symm_apply z
  · intro z
    rw [hfor, hinter, hback]
    exact S.symm_apply_apply _

theorem quadratic_eval_add (q : Quadratic) (z w : ℂ) :
    q.eval (z + w) = q.eval z + q.directional z w + q.eval w := by
  simp [Quadratic.eval, Quadratic.directional, map_add]
  ring

theorem quadratic_directional_add (q : Quadratic) (z v w : ℂ) :
    q.directional z (v + w) = q.directional z v + q.directional z w := by
  simp [Quadratic.directional, map_add]
  ring

theorem cubic_directional_add (p : Cubic) (z v w : ℂ) :
    p.directional z (v + w) = p.directional z v + p.directional z w := by
  simp [Cubic.directional, map_add]
  ring

theorem quadratic_change_fderiv_apply (h : Quadratic) (z v : ℂ) :
    fderiv ℝ (fun w => w + h.eval w) z v = v + h.directional z v := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) z).fun_add
    (((quadratic_contDiff h : ContDiff ℝ 1 h.eval).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt)
  change HasFDerivAt (fun w => w + h.eval w) _ z at hd
  rw [hd.fderiv]
  simp [quadratic_fderiv]

theorem cubic_change_fderiv_apply (t : Cubic) (z v : ℂ) :
    fderiv ℝ (fun w => w + t.eval w) z v = v + t.directional z v := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) z).fun_add
    (((cubic_contDiff t : ContDiff ℝ 1 t.eval).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt)
  change HasFDerivAt (fun w => w + t.eval w) _ z at hd
  rw [hd.fderiv]
  simp [cubic_fderiv]

theorem actualPullbackIdentities : ActualPullbackIdentities := by
  intro F a b q p hb
  dsimp only
  let l := eigenvalue a b
  let h := quadraticChange a b q
  let g := cubicAfterQuadratic q p h
  let t := cubicChange a b g
  constructor
  · intro z hinv
    change (fderiv ℝ (fun w => w + h.eval w) z).inverse (F (z + h.eval z)) -
      (l * z + g.eval z) = _
    rw [← hinv.inverse_apply_self (l * z + g.eval z), ← map_sub]
    congr 1
    rw [quadratic_change_fderiv_apply, quadratic_directional_add, quadratic_eval_add]
    have hq := quadratic_change_solves a b q hb z
    have hg := cubic_after_quadratic_eval q p h z
    change h.directional z (l * z) - l * h.eval z = q.eval z at hq
    change g.eval z = p.eval z + q.directional z (h.eval z) at hg
    linear_combination -hq - hg
  · intro z hinv
    change (fderiv ℝ (fun w => w + t.eval w) z).inverse (F (z + t.eval z)) -
      (l * z + g.c21 * z ^ 2 * conj z) = _
    rw [← hinv.inverse_apply_self (l * z + g.c21 * z ^ 2 * conj z), ← map_sub]
    congr 1
    rw [cubic_change_fderiv_apply, cubic_directional_add]
    have ht := cubic_change_solves a b g hb z
    change t.directional z (l * z) - l * t.eval z =
      g.eval z - g.c21 * z ^ 2 * conj z at ht
    linear_combination -ht

theorem quadraticRegular_of_le {m n : WithTop ℕ∞} {q : ℝ → Quadratic} {μ : ℝ}
    (hq : QuadraticRegular n q μ) (hmn : m ≤ n) : QuadraticRegular m q μ :=
  ⟨hq.1.of_le hmn, hq.2.1.of_le hmn, hq.2.2.of_le hmn⟩

theorem sourceHomologicalData : SourceHomologicalData := by
  intro F ω hF hω heig
  dsimp only
  let a := spectralReal F
  let b := spectralImag F
  let q := familyQuadratic F (sourceForwardCLM F) (sourceInverseCLM F)
  let p := familyCubic F (sourceForwardCLM F) (sourceInverseCLM F)
  let h := fun μ => quadraticChange (a μ) (b μ) (q μ)
  let g := fun μ => cubicAfterQuadratic (q μ) (p μ) (h μ)
  let t := fun μ => cubicChange (a μ) (b μ) (g μ)
  obtain ⟨ε₁, hε₁, hdata⟩ := sourceTaylorData F ω hF hω heig
  obtain ⟨_, _, ε₂, hε₂, hspec⟩ := spectralFamilyCoordinates F ω hF hω heig
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro μ hμ
  obtain ⟨_, hb, _, _, hq, hp, _⟩ :=
    hdata μ (lt_of_lt_of_le hμ (min_le_left _ _))
  obtain ⟨_, ha, hbreg, _⟩ := hspec μ (lt_of_lt_of_le hμ (min_le_right _ _))
  have hh : QuadraticRegular 3 h μ := quadratic_change_regular a b q μ
    (ha.of_le (by norm_num)) (hbreg.of_le (by norm_num)) hb hq
  have hg : CubicRegular 2 g μ := cubic_after_quadratic_regular q h p μ
    (quadraticRegular_of_le hq (by norm_num))
    (quadraticRegular_of_le hh (by norm_num)) hp
  have ht : CubicRegular 2 t μ := cubic_change_regular a b g μ
    (ha.of_le (by norm_num)) (hbreg.of_le (by norm_num)) hb hg
  exact ⟨hb, hh, hg, ht, hg.2.1,
    (parameterLocalInverses 3 (by norm_num)).1 h μ hh,
    (parameterLocalInverses 2 (by norm_num)).2 t μ ht,
    (nonzeroDivisors (a μ) (b μ) hb).1, (nonzeroDivisors (a μ) (b μ) hb).2⟩

theorem pullback_contDiffAt (F H : ℂ → ℂ) (hF : ContDiffAt ℝ n F 0)
    (hH : ContDiffAt ℝ ⊤ H 0) (h0 : H 0 = 0)
    (hd : fderiv ℝ H 0 = ContinuousLinearMap.id ℝ ℂ) :
    ContDiffAt ℝ n (nonlinearPullback F H) 0 := by
  have hi : ContDiffAt ℝ n ContinuousLinearMap.inverse (fderiv ℝ H 0) := by
    rw [hd]
    exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ ℂ)
  have hJ : ContDiffAt ℝ n (fun z => fderiv ℝ H z) 0 :=
    hH.fderiv_right (by exact le_top)
  have hFH : ContDiffAt ℝ n (fun z => F (H z)) 0 := by
    apply ContDiffAt.comp 0 _ (hH.of_le le_top)
    simpa [h0] using hF
  exact (hi.comp 0 hJ).clm_apply hFH

theorem actualPullbackRegularity : ActualPullbackRegularity := by
  intro F hF
  constructor
  · intro h
    apply pullback_contDiffAt F _ hF
      (contDiff_id.add (quadratic_contDiff h)).contDiffAt
      (by simp [Quadratic.eval])
    ext v
    simp [quadratic_change_fderiv_apply, Quadratic.directional]
  · intro t
    apply pullback_contDiffAt F _ hF
      (contDiff_id.add (cubic_contDiff t)).contDiffAt
      (by simp [Cubic.eval])
    ext v
    simp [cubic_change_fderiv_apply, Cubic.directional]

theorem linearNormalizedFamily_fderiv (F : ℝ × ℂ → ℂ)
    (S T : ℝ → ℂ →L[ℝ] ℂ) (μ : ℝ) (hF : ContDiffAt ℝ 5 F (μ, 0)) (z : ℂ) :
    fderiv ℝ (fun w => linearNormalizedFamily F S T (μ, w)) 0 z =
      T μ (linearization F μ (S μ z)) := by
  have hsp : ContDiffAt ℝ 5 (fun w : ℂ => F (μ, w)) 0 :=
    hF.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hsp' : HasFDerivAt (fun w : ℂ => F (μ, w)) (linearization F μ) (S μ 0) := by
    simpa [linearization] using (hsp.differentiableAt (by norm_num)).hasFDerivAt
  have hd := (T μ).hasFDerivAt.comp (0 : ℂ)
    (hsp'.comp (0 : ℂ) (S μ).hasFDerivAt)
  change HasFDerivAt (fun w => linearNormalizedFamily F S T (μ, w)) _ 0 at hd
  rw [hd.fderiv]
  rfl

theorem sourceNormalizedLinearJet : SourceNormalizedLinearJet := by
  intro F ω hF hω heig heq
  obtain ⟨ε₁, hε₁, hdata⟩ := sourceTaylorData F ω hF hω heig
  obtain ⟨ε₂, hε₂, hzero⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro μ hμ
  obtain ⟨hFμ, _, _, _, _, _, _, _, _, _, hlin⟩ :=
    hdata μ (lt_of_lt_of_le hμ (min_le_left _ _))
  have heqμ : F (μ, 0) = 0 := hzero (by
    simpa [Real.dist_eq] using lt_of_lt_of_le hμ (min_le_right ε₁ ε₂))
  refine ⟨by simp [linearNormalizedFamily, heqμ], ?_⟩
  intro z
  rw [linearNormalizedFamily_fderiv F _ _ μ hFμ z]
  exact hlin z

/-- Restricting a local spatial jet to a real ray gives its diagonal values. -/
theorem iteratedDeriv_ray (F : ℂ → ℂ) (hF : ContDiffAt ℝ 5 F 0)
    (v : ℂ) (d : ℕ) (hd : d ≤ 5) :
    iteratedDeriv d (fun s : ℝ => F (s • v)) 0 =
      iteratedFDeriv ℝ d F 0 (fun _ => v) := by
  let L : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  let g : ℝ →ᴬ[ℝ] ℂ := L.toContinuousAffineMap
  obtain ⟨U, hU, hxU, hFU⟩ := (hF.contDiffWithinAt (s := Set.univ)).contDiffOn' (m := 5) le_rfl (by norm_num)
  have hFU' : ContDiffOn ℝ 5 F U := by simpa using hFU
  have hV := hU.preimage g.continuous
  have hxV : (0 : ℝ) ∈ g ⁻¹' U := by simpa [g, L] using hxU
  have hcomp := (hFU'.ftaylorSeriesWithin hU.uniqueDiffOn).comp_continuousAffineMap g
  have hj := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := d)
    (by exact_mod_cast hd) hV.uniqueDiffOn hxV
  rw [iteratedFDerivWithin_of_isOpen d hV hxV] at hj
  change (iteratedFDerivWithin ℝ d F U (g 0)).compContinuousLinearMap _ = _ at hj
  rw [iteratedFDerivWithin_of_isOpen d hU (by simpa [g, L] using hxU)] at hj
  have he := congrArg (fun B : ℝ [×d]→L[ℝ] ℂ => B (fun _ => 1)) hj
  simpa [iteratedDeriv, g, L, Function.comp_def] using he.symm

theorem iteratedDeriv_linear_comp (L : ℂ →L[ℝ] ℂ) (f : ℝ → ℂ)
    (hf : ContDiffAt ℝ 5 f 0) (d : ℕ) (hd : d ≤ 5) :
    iteratedDeriv d (fun s => L (f s)) 0 = L (iteratedDeriv d f 0) := by
  have h := congrArg (fun B : ℝ [×d]→L[ℝ] ℂ => B (fun _ => 1))
    (L.iteratedFDeriv_comp_left hf (by exact_mod_cast hd))
  exact h

/-- Differentiating a monomial times a smooth curve at zero. -/
theorem iteratedDeriv_monomial_mul (f : ℝ → ℂ) (hf : ContDiffAt ℝ 5 f 0)
    (d n : ℕ) (hn : n ≤ 5) :
    iteratedDeriv n (fun s : ℝ => s ^ d • f s) 0 =
      ∑ i ∈ Finset.range (n + 1), n.choose i •
        ((d.descFactorial i : ℝ) * (0 : ℝ) ^ (d - i)) • iteratedDeriv (n-i) f 0 := by
  have h := iteratedDerivWithin_smul (𝕜 := ℝ) (𝔸 := ℝ) (n := n) (f := fun s : ℝ => s ^ d)
    (g := f) (Set.mem_univ (0 : ℝ)) uniqueDiffOn_univ (by fun_prop)
    (hf.of_le (by exact_mod_cast hn)).contDiffWithinAt
  simp only [iteratedDerivWithin_univ, iteratedDeriv_pow] at h
  convert h using 1

noncomputable def polynomialCurve (v u : ℂ) (d : ℕ) (s : ℝ) : ℂ :=
  s • v + s ^ d • u

theorem polynomialCurve_contDiff (v u : ℂ) (d : ℕ) :
    ContDiff ℝ n (polynomialCurve v u d) := by
  unfold polynomialCurve
  fun_prop

theorem polynomialCurve_derivatives (v u : ℂ) :
    (polynomialCurve v u 2 0 = 0 ∧
      deriv (polynomialCurve v u 2) 0 = v ∧
      iteratedDeriv 2 (polynomialCurve v u 2) 0 = 2 • u ∧
      iteratedDeriv 3 (polynomialCurve v u 2) 0 = 0) ∧
    (polynomialCurve v u 3 0 = 0 ∧
      deriv (polynomialCurve v u 3) 0 = v ∧
      iteratedDeriv 2 (polynomialCurve v u 3) 0 = 0 ∧
      iteratedDeriv 3 (polynomialCurve v u 3) 0 = 6 • u) := by
  have he (d n : ℕ) : iteratedDeriv n (polynomialCurve v u d) 0 =
      iteratedDeriv n (fun s : ℝ => s) 0 • v +
        iteratedDeriv n (fun s : ℝ => s ^ d) 0 • u := by
    unfold polynomialCurve
    rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_smul_const (by fun_prop)]
  simp only [← iteratedDeriv_one]
  simp [he, iteratedDeriv_fun_id, iteratedDeriv_pow, polynomialCurve, Nat.descFactorial]

/-- The differentiated equation for an identity plus a homogeneous Jacobian. -/
theorem curve_identity_derivatives (f X : ℝ → ℂ) (L : ℂ →L[ℝ] ℂ)
    (hf : ContDiffAt ℝ 5 f 0) (d n : ℕ) (hn : n ≤ 5)
    (he : (fun s : ℝ => f s + s ^ d • L (f s)) =ᶠ[nhds 0] X) :
    iteratedDeriv n f 0 +
      (∑ i ∈ Finset.range (n + 1), n.choose i •
        ((d.descFactorial i : ℝ) * (0 : ℝ) ^ (d - i)) •
          L (iteratedDeriv (n-i) f 0)) = iteratedDeriv n X 0 := by
  have hL : ContDiffAt ℝ 5 (fun s => L (f s)) 0 := L.contDiff.contDiffAt.comp 0 hf
  have he' := he.iteratedDeriv_eq n
  have hadd := iteratedDeriv_fun_add (n := n) (f := f)
    (g := fun s : ℝ => s ^ d • L (f s))
    (hf.of_le (by exact_mod_cast hn)) (by
      have hp : ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => s ^ d) 0 := by fun_prop
      convert hp.smul (hL.of_le (by exact_mod_cast hn)) using 1)
  rw [hadd,
    iteratedDeriv_monomial_mul _ hL d n hn] at he'
  have hh (i : ℕ) := iteratedDeriv_linear_comp L f hf (n - i) (by omega)
  simp_rw [hh] at he'
  exact he'

theorem quadratic_ray (q : Quadratic) (v : ℂ) (s : ℝ) :
    q.eval (s • v) = s ^ 2 • q.eval v := by
  simp [Quadratic.eval, Complex.real_smul, map_mul]
  ring

theorem cubic_ray (p : Cubic) (v : ℂ) (s : ℝ) :
    p.eval (s • v) = s ^ 3 • p.eval v := by
  simp [Cubic.eval, Complex.real_smul, map_mul]
  ring

theorem quadratic_directional_ray (q : Quadratic) (v y : ℂ) (s : ℝ) :
    q.directional (s • v) y = s • q.directional v y := by
  simp [Quadratic.directional, Complex.real_smul, map_mul]
  ring

theorem cubic_directional_ray (p : Cubic) (v y : ℂ) (s : ℝ) :
    p.directional (s • v) y = s ^ 2 • p.directional v y := by
  simp [Cubic.directional, Complex.real_smul, map_mul]
  ring

/-- Actual Jacobian cancellation on a neighborhood, before taking derivatives. -/
theorem pullback_equation_eventually (F H : ℂ → ℂ)
    (hH : ContDiffAt ℝ ⊤ H 0) (_h0 : H 0 = 0)
    (hd : fderiv ℝ H 0 = ContinuousLinearMap.id ℝ ℂ) :
    ∀ᶠ z in nhds 0, fderiv ℝ H z (nonlinearPullback F H z) = F (H z) := by
  have hi : (fderiv ℝ H 0).IsInvertible := by
    rw [hd]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, rfl⟩
  have hj : ContinuousAt (fun z => fderiv ℝ H z) 0 :=
    (hH.fderiv_right (by exact le_top : (1 : WithTop ℕ∞) + 1 ≤ ⊤)).continuousAt
  filter_upwards [hj.tendsto.eventually hi.eventually_nhds] with z hz
  exact hz.self_apply_inverse _

/-- The quadratic coordinate's exact equation restricted to a real ray. -/
theorem quadratic_pullback_curve_equation (F : ℂ → ℂ) (h : Quadratic) (v : ℂ) :
    let G := fun s : ℝ => nonlinearPullback F (fun z => z + h.eval z) (s • v)
    (fun s : ℝ => G s + s • (fderiv ℝ h.eval v) (G s)) =ᶠ[nhds 0]
      (fun s => F (polynomialCurve v (h.eval v) 2 s)) := by
  have he := pullback_equation_eventually F (fun z => z + h.eval z)
    (contDiff_id.add (quadratic_contDiff h)).contDiffAt
    (by simp [Quadratic.eval]) (by ext y; simp [quadratic_change_fderiv_apply, Quadratic.directional])
  have hv : ContinuousAt (fun s : ℝ => s • v) 0 := by fun_prop
  have he' := hv.tendsto.eventually (by simpa using he)
  filter_upwards [he'] with s hs
  simpa only [quadratic_change_fderiv_apply, quadratic_fderiv,
    quadratic_directional_ray, quadratic_ray, polynomialCurve] using hs

theorem cubic_pullback_curve_equation (F : ℂ → ℂ) (t : Cubic) (v : ℂ) :
    let G := fun s : ℝ => nonlinearPullback F (fun z => z + t.eval z) (s • v)
    (fun s : ℝ => G s + s ^ 2 • (fderiv ℝ t.eval v) (G s)) =ᶠ[nhds 0]
      (fun s => F (polynomialCurve v (t.eval v) 3 s)) := by
  have he := pullback_equation_eventually F (fun z => z + t.eval z)
    (contDiff_id.add (cubic_contDiff t)).contDiffAt
    (by simp [Cubic.eval]) (by ext y; simp [cubic_change_fderiv_apply, Cubic.directional])
  have hv : ContinuousAt (fun s : ℝ => s • v) 0 := by fun_prop
  have he' := hv.tendsto.eventually (by simpa using he)
  filter_upwards [he'] with s hs
  simpa only [cubic_change_fderiv_apply, cubic_fderiv,
    cubic_directional_ray, cubic_ray, polynomialCurve] using hs

/-- Recover the mixed bilinear coefficient from its diagonal quadratic. -/
theorem quadratic_directional_of_diagonal (F : ℂ → ℂ) (q : Quadratic)
    (hF : ContDiffAt ℝ 5 F 0)
    (hq : ∀ z, q.eval z = iteratedFDeriv ℝ 2 F 0 (fun _ => z) / 2) (v u : ℂ) :
    q.directional v u = iteratedFDeriv ℝ 2 F 0 ![v, u] := by
  let B := iteratedFDeriv ℝ 2 F 0
  have hs : B ![u, v] = B ![v, u] :=
    (hF.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons
  have he : B (fun _ => v + u) = B (fun _ => v) + B ![v, u] + B ![u, v] + B (fun _ => u) := by
    have hvv : (fun _ : Fin 2 => v) = ![v,v] := by ext i; fin_cases i <;> rfl
    have huu : (fun _ : Fin 2 => u) = ![u,u] := by ext i; fin_cases i <;> rfl
    have hvu : (fun _ : Fin 2 => v + u) = ![v+u,v+u] := by ext i; fin_cases i <;> rfl
    rw [hvv, huu, hvu]
    simp only [Matrix.vecCons, ← ContinuousMultilinearMap.curryLeft_apply, map_add, add_apply]
    abel
  have ha := quadratic_eval_add q v u
  rw [hq (v+u), hq v, hq u] at ha
  change B (fun _ => v+u) / 2 = B (fun _ => v) / 2 + q.directional v u + B (fun _ => u) / 2 at ha
  rw [he, hs] at ha
  linear_combination -ha

/-- Diagonal chain rules at the origin for the actual quadratic substitution. -/
theorem quadratic_composed_curve_jets (F : ℂ → ℂ) (hF : ContDiffAt ℝ 5 F 0)
    (h : Quadratic) (q : Quadratic)
    (hq : ∀ z, q.eval z = iteratedFDeriv ℝ 2 F 0 (fun _ => z) / 2) (v : ℂ) :
    let X := F ∘ polynomialCurve v (h.eval v) 2
    deriv X 0 = fderiv ℝ F 0 v ∧
    iteratedDeriv 2 X 0 = iteratedFDeriv ℝ 2 F 0 (fun _ => v) +
      2 • fderiv ℝ F 0 (h.eval v) ∧
    iteratedDeriv 3 X 0 = iteratedFDeriv ℝ 3 F 0 (fun _ => v) +
      6 • q.directional v (h.eval v) := by
  obtain ⟨⟨hc0, hc1, hc2, hc3⟩, _⟩ := polynomialCurve_derivatives v (h.eval v)
  have hc : ContDiffAt ℝ 5 (polynomialCurve v (h.eval v) 2) 0 :=
    (polynomialCurve_contDiff _ _ _).contDiffAt
  have hF' : ContDiffAt ℝ 5 F (polynomialCurve v (h.eval v) 2 0) := by simpa [hc0] using hF
  have h1 := hF'.differentiableAt (by norm_num) |>.hasFDerivAt |>.comp_hasDerivAt 0
    (hc.differentiableAt (by norm_num)).hasDerivAt
  have h2 := iteratedDeriv_vcomp_two (hF'.of_le (by norm_num)) (hc.of_le (by norm_num))
  have h3 := iteratedDeriv_vcomp_three (hF'.of_le (by norm_num)) (hc.of_le (by norm_num))
  have hs : iteratedFDeriv ℝ 2 F 0 ![h.eval v, v] =
      iteratedFDeriv ℝ 2 F 0 ![v, h.eval v] :=
    (hF.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons
  have hb (r : ℕ) (u w : ℂ) :
      iteratedFDeriv ℝ 2 F 0 ![r • u, w] = r • iteratedFDeriv ℝ 2 F 0 ![u,w] := by
    simp only [Matrix.vecCons, ← ContinuousMultilinearMap.curryLeft_apply, map_nsmul, smul_apply]
  have hb' (r : ℕ) (u w : ℂ) :
      iteratedFDeriv ℝ 2 F 0 ![u, r • w] = r • iteratedFDeriv ℝ 2 F 0 ![u,w] := by
    simp only [Matrix.vecCons, ← ContinuousMultilinearMap.curryLeft_apply, map_nsmul, smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_def, hc0, hc1] using h1.deriv
  · simpa only [hc0, hc1, hc2, map_nsmul] using h2
  · rw [hc0, hc1, hc2, hc3, hb, hb', hs, map_zero, add_zero,
      ← quadratic_directional_of_diagonal F q hF hq v (h.eval v)] at h3
    convert h3 using 1 <;> simp only [Complex.real_smul, nsmul_eq_mul] <;> ring

theorem quadraticPullbackJets : QuadraticPullbackJets := by
  intro F a b q p hF hb hj
  rcases hj with ⟨hF0, hlin, hq, hp⟩
  let h := quadraticChange a b q
  let g := cubicAfterQuadratic q p h
  let P := nonlinearPullback F (fun z => z + h.eval z)
  have hP : ContDiffAt ℝ 5 P 0 := (actualPullbackRegularity F hF).1 h
  have hP0 : P 0 = 0 := by
    have hd : fderiv ℝ (fun z => z + h.eval z) 0 = ContinuousLinearMap.id ℝ ℂ := by
      ext v; simp [quadratic_change_fderiv_apply, Quadratic.directional]
    simp [P, nonlinearPullback, Quadratic.eval, hd, hF0]
  have hjet (v : ℂ) :
      fderiv ℝ P 0 v = eigenvalue a b * v ∧
      iteratedFDeriv ℝ 2 P 0 (fun _ => v) = 0 ∧
      iteratedFDeriv ℝ 3 P 0 (fun _ => v) = 6 * g.eval v := by
    let G := fun s : ℝ => P (s • v)
    let X := F ∘ polynomialCurve v (h.eval v) 2
    let L := fderiv ℝ h.eval v
    have hG : ContDiffAt ℝ 5 G 0 := by
      have hv : ContDiffAt ℝ 5 (fun s : ℝ => s • v) 0 := by fun_prop
      have hP' : ContDiffAt ℝ 5 P ((0 : ℝ) • v) := by simpa using hP
      exact hP'.comp 0 hv
    have hG0 : G 0 = 0 := by simpa [G] using hP0
    have heq : (fun s : ℝ => G s + s ^ 1 • L (G s)) =ᶠ[nhds 0] X := by
      simpa only [pow_one, X, Function.comp_def] using quadratic_pullback_curve_equation F h v
    have he1 := curve_identity_derivatives G X L hG 1 1 (by norm_num) heq
    have he2 := curve_identity_derivatives G X L hG 1 2 (by norm_num) heq
    have he3 := curve_identity_derivatives G X L hG 1 3 (by norm_num) heq
    simp [Finset.sum_range_succ, Nat.descFactorial, hG0] at he1 he2 he3
    obtain ⟨hX1, hX2, hX3⟩ := quadratic_composed_curve_jets F hF h q hq v
    have hG1 : deriv G 0 = eigenvalue a b * v := by
      simpa only [X, hX1, hlin] using he1
    have hhom := quadratic_change_solves a b q hb v
    have hG2 : iteratedDeriv 2 G 0 = 0 := by
      change h.directional v (eigenvalue a b * v) - eigenvalue a b * h.eval v = q.eval v at hhom
      rw [hG1] at he2
      dsimp only [L] at he2
      rw [quadratic_fderiv] at he2
      rw [show iteratedDeriv 2 X 0 = _ from hX2, hlin] at he2
      have hq' := hq v
      simp only [nsmul_eq_mul] at he2
      linear_combination he2 - 2 * hhom - 2 * hq'
    have hG3 : iteratedDeriv 3 G 0 = 6 * g.eval v := by
      rw [hG2, map_zero, mul_zero, add_zero] at he3
      rw [show iteratedDeriv 3 X 0 = _ from hX3] at he3
      have hp' := hp v
      have hg := cubic_after_quadratic_eval q p h v
      change g.eval v = _ at hg
      simp only [nsmul_eq_mul] at he3
      linear_combination he3 - 6 * hp' - 6 * hg
    have hr1 := iteratedDeriv_ray P hP v 1 (by norm_num)
    have hr2 := iteratedDeriv_ray P hP v 2 (by norm_num)
    have hr3 := iteratedDeriv_ray P hP v 3 (by norm_num)
    simp only [iteratedDeriv_one, iteratedFDeriv_one_apply] at hr1
    exact ⟨hr1 ▸ hG1, hr2 ▸ hG2, hr3 ▸ hG3⟩
  refine ⟨hP0, fun v => (hjet v).1, ?_, ?_⟩
  · intro v
    change zeroQuadratic.eval v = iteratedFDeriv ℝ 2 P 0 (fun _ => v) / 2
    simp [zeroQuadratic, Quadratic.eval, (hjet v).2.1]
  · intro v
    change g.eval v = iteratedFDeriv ℝ 3 P 0 (fun _ => v) / 6
    rw [(hjet v).2.2]
    ring

theorem cubic_composed_curve_jets (F : ℂ → ℂ) (hF : ContDiffAt ℝ 5 F 0)
    (t : Cubic) (v : ℂ) :
    let X := F ∘ polynomialCurve v (t.eval v) 3
    deriv X 0 = fderiv ℝ F 0 v ∧
    iteratedDeriv 2 X 0 = iteratedFDeriv ℝ 2 F 0 (fun _ => v) ∧
    iteratedDeriv 3 X 0 = iteratedFDeriv ℝ 3 F 0 (fun _ => v) +
      6 • fderiv ℝ F 0 (t.eval v) := by
  obtain ⟨_, ⟨hc0, hc1, hc2, hc3⟩⟩ := polynomialCurve_derivatives v (t.eval v)
  have hc : ContDiffAt ℝ 5 (polynomialCurve v (t.eval v) 3) 0 :=
    (polynomialCurve_contDiff _ _ _).contDiffAt
  have hF' : ContDiffAt ℝ 5 F (polynomialCurve v (t.eval v) 3 0) := by simpa [hc0] using hF
  have h1 := hF'.differentiableAt (by norm_num) |>.hasFDerivAt |>.comp_hasDerivAt 0
    (hc.differentiableAt (by norm_num)).hasDerivAt
  have h2 := iteratedDeriv_vcomp_two (hF'.of_le (by norm_num)) (hc.of_le (by norm_num))
  have h3 := iteratedDeriv_vcomp_three (hF'.of_le (by norm_num)) (hc.of_le (by norm_num))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hc0, hc1] using h1.deriv
  · simpa only [hc0, hc1, hc2, map_zero, add_zero] using h2
  · simpa only [hc0, hc1, hc2, hc3, Matrix.vecCons,
      ← ContinuousMultilinearMap.curryLeft_apply, map_zero, map_nsmul, zero_apply,
      smul_apply, smul_zero, add_zero] using h3

theorem cubicPullbackJets : CubicPullbackJets := by
  intro F a b g hF hb hj
  rcases hj with ⟨hF0, hlin, hq, hp⟩
  let t := cubicChange a b g
  let P := nonlinearPullback F (fun z => z + t.eval z)
  have hP : ContDiffAt ℝ 5 P 0 := (actualPullbackRegularity F hF).2 t
  have hP0 : P 0 = 0 := by
    simp [P, nonlinearPullback, Cubic.eval, hF0]
  have hjet (v : ℂ) :
      fderiv ℝ P 0 v = eigenvalue a b * v ∧
      iteratedFDeriv ℝ 2 P 0 (fun _ => v) = 0 ∧
      iteratedFDeriv ℝ 3 P 0 (fun _ => v) = 6 * (g.c21 * v ^ 2 * conj v) := by
    let G := fun s : ℝ => P (s • v)
    let X := F ∘ polynomialCurve v (t.eval v) 3
    let L := fderiv ℝ t.eval v
    have hG : ContDiffAt ℝ 5 G 0 := by
      have hv : ContDiffAt ℝ 5 (fun s : ℝ => s • v) 0 := by fun_prop
      have hP' : ContDiffAt ℝ 5 P ((0 : ℝ) • v) := by simpa using hP
      exact hP'.comp 0 hv
    have hG0 : G 0 = 0 := by simpa [G] using hP0
    have heq : (fun s : ℝ => G s + s ^ 2 • L (G s)) =ᶠ[nhds 0] X :=
      cubic_pullback_curve_equation F t v
    have he1 := curve_identity_derivatives G X L hG 2 1 (by norm_num) heq
    have he2 := curve_identity_derivatives G X L hG 2 2 (by norm_num) heq
    have he3 := curve_identity_derivatives G X L hG 2 3 (by norm_num) heq
    simp [Finset.sum_range_succ, Nat.descFactorial, hG0] at he1 he2 he3
    obtain ⟨hX1, hX2, hX3⟩ := cubic_composed_curve_jets F hF t v
    have hG1 : deriv G 0 = eigenvalue a b * v := by
      simpa only [X, hX1, hlin] using he1
    have hG2 : iteratedDeriv 2 G 0 = 0 := by
      rw [show iteratedDeriv 2 X 0 = _ from hX2] at he2
      have hq' := hq v
      simp only [zeroQuadratic, Quadratic.eval, zero_mul, add_zero] at hq'
      linear_combination he2 - 2 * hq'
    have hG3 : iteratedDeriv 3 G 0 = 6 * (g.c21 * v ^ 2 * conj v) := by
      rw [hG1] at he3
      dsimp only [L] at he3
      rw [cubic_fderiv, show iteratedDeriv 3 X 0 = _ from hX3, hlin] at he3
      have hp' := hp v
      have hhom := cubic_change_solves a b g hb v
      change t.directional v (eigenvalue a b * v) - eigenvalue a b * t.eval v =
        g.eval v - g.c21 * v ^ 2 * conj v at hhom
      simp only [nsmul_eq_mul] at he3
      linear_combination he3 - 6 * hp' - 6 * hhom
    have hr1 := iteratedDeriv_ray P hP v 1 (by norm_num)
    have hr2 := iteratedDeriv_ray P hP v 2 (by norm_num)
    have hr3 := iteratedDeriv_ray P hP v 3 (by norm_num)
    simp only [iteratedDeriv_one, iteratedFDeriv_one_apply] at hr1
    exact ⟨hr1 ▸ hG1, hr2 ▸ hG2, hr3 ▸ hG3⟩
  refine ⟨hP0, fun v => (hjet v).1, ?_, ?_⟩
  · intro v
    change zeroQuadratic.eval v = iteratedFDeriv ℝ 2 P 0 (fun _ => v) / 2
    simp [zeroQuadratic, Quadratic.eval, (hjet v).2.1]
  · intro v
    change (resonantCubic g.c21).eval v = iteratedFDeriv ℝ 3 P 0 (fun _ => v) / 6
    rw [(hjet v).2.2]
    simp [resonantCubic, Cubic.eval]

theorem linearNormalizedFamily_contDiffAt (F : ℝ × ℂ → ℂ)
    (S T : ℝ → ℂ →L[ℝ] ℂ) (μ : ℝ) (hF : ContDiffAt ℝ 5 F (μ, 0)) :
    ContDiffAt ℝ 5 (fun z => linearNormalizedFamily F S T (μ, z)) 0 := by
  have hinner : ContDiffAt ℝ 5 (fun z : ℂ => (μ, S μ z)) 0 :=
    contDiffAt_const.prodMk (S μ).contDiff.contDiffAt
  have hF' : ContDiffAt ℝ 5 F (μ, S μ 0) := by simpa using hF
  exact (T μ).contDiff.contDiffAt.comp 0 (hF'.comp 0 hinner)

theorem sourceFiniteElimination : SourceFiniteElimination := by
  intro F ω hF hω heig heq
  dsimp only
  let a := spectralReal F
  let b := spectralImag F
  let S := sourceForwardCLM F
  let T := sourceInverseCLM F
  let q := familyQuadratic F S T
  let p := familyCubic F S T
  let h := fun μ => quadraticChange (a μ) (b μ) (q μ)
  let g := fun μ => cubicAfterQuadratic (q μ) (p μ) (h μ)
  let t := fun μ => cubicChange (a μ) (b μ) (g μ)
  let N := fun μ z => linearNormalizedFamily F S T (μ, z)
  let G := fun μ => nonlinearPullback (N μ) (fun z => z + (h μ).eval z)
  let K := fun μ => nonlinearPullback (G μ) (fun z => z + (t μ).eval z)
  obtain ⟨ha0, hb0, ε₁, hε₁, hspec⟩ := spectralFamilyCoordinates F ω hF hω heig
  obtain ⟨ε₂, hε₂, hdata⟩ := sourceTaylorData F ω hF hω heig
  obtain ⟨ε₃, hε₃, hhom⟩ := sourceHomologicalData F ω hF hω heig
  obtain ⟨ε₄, hε₄, hlin⟩ := sourceNormalizedLinearJet F ω hF hω heig heq
  refine ⟨ha0, hb0, min (min ε₁ ε₂) (min ε₃ ε₄),
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), ?_⟩
  intro μ hμ
  have hm1 : |μ| < ε₁ := lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hm2 : |μ| < ε₂ := lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hm3 : |μ| < ε₃ := lt_of_lt_of_le hμ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm4 : |μ| < ε₄ := lt_of_lt_of_le hμ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hb, ha, hbreg, _⟩ := hspec μ hm1
  obtain ⟨hFμ, _, hS, hT, hqreg, hpreg, hqjet, hpjet, hTS, hST, hA⟩ := hdata μ hm2
  obtain ⟨_, hh, hg, ht, hc, hhi, hti, hd2, hd3⟩ := hhom μ hm3
  obtain ⟨hN0, hNlin⟩ := hlin μ hm4
  have hN : ContDiffAt ℝ 5 (N μ) 0 := linearNormalizedFamily_contDiffAt F S T μ hFμ
  have hG : ContDiffAt ℝ 5 (G μ) 0 := (actualPullbackRegularity (N μ) hN).1 (h μ)
  have hK : ContDiffAt ℝ 5 (K μ) 0 := (actualPullbackRegularity (G μ) hG).2 (t μ)
  have hjN : SpatialCubicJet (N μ) (eigenvalue (a μ) (b μ)) (q μ) (p μ) :=
    ⟨hN0, hNlin, hqjet, hpjet⟩
  have hjG : SpatialCubicJet (G μ) (eigenvalue (a μ) (b μ)) zeroQuadratic (g μ) :=
    quadraticPullbackJets (N μ) (a μ) (b μ) (q μ) (p μ) hN hb hjN
  have hjK : SpatialCubicJet (K μ) (eigenvalue (a μ) (b μ)) zeroQuadratic (resonantCubic (g μ).c21) :=
    cubicPullbackJets (G μ) (a μ) (b μ) (g μ) hG hb hjG
  exact ⟨hb, ha, hbreg, hS, hT, hTS, hST, hA, hqreg, hpreg, hh, hg, ht, hc,
    hhi, hti, hd2, hd3, hN, hG, hK, hjN, hjG, hjK⟩

end D13Unified.Ch16.CubicHomologicalElimination
