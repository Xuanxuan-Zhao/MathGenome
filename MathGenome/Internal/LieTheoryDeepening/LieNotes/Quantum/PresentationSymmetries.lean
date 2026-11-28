import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Presentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.PresentationSymmetries

noncomputable section

namespace LieNotes.Quantum.PresentationSymmetries

open Presentation MulOpposite
open Specs.LieNotes.Quantum.Presentation
  (liftBasic_cartan liftBasic_E liftBasic_F polynomialKappa exponentialUnit)
open LieNotes.Quantum.Truncations (A expH cartanTruncate)
open Specs.LieNotes.Quantum.PresentationSymmetries (InvertsCartan SymmetryLaws HasSymmetries)
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)

universe u v w

section Relations

variable {A : Type u} {T : Type v} {B : Type w}
  [CommRing A] [CommRing T] [Algebra A T] [Ring B] [Algebra A B]
variable {C : Cartan A T} {t : T →ₐ[A] B} {e f : Root → B}

private theorem kappa_tau_symm (h : InvertsCartan C) (i : Root) (x : T) :
    C.kappa ((C.tau i).symm x) = C.tau i (C.kappa x) := by
  apply (C.tau i).symm.injective
  rw [← h.tau, AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]

private theorem kappa_mixed (h : InvertsCartan C) (i j : Root) :
    C.kappa (mixed C i j) = -mixed C j i := by
  by_cases hij : i = j
  · subst j
    simpa [Specs.LieNotes.Quantum.Presentation.mixed] using h.D i
  · simp [Specs.LieNotes.Quantum.Presentation.mixed, hij, Ne.symm hij]

private theorem omegaBasic (h : InvertsCartan C) (hb : SatisfiesBasic C t e f) :
    SatisfiesBasic C (t.comp C.kappa.toAlgHom) f e where
  cartanF x j := by
    change t (C.kappa x) * e j = e j * t (C.kappa ((C.tau j).symm x))
    rw [kappa_tau_symm h]
    simpa only [AlgEquiv.symm_apply_apply] using (hb.eCartan j (C.tau j (C.kappa x))).symm
  eCartan i x := by
    change f i * t (C.kappa x) = t (C.kappa ((C.tau i).symm x)) * f i
    rw [kappa_tau_symm h]
    simpa only [AlgEquiv.symm_apply_apply] using (hb.cartanF (C.tau i (C.kappa x)) i).symm
  comm i j := by
    change f i * e j - e j * f i = t (C.kappa (mixed C i j))
    rw [kappa_mixed h, map_neg, ← hb.comm j i, neg_sub]

private def oppositeCartan (t : T →ₐ[A] B) : T →ₐ[A] Bᵐᵒᵖ :=
  t.toOpposite fun x y => (Commute.all x y).map t

private theorem etaBasic (hb : SatisfiesBasic C t e f) :
    SatisfiesBasic C (oppositeCartan t) (fun i => op (f i)) (fun i => op (e i)) where
  cartanF x j := unop_injective (hb.eCartan j x)
  eCartan i x := unop_injective (hb.cartanF x i)
  comm i j := by
    apply unop_injective
    change e j * f i - f i * e j = t (mixed C i j)
    rw [hb.comm j i]
    by_cases hij : i = j
    · subst j
      rfl
    · simp [Specs.LieNotes.Quantum.Presentation.mixed, hij, Ne.symm hij]

private theorem unop_serre (q : Aˣ) (x y : Bᵐᵒᵖ) :
    unop (serrePolynomial q x y) = serrePolynomial q (unop x) (unop y) := by
  simp only [serrePolynomial, unop_add, unop_neg, unop_smul, unop_mul, unop_pow, mul_assoc,
    sub_eq_add_neg]
  ac_rfl

private theorem etaSerre (hs : SatisfiesSerre C.q e f) :
    SatisfiesSerre C.q (fun i => op (f i)) (fun i => op (e i)) where
  pos i j hij := unop_injective (by rw [unop_serre]; exact hs.neg i j hij)
  neg i j hij := unop_injective (by rw [unop_serre]; exact hs.pos i j hij)

end Relations

section Symmetries

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
variable {C : Cartan A T} (h : InvertsCartan C)

/-- The Cartan-inverting swap of the simple-root generators before imposing Serre relations. -/
def omega₀ : B₀ C →ₐ[A] B₀ C :=
  liftBasic C ((cartan₀ C).comp C.kappa.toAlgHom) (F₀ C) (E₀ C)
    (omegaBasic h (basic_relations C))

/-- The product-reversing swap of the simple-root generators before imposing Serre relations. -/
def eta₀ (C : Cartan A T) : B₀ C →ₐ[A] (B₀ C)ᵐᵒᵖ :=
  liftBasic C (oppositeCartan (cartan₀ C)) (fun i => op (F₀ C i)) (fun i => op (E₀ C i))
    (etaBasic (basic_relations C))

/-- The Cartan-inverting swap on the Serre quotient. -/
def omega : U C →ₐ[A] U C :=
  liftU C ((cartan C).comp C.kappa.toAlgHom) (F C) (E C)
    (omegaBasic h (relations C)) ⟨(serre_relations C).neg, (serre_relations C).pos⟩

/-- The product-reversing swap on the Serre quotient. -/
def eta (C : Cartan A T) : U C →ₐ[A] (U C)ᵐᵒᵖ :=
  liftU C (oppositeCartan (cartan C)) (fun i => op (F C i)) (fun i => op (E C i))
    (etaBasic (relations C)) (etaSerre (serre_relations C))

@[simp] theorem omega₀_cartan (x : T) : omega₀ h (cartan₀ C x) = cartan₀ C (C.kappa x) := by
  simp [omega₀]

@[simp] theorem omega₀_E (i : Root) : omega₀ h (E₀ C i) = F₀ C i := by
  simp [omega₀]

@[simp] theorem omega₀_F (i : Root) : omega₀ h (F₀ C i) = E₀ C i := by
  simp [omega₀]

@[simp] theorem eta₀_cartan (x : T) : eta₀ C (cartan₀ C x) = op (cartan₀ C x) := by
  simp [eta₀, oppositeCartan]

@[simp] theorem eta₀_E (i : Root) : eta₀ C (E₀ C i) = op (F₀ C i) := by
  simp [eta₀]

@[simp] theorem eta₀_F (i : Root) : eta₀ C (F₀ C i) = op (E₀ C i) := by
  simp [eta₀]

@[simp] theorem omega_cartan (x : T) : omega h (cartan C x) = cartan C (C.kappa x) := by
  simp [omega]

@[simp] theorem omega_E (i : Root) : omega h (E C i) = F C i := by
  simp [omega]

@[simp] theorem omega_F (i : Root) : omega h (F C i) = E C i := by
  simp [omega]

@[simp] theorem eta_cartan (x : T) : eta C (cartan C x) = op (cartan C x) := by
  simp [eta, oppositeCartan]

@[simp] theorem eta_E (i : Root) : eta C (E C i) = op (F C i) := by
  simp [eta]

@[simp] theorem eta_F (i : Root) : eta C (F C i) = op (E C i) := by
  simp [eta]

theorem omega₀_involutive : Function.Involutive (omega₀ h) := by
  have he : (omega₀ h).comp (omega₀ h) = AlgHom.id A (B₀ C) := by
    apply basic_hom_ext C
    · intro x
      simp [h.involutive x]
    · intro i
      simp
    · intro i
      simp
  exact DFunLike.congr_fun he

theorem eta₀_involutive (C : Cartan A T) :
    Function.Involutive (fun b => unop (eta₀ C b)) := by
  let square := (AlgEquiv.opOp A (B₀ C)).symm.toAlgHom.comp
    ((AlgHom.op (eta₀ C)).comp (eta₀ C))
  have he : square = AlgHom.id A (B₀ C) := by
    apply basic_hom_ext C
    · intro x
      change unop (eta₀ C (unop (eta₀ C (cartan₀ C x)))) = cartan₀ C x
      simp
    · intro i
      change unop (eta₀ C (unop (eta₀ C (E₀ C i)))) = E₀ C i
      simp
    · intro i
      change unop (eta₀ C (unop (eta₀ C (F₀ C i)))) = F₀ C i
      simp
  exact DFunLike.congr_fun he

theorem omega_involutive : Function.Involutive (omega h) := by
  have he : (omega h).comp (omega h) = AlgHom.id A (U C) := by
    apply hom_ext C
    · intro x
      simp [h.involutive x]
    · intro i
      simp
    · intro i
      simp
  exact DFunLike.congr_fun he

theorem eta_involutive (C : Cartan A T) :
    Function.Involutive (fun b => unop (eta C b)) := by
  let square := (AlgEquiv.opOp A (U C)).symm.toAlgHom.comp
    ((AlgHom.op (eta C)).comp (eta C))
  have he : square = AlgHom.id A (U C) := by
    apply hom_ext C
    · intro x
      change unop (eta C (unop (eta C (cartan C x)))) = cartan C x
      simp
    · intro i
      change unop (eta C (unop (eta C (E C i)))) = E C i
      simp
    · intro i
      change unop (eta C (unop (eta C (F C i)))) = F C i
      simp
  exact DFunLike.congr_fun he

theorem omega_descends (b : B₀ C) :
    serreQuotient C (omega₀ h b) = omega h (serreQuotient C b) := by
  have he : (serreQuotient C).comp (omega₀ h) = (omega h).comp (serreQuotient C) := by
    apply basic_hom_ext C
    · intro x
      simp only [AlgHom.comp_apply, omega₀_cartan]
      exact (omega_cartan h x).symm
    · intro i
      simp only [AlgHom.comp_apply, omega₀_E]
      exact (omega_E h i).symm
    · intro i
      simp only [AlgHom.comp_apply, omega₀_F]
      exact (omega_F h i).symm
  exact DFunLike.congr_fun he b

theorem eta_descends (b : B₀ C) :
    op (serreQuotient C (unop (eta₀ C b))) = eta C (serreQuotient C b) := by
  have he : (serreQuotient C).op.comp (eta₀ C) = (eta C).comp (serreQuotient C) := by
    apply basic_hom_ext C
    · intro x
      change op (serreQuotient C (unop (eta₀ C (cartan₀ C x)))) = eta C (cartan C x)
      rw [eta₀_cartan, unop_op, eta_cartan]
      rfl
    · intro i
      change op (serreQuotient C (unop (eta₀ C (E₀ C i)))) = eta C (E C i)
      rw [eta₀_E, unop_op, eta_E]
      rfl
    · intro i
      change op (serreQuotient C (unop (eta₀ C (F₀ C i)))) = eta C (F C i)
      rw [eta₀_F, unop_op, eta_F]
      rfl
  exact DFunLike.congr_fun he b

private theorem quotient_eq_zero (b : B₀ C) :
    serreQuotient C b = 0 ↔ b ∈ serreIdeal C :=
  Ideal.Quotient.eq_zero_iff_mem.trans TwoSidedIdeal.mem_asIdeal

theorem omega₀_mem_serreIdeal (b : B₀ C) :
    omega₀ h b ∈ serreIdeal C ↔ b ∈ serreIdeal C := by
  rw [← quotient_eq_zero, ← quotient_eq_zero, omega_descends]
  exact map_eq_zero_iff _ (omega_involutive h).injective

theorem eta₀_mem_serreIdeal (b : B₀ C) :
    unop (eta₀ C b) ∈ serreIdeal C ↔ b ∈ serreIdeal C := by
  rw [← quotient_eq_zero, ← quotient_eq_zero]
  have hq := congrArg unop (eta_descends (C := C) b)
  change serreQuotient C (unop (eta₀ C b)) = unop (eta C (serreQuotient C b)) at hq
  rw [hq]
  exact ⟨fun hz => (eta_involutive C).injective (by simpa using hz), fun hz => by simp [hz]⟩

theorem hasSymmetries (h : InvertsCartan C) : HasSymmetries C :=
  ⟨h, omega₀ h, eta₀ C, omega h, eta C,
    ⟨omega₀_cartan h, omega₀_E h, omega₀_F h, omega₀_involutive h,
      eta₀_cartan, eta₀_E, eta₀_F, eta₀_involutive C⟩,
    ⟨omega_cartan h, omega_E h, omega_F h, omega_involutive h,
      eta_cartan, eta_E, eta_F, eta_involutive C⟩,
    omega₀_mem_serreIdeal h, eta₀_mem_serreIdeal, omega_descends h, eta_descends⟩

end Symmetries

section Coefficients

variable {k : Type u} [Field k] [CharZero k]

theorem generic_invertsCartan (q : kˣ) (hq : (q : k)^2 ≠ 1) :
    InvertsCartan (generic q hq) :=
  ⟨generic_kappa_involutive q hq, generic_kappa_tau q hq, generic_kappa_D q hq⟩

theorem indeterminate_invertsCartan (k : Type u) [Field k] [CharZero k] :
    InvertsCartan (indeterminate k) :=
  generic_invertsCartan (rationalQ k) (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

theorem truncated_invertsCartan (k : Type u) [Field k] [CharZero k] (N : ℕ) :
    InvertsCartan (truncated k N) :=
  ⟨truncated_kappa_involutive N, truncated_kappa_tau N, truncated_kappa_D N⟩

/-- Cartan inversion also inverts the truncated exponential used in the coproduct. -/
theorem truncated_kappa_K (N : ℕ) (i : Root) :
    (truncated k N).kappa ((truncated k N).K i : TruncatedCartan k N) =
      ↑((truncated k N).K i)⁻¹ := by
  let tr := cartanTruncate (R := k) Root N
  let H : PolynomialCartan k := MvPolynomial.X i
  have hK : ((truncated k N).K i : TruncatedCartan k N) = tr (expH H) :=
    congrArg tr (exponentialUnit_val H)
  apply ((truncated k N).K i).eq_inv_of_mul_eq_one_left
  rw [hK]
  change tr (expH H) * (polynomialKappa (A k N)).toAlgHom (tr (expH H)) = 1
  rw [cartanTruncate_map N (polynomialKappa k).toAlgHom (polynomialKappa (A k N)).toAlgHom,
    Truncations.map_expH]
  · change tr (expH H) * tr (expH (polynomialKappa k (MvPolynomial.X i))) = 1
    rw [polynomialKappa_X, ← map_mul, Truncations.expH_mul_neg, map_one]
  · intro l
    simp

theorem generic_symmetries (q : kˣ) (hq : (q : k)^2 ≠ 1) :
    HasSymmetries (generic q hq) ∧
      ∀ i, (generic q hq).kappa ((generic q hq).K i : Laurent k) = ↑((generic q hq).K i)⁻¹ :=
  ⟨hasSymmetries (generic_invertsCartan q hq), generic_kappa_K q hq⟩

theorem indeterminate_symmetries (k : Type u) [Field k] [CharZero k] :
    HasSymmetries (indeterminate k) ∧
      ∀ i, (indeterminate k).kappa ((indeterminate k).K i : Laurent (RatFunc k)) =
        ↑((indeterminate k).K i)⁻¹ :=
  generic_symmetries (rationalQ k) (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

theorem truncated_symmetries (k : Type u) [Field k] [CharZero k] (N : ℕ) (_hN : 1 ≤ N) :
    HasSymmetries (truncated k N) ∧
      ∀ i : Root, (truncated k N).kappa (MvPolynomial.X i) = -MvPolynomial.X i :=
  ⟨hasSymmetries (truncated_invertsCartan k N), truncated_kappa_H N⟩

end Coefficients

end LieNotes.Quantum.PresentationSymmetries
