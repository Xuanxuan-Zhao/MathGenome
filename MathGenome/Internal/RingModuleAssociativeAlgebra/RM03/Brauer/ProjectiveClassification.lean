import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ProjectiveClassification
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.SemilinearDescent
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.Basic

open scoped TensorProduct MatrixGroups

universe u v w

namespace RM03.Brauer.ProjectiveClassification

open SemilinearDescent Matrix

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}

private def unitConj (G : GL (Fin n) K) : Mat K n ≃ₐ[K] Mat K n where
  toFun x := (G : Mat K n) * x * (↑G⁻¹ : Mat K n)
  invFun x := (↑G⁻¹ : Mat K n) * x * (G : Mat K n)
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_mul' x y := by
    change _ = _ * (_ * y * _)
    simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' a := by
    rw [← Algebra.commutes, mul_assoc, G.mul_inv, mul_one]

private theorem unitConj_apply (G : GL (Fin n) K) (x : Mat K n) :
    unitConj G x = (G : Mat K n) * x * (↑G⁻¹ : Mat K n) := rfl

private def unitConjugation : GL (Fin n) K →* (Mat K n ≃ₐ[K] Mat K n) where
  toFun := unitConj
  map_one' := AlgEquiv.ext fun x => by simp [unitConj_apply]
  map_mul' G H := AlgEquiv.ext fun x => by
    simp [unitConj_apply, _root_.mul_inv_rev, mul_assoc]

private def conjugation : PGL(n, K) →* (Mat K n ≃ₐ[K] Mat K n) :=
  ProjGenLinGroup.lift unitConjugation <| MonoidHom.ext fun a => AlgEquiv.ext fun x => by
    change (GeneralLinearGroup.scalar (Fin n) a : Mat K n) * x *
      (↑((GeneralLinearGroup.scalar (Fin n)) a)⁻¹ : Mat K n) = x
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_comm _ (Commute.all _),
      ← GeneralLinearGroup.coe_scalar a, mul_assoc, Units.mul_inv, mul_one]

private theorem conjugation_mk (G : GL (Fin n) K) (x : Mat K n) :
    conjugation (ProjGenLinGroup.mk G) x = (G : Mat K n) * x * (↑G⁻¹ : Mat K n) := rfl

private theorem conjugation_injective :
    Function.Injective (conjugation (n := n) (K := K)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  refine le_antisymm (fun p hp => ?_) bot_le
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective p
  rw [Subgroup.mem_bot, ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
  intro H
  apply Units.ext
  have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hp) (H : Mat K n)
  rw [conjugation_mk, AlgEquiv.one_apply] at h
  simpa [mul_assoc] using (congrArg (fun x : Mat K n => x * (G : Mat K n)) h).symm

private theorem conjugation_surjective (hn : 0 < n) :
    Function.Surjective (conjugation (n := n) (K := K)) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro f
  obtain ⟨G, hG⟩ := CSA.algEquiv_isInner
    (show CSA.IsCentralSimple K (Mat K n) from ⟨inferInstance, inferInstance, inferInstance⟩) f
  exact ⟨ProjGenLinGroup.mk G, AlgEquiv.ext fun x => (conjugation_mk G x).trans (hG x).symm⟩

private def coefficient (g : Gal(K/k)) : Mat K n ≃+* Mat K n :=
  g.toRingEquiv.mapMatrix

private theorem coefficient_mul (g h : Gal(K/k)) (x : Mat K n) :
    coefficient (g * h) x = coefficient g (coefficient h x) := rfl

private theorem coefficient_one (x : Mat K n) :
    coefficient (1 : Gal(K/k)) x = x := rfl

private theorem coefficient_inv_apply (g : Gal(K/k)) (x : Mat K n) :
    coefficient g⁻¹ (coefficient g x) = x := by
  rw [← coefficient_mul, inv_mul_cancel, coefficient_one]

private theorem coefficient_apply_inv (g : Gal(K/k)) (x : Mat K n) :
    coefficient g (coefficient g⁻¹ x) = x := by
  rw [← coefficient_mul, mul_inv_cancel, coefficient_one]

private theorem coefficient_smul (g : Gal(K/k)) (a : K) (x : Mat K n) :
    coefficient g (a • x) = g a • coefficient g x := by
  ext i j
  exact map_mul g a (x i j)

private theorem coefficient_conjugation (g : Gal(K/k)) (p : PGL(n, K)) (x : Mat K n) :
    coefficient g (conjugation p x) =
      conjugation (projectiveAction k K n g p) (coefficient g x) := by
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective p
  rw [projectiveAction, ProjGenLinGroup.map_mk, conjugation_mk, conjugation_mk,
    map_mul, map_mul]
  rfl

@[simp] theorem projectiveAction_one (p : PGL(n, K)) :
    projectiveAction k K n 1 p = p :=
  DFunLike.congr_fun ProjGenLinGroup.map_id p

theorem projectiveAction_mul (g h : Gal(K/k)) (p : PGL(n, K)) :
    projectiveAction k K n (g * h) p =
      projectiveAction k K n g (projectiveAction k K n h p) :=
  DFunLike.congr_fun (ProjGenLinGroup.map_comp h.toRingHom g.toRingHom) p

private theorem Cocycle.val_one (c : Cocycle k K n) : c.val 1 = 1 := by
  have h := c.law 1 1
  rw [one_mul, projectiveAction_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one (c.val 1)).symm)

private def twist (c : Cocycle k K n) : AlgebraAction k K (Mat K n) where
  act g := (coefficient g).toAddEquiv.trans (conjugation (c.val g)).toRingEquiv.toAddEquiv
  one_act x := by
    change conjugation (c.val 1) (coefficient (1 : Gal(K/k)) x) = x
    rw [c.val_one, coefficient_one, map_one, AlgEquiv.one_apply]
  mul_act g h x := by
    change conjugation (c.val (g * h)) (coefficient (g * h) x) =
      conjugation (c.val g) (coefficient g (conjugation (c.val h) (coefficient h x)))
    rw [c.law, map_mul, AlgEquiv.mul_apply, coefficient_mul, coefficient_conjugation]
  map_smul g a x := by
    change conjugation (c.val g) (coefficient g (a • x)) =
      g a • conjugation (c.val g) (coefficient g x)
    rw [coefficient_smul, map_smul]
  map_one g := by
    change conjugation (c.val g) (coefficient g 1) = 1
    rw [map_one, map_one]
  map_mul g x y := by
    change conjugation (c.val g) (coefficient g (x * y)) =
      conjugation (c.val g) (coefficient g x) * conjugation (c.val g) (coefficient g y)
    rw [map_mul, map_mul]

private theorem twist_apply (c : Cocycle k K n) (g : Gal(K/k)) (x : Mat K n) :
    (twist c).act g x = conjugation (c.val g) (coefficient g x) := rfl

private theorem AlgebraAction.ext' {A : Type w} [Ring A] [Algebra K A]
    {ρ τ : AlgebraAction k K A} (h : ∀ g x, ρ.act g x = τ.act g x) : ρ = τ := by
  have ha : ρ.act = τ.act := funext fun g => AddEquiv.ext (h g)
  rcases ρ with ⟨⟨a, _, _, _⟩, _, _⟩
  rcases τ with ⟨⟨b, _, _, _⟩, _, _⟩
  change a = b at ha
  cases ha
  rfl

private theorem twist_implements (c : Cocycle k K n) : Implements (twist c) c := by
  intro g G hG x
  rw [twist_apply, ← hG, conjugation_mk]
  rfl

private theorem implements_iff (c : Cocycle k K n) (ρ : AlgebraAction k K (Mat K n)) :
    Implements ρ c ↔ twist c = ρ := by
  refine ⟨fun h => AlgebraAction.ext' fun g x => ?_, fun h => h ▸ twist_implements c⟩
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective (c.val g)
  exact (twist_implements c g G hG x).trans (h g G hG x).symm

private theorem twist_injective : Function.Injective (twist (k := k) (K := K) (n := n)) := by
  intro c d h
  have hw (g : Gal(K/k)) : c.val g = d.val g := by
    apply conjugation_injective
    apply AlgEquiv.ext
    intro x
    have hx := congrArg (fun ρ : AlgebraAction k K (Mat K n) =>
      ρ.act g (coefficient g⁻¹ x)) h
    simpa only [twist_apply, coefficient_apply_inv] using hx
  cases c
  cases d
  simpa only [Cocycle.mk.injEq] using funext hw

private def linearPart (ρ : AlgebraAction k K (Mat K n)) (g : Gal(K/k)) :
    Mat K n ≃ₐ[K] Mat K n where
  toRingEquiv := (coefficient g⁻¹).trans (ρ.actRingEquiv g)
  commutes' a := by
    change ρ.act g (coefficient g⁻¹ (algebraMap K (Mat K n) a)) = _
    rw [Algebra.algebraMap_eq_smul_one, coefficient_smul, map_one, ρ.map_smul, ρ.map_one,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

private theorem linearPart_apply (ρ : AlgebraAction k K (Mat K n)) (g : Gal(K/k))
    (x : Mat K n) :
    linearPart ρ g x = ρ.act g (coefficient g⁻¹ x) := rfl

private theorem twist_surjective (hn : 0 < n) :
    Function.Surjective (twist (k := k) (K := K) (n := n)) := by
  classical
  intro ρ
  have hex (g : Gal(K/k)) := conjugation_surjective hn (linearPart ρ g)
  choose p hp using hex
  have h (g : Gal(K/k)) (x : Mat K n) :
      conjugation (p g) (coefficient g x) = ρ.act g x := by
    rw [hp, linearPart_apply, coefficient_inv_apply]
  let c : Cocycle k K n := ⟨p, fun g j => by
    apply conjugation_injective
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (coefficient (g * j)).surjective x
    rw [h, ρ.mul_act, map_mul, AlgEquiv.mul_apply, coefficient_mul,
      ← coefficient_conjugation, h, h]⟩
  exact ⟨c, AlgebraAction.ext' h⟩

/-- Projective cocycles give exactly the semilinear algebra actions on matrices. -/
theorem action_correspondence (hn : 0 < n) :
    ∃ e : Cocycle k K n ≃ AlgebraAction k K (Mat K n),
      ∀ c ρ, Implements ρ c ↔ e c = ρ :=
  ⟨Equiv.ofBijective twist ⟨twist_injective, twist_surjective hn⟩, implements_iff⟩

private theorem conjugation_equivariant_iff (c d : Cocycle k K n) (p : PGL(n, K)) :
    (twist c).Equivariant (twist d) (conjugation p).toAlgHom ↔
      ∀ g, d.val g = p * c.val g * projectiveAction k K n g p⁻¹ := by
  constructor
  · intro hb g
    have he : p * c.val g = d.val g * projectiveAction k K n g p := by
      apply conjugation_injective
      apply AlgEquiv.ext
      intro x
      obtain ⟨y, rfl⟩ := (coefficient g).surjective x
      have h := hb g y
      change conjugation p ((twist c).act g y) = (twist d).act g (conjugation p y) at h
      rw [twist_apply, twist_apply, coefficient_conjugation] at h
      simpa only [map_mul, AlgEquiv.mul_apply] using h
    rw [← mul_inv_eq_iff_eq_mul] at he
    simpa only [map_inv] using he.symm
  · intro hh g x
    have he : p * c.val g = d.val g * projectiveAction k K n g p := by
      rw [hh, map_inv]
      simp [mul_assoc]
    change conjugation p ((twist c).act g x) = (twist d).act g (conjugation p x)
    rw [twist_apply, twist_apply, coefficient_conjugation, ← AlgEquiv.mul_apply,
      ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, he]

private theorem cohomologous_iff_equivariant (hn : 0 < n) (c d : Cocycle k K n) :
    Cohomologous k K n c d ↔
      ∃ b : Mat K n ≃ₐ[K] Mat K n, (twist c).Equivariant (twist d) b.toAlgHom := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨conjugation h⁻¹, (conjugation_equivariant_iff c d h⁻¹).2 (by simpa using hh)⟩
  · rintro ⟨b, hb⟩
    obtain ⟨p, rfl⟩ := conjugation_surjective hn b
    exact ⟨p⁻¹, by simpa using (conjugation_equivariant_iff c d p).1 hb⟩

section CoefficientTensor

variable {A : Type w} [Ring A] [Algebra k A]

private def coefficientTensor (g : Gal(K/k)) : (K ⊗[k] A) ≃ₐ[k] (K ⊗[k] A) :=
  Algebra.TensorProduct.congr g (AlgEquiv.refl : A ≃ₐ[k] A)

private theorem coefficientTensor_tmul (g : Gal(K/k)) (a : K) (x : A) :
    coefficientTensor g (a ⊗ₜ[k] x) = g a ⊗ₜ[k] x := rfl

private def scalarAction : AlgebraAction k K (K ⊗[k] A) where
  act g := (coefficientTensor g).toRingEquiv.toAddEquiv
  one_act x := by
    change coefficientTensor (1 : Gal(K/k)) x = x
    induction x using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  mul_act g h x := by
    change coefficientTensor (g * h) x = coefficientTensor g (coefficientTensor h x)
    induction x using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_smul g a x := by
    change coefficientTensor g (a • x) = g a • coefficientTensor g x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply]
    rfl
  map_one g := map_one (coefficientTensor g : (K ⊗[k] A) ≃ₐ[k] _)
  map_mul g := map_mul (coefficientTensor g : (K ⊗[k] A) ≃ₐ[k] _)

private def transport (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) : AlgebraAction k K (Mat K n) where
  act g := (s.symm.toRingEquiv.toAddEquiv.trans (scalarAction.act g)).trans
    s.toRingEquiv.toAddEquiv
  one_act x := by
    change s (scalarAction.act (1 : Gal(K/k)) (s.symm x)) = x
    rw [scalarAction.one_act, s.apply_symm_apply]
  mul_act g h x := by
    change s (scalarAction.act (g * h) (s.symm x)) =
      s (scalarAction.act g (s.symm (s (scalarAction.act h (s.symm x)))))
    rw [s.symm_apply_apply, scalarAction.mul_act]
  map_smul g a x := by
    change s (scalarAction.act g (s.symm (a • x))) = g a • s (scalarAction.act g (s.symm x))
    rw [map_smul, scalarAction.map_smul, map_smul]
  map_one g := by
    change s (scalarAction.act g (s.symm 1)) = 1
    rw [map_one, scalarAction.map_one, map_one]
  map_mul g x y := by
    change s (scalarAction.act g (s.symm (x * y))) =
      s (scalarAction.act g (s.symm x)) * s (scalarAction.act g (s.symm y))
    rw [map_mul, scalarAction.map_mul, map_mul]

private theorem transport_spec (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) :
    IsTransport (transport s) s := by
  intro g a x
  change s (coefficientTensor g (s.symm (s (a ⊗ₜ[k] x)))) = _
  rw [s.symm_apply_apply, coefficientTensor_tmul]

/-- Each splitting gives the projective cocycle implementing its coefficient action. -/
theorem transported_cocycle (hn : 0 < n) (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) :
    ∃ ρ : AlgebraAction k K (Mat K n), IsTransport ρ s ∧
      ∃ c : Cocycle k K n, Implements ρ c := by
  obtain ⟨c, hc⟩ := twist_surjective hn (transport s)
  exact ⟨transport s, transport_spec s, c, (implements_iff _ _).2 hc⟩

/-- Changing a splitting by conjugation with `H⁻¹` changes its projective cocycle
by the coboundary specified in RM03-C04.13. -/
theorem change_splitting (s t : (K ⊗[k] A) ≃ₐ[K] Mat K n)
    (H : GL (Fin n) K) (h : ∀ y, t y = (↑H⁻¹ : Mat K n) * s y * (H : Mat K n))
    (ρ τ : AlgebraAction k K (Mat K n)) (c d : Cocycle k K n)
    (hρ : IsTransport ρ s) (hτ : IsTransport τ t) (hc : Implements ρ c) (hd : Implements τ d) :
    ∀ g, d.val g = (ProjGenLinGroup.mk H)⁻¹ * c.val g *
      projectiveAction k K n g (ProjGenLinGroup.mk H) := by
  obtain rfl := (implements_iff c ρ).1 hc
  obtain rfl := (implements_iff d τ).1 hd
  let p := (ProjGenLinGroup.mk H)⁻¹
  have hp (y : K ⊗[k] A) : conjugation p (s y) = t y := by
    rw [show p = ProjGenLinGroup.mk H⁻¹ from (map_inv _ _).symm, conjugation_mk, inv_inv, h]
  have he : (twist c).Equivariant (twist d) (conjugation p).toAlgHom := by
    intro g x
    change conjugation p ((twist c).act g x) = (twist d).act g (conjugation p x)
    obtain ⟨y, rfl⟩ := s.surjective x
    induction y using TensorProduct.inductionOn with
    | tmul a y => rw [hρ, hp, hp, hτ]
    | add y z hy hz => simp only [map_add, hy, hz]
  simpa only [p, inv_inv] using (conjugation_equivariant_iff c d p).1 he

end CoefficientTensor

private theorem cohomologous_equivalence : Equivalence (Cohomologous k K n) := by
  constructor
  · intro c
    exact ⟨1, fun g => by simp⟩
  · rintro c d ⟨h, hd⟩
    refine ⟨h⁻¹, fun g => ?_⟩
    rw [hd]
    simp [mul_assoc]
  · rintro c d f ⟨h, hd⟩ ⟨j, hf⟩
    refine ⟨h * j, fun g => ?_⟩
    rw [hf, hd, map_mul, _root_.mul_inv_rev]
    simp only [mul_assoc]

/-- Equality of projective cohomology classes is exactly the coboundary relation. -/
theorem h1_eq_iff (c d : Cocycle k K n) :
    (Quot.mk _ c : H1 k K n) = Quot.mk _ d ↔ Cohomologous k K n c d := by
  let s : Setoid (Cocycle k K n) := ⟨Cohomologous k K n, cohomologous_equivalence⟩
  exact ⟨fun h => @Quotient.exact _ s c d h, Quot.sound⟩

/-- The form quotient identifies exactly the algebras isomorphic over the base field. -/
theorem splitClasses_eq_iff (A B : Form k K n) :
    (Quot.mk _ A : SplitClasses k K n) = Quot.mk _ B ↔ Isomorphic k K n A B := by
  let s : Setoid (Form k K n) :=
    ⟨Isomorphic k K n, fun _ => ⟨AlgEquiv.refl⟩, fun ⟨f⟩ => ⟨f.symm⟩,
      fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩
  exact ⟨fun h => @Quotient.exact _ s A B h, Quot.sound⟩

section FiniteGalois

variable [FiniteDimensional k K] [IsGalois k K]

omit [IsGalois k K] in
private theorem fixed_finite (ρ : AlgebraAction k K (Mat K n)) :
    FiniteDimensional k ρ.fixedSubalgebra := by
  have : FiniteDimensional k (Mat K n) := Module.Finite.trans K _
  exact FiniteDimensional.of_injective ρ.fixedSubalgebra.val.toLinearMap Subtype.val_injective

private theorem descentEquiv_isTransport (ρ : AlgebraAction k K (Mat K n)) :
    IsTransport ρ ρ.descentEquiv := by
  intro g a x
  rw [ρ.descentEquiv_tmul, ρ.descentEquiv_tmul, ρ.map_smul, x.property g]

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem simple_of_scalarExtension {A : Type w} [Ring A] [Algebra k A]
    [Nontrivial A] [IsSimpleRing (K ⊗[k] A)] : IsSimpleRing A := by
  rw [isSimpleRing_iff]
  refine ⟨?_⟩
  intro I
  by_cases hI : I = ⊤
  · exact Or.inr hI
  · left
    have : Nontrivial I.ringCon.Quotient :=
      RingCon.nontrivial_quotient.2 (fun h => hI (TwoSidedIdeal.ringCon_injective h))
    have : Nontrivial (K ⊗[k] I.ringCon.Quotient) :=
      (Algebra.TensorProduct.includeRight_injective (B := I.ringCon.Quotient)
        (RingHom.injective (algebraMap k K))).nontrivial
    let q := I.ringCon.mkₐ k
    let f : (K ⊗[k] A) →ₐ[K] (K ⊗[k] I.ringCon.Quotient) :=
      Algebra.TensorProduct.map (AlgHom.id K K) q
    have hf : Function.Injective f := RingHom.injective f.toRingHom
    refine le_antisymm ?_ bot_le
    intro x hx
    have hqx : q x = 0 := Quotient.sound hx
    have hz : f ((1 : K) ⊗ₜ[k] x) = f 0 := by
      rw [Algebra.TensorProduct.map_tmul, hqx, TensorProduct.tmul_zero, map_zero]
    have hinc : Function.Injective
        (Algebra.TensorProduct.includeRight : A →ₐ[k] (K ⊗[k] A)) :=
      Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k K))
    apply (TwoSidedIdeal.mem_bot _).2
    apply hinc
    simpa only [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_zero] using hf hz

private theorem fixed_csa (hn : 0 < n) (ρ : AlgebraAction k K (Mat K n)) :
    CSA.IsCentralSimple k ρ.fixedSubalgebra := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nontrivial ρ.fixedSubalgebra := ρ.fixedSubalgebra.nontrivial
  have : IsSimpleRing (K ⊗[k] ρ.fixedSubalgebra) :=
    IsSimpleRing.of_ringEquiv ρ.descentEquiv.symm.toRingEquiv inferInstance
  refine ⟨simple_of_scalarExtension (k := k) (K := K), ⟨?_⟩, fixed_finite ρ⟩
  intro x hx
  have hcomm (y : ρ.fixedSubalgebra) : (y : Mat K n) * (x : Mat K n) =
      (x : Mat K n) * (y : Mat K n) :=
    congrArg Subtype.val (Subalgebra.mem_center_iff.mp hx y)
  have hcentral : (x : Mat K n) ∈ Subalgebra.center K (Mat K n) := by
    apply Subalgebra.mem_center_iff.mpr
    intro y
    obtain ⟨t, rfl⟩ := ρ.descentEquiv.surjective y
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      rw [ρ.descentEquiv_tmul, smul_mul_assoc, mul_smul_comm, hcomm]
    | add y z hy hz => rw [map_add, add_mul, mul_add, hy, hz]
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).mp hcentral
  have ha_fixed (g : Gal(K/k)) : g a = a := by
    apply (algebraMap K (Mat K n)).injective
    calc
      algebraMap K (Mat K n) (g a) = ρ.act g (algebraMap K (Mat K n) a) := by
        simp only [Algebra.algebraMap_eq_smul_one, ρ.map_smul, ρ.map_one]
      _ = algebraMap K (Mat K n) a := by rw [← ha, x.property g]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := k) a).mpr ha_fixed
  refine Algebra.mem_bot.mpr ⟨b, Subtype.ext ?_⟩
  change algebraMap k (Mat K n) b = (x : Mat K n)
  rw [IsScalarTower.algebraMap_apply k K, hb, ← ha]

/-- The fixed algebra is a degree-`n` form, with its canonical equivariant splitting. -/
theorem descended_form (hn : 0 < n) (c : Cocycle k K n)
    (ρ : AlgebraAction k K (Mat K n)) (_hc : Implements ρ c) :
    CSA.IsCentralSimple k ρ.fixedSubalgebra ∧
      CSA.degree k ρ.fixedSubalgebra = n ∧
      ∃ s : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] Mat K n, IsTransport ρ s ∧
        ∀ (a : K) (x : ρ.fixedSubalgebra), s (a ⊗ₜ[k] x) = a • (x : Mat K n) :=
  let h := fixed_csa hn ρ
  ⟨h, CSA.degree_eq_matrix_size h ρ.descentEquiv, ρ.descentEquiv,
    descentEquiv_isTransport ρ, ρ.descentEquiv_tmul⟩

private def formInclusion {A : Type w} [Ring A] [Algebra k A]
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (ρ : AlgebraAction k K (Mat K n))
    (hρ : IsTransport ρ s) : A →ₐ[k] ρ.fixedSubalgebra :=
  ((s.restrictScalars k).toAlgHom.comp Algebra.TensorProduct.includeRight).codRestrict _
    (fun x g => by
      change ρ.act g (s (1 ⊗ₜ[k] x)) = s (1 ⊗ₜ[k] x)
      rw [hρ, map_one])

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem formInclusion_apply {A : Type w} [Ring A] [Algebra k A]
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (ρ : AlgebraAction k K (Mat K n))
    (hρ : IsTransport ρ s) (x : A) :
    (formInclusion s ρ hρ x : Mat K n) = s (1 ⊗ₜ[k] x) := rfl

/-- Fixed points of the transported action recover the original algebra, in every universe. -/
theorem recover_form {A : Type w} [Ring A] [Algebra k A]
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (ρ : AlgebraAction k K (Mat K n))
    (hρ : IsTransport ρ s) :
    ∃ e : A ≃ₐ[k] ρ.fixedSubalgebra, ∀ x : A, (e x : Mat K n) = s (1 ⊗ₜ[k] x) := by
  let f := formInclusion s ρ hρ
  have hf : Function.Injective f := by
    intro x y hxy
    apply Algebra.TensorProduct.includeRight_injective (A := K)
      (RingHom.injective (algebraMap k K))
    apply s.injective
    exact congrArg Subtype.val hxy
  have : FiniteDimensional k ρ.fixedSubalgebra := fixed_finite ρ
  have : FiniteDimensional k A := FiniteDimensional.of_injective f.toLinearMap hf
  have hdim : Module.finrank k A = Module.finrank k ρ.fixedSubalgebra := by
    rw [← Module.finrank_baseChange (R := K) (S := k) (M' := A),
      ← Module.finrank_baseChange (R := K) (S := k) (M' := ρ.fixedSubalgebra),
      s.toLinearEquiv.finrank_eq, ρ.descentEquiv.toLinearEquiv.finrank_eq]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp hf
  exact ⟨AlgEquiv.ofBijective f ⟨hf, hsurj⟩, formInclusion_apply s ρ hρ⟩

private theorem equivariant_iff_fixed_isomorphic (ρ τ : AlgebraAction k K (Mat K n)) :
    (∃ b : Mat K n ≃ₐ[K] Mat K n, ρ.Equivariant τ b.toAlgHom) ↔
      Nonempty (ρ.fixedSubalgebra ≃ₐ[k] τ.fixedSubalgebra) := by
  constructor
  · rintro ⟨b, hb⟩
    let f := ρ.restrictHom τ b.toAlgHom hb
    refine ⟨AlgEquiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro x y h
      exact Subtype.ext (b.injective (congrArg Subtype.val h))
    · intro y
      have hy (g : Gal(K/k)) : ρ.act g (b.symm (y : Mat K n)) = b.symm (y : Mat K n) := by
        apply b.injective
        exact (hb g (b.symm (y : Mat K n))).trans (by simp only [AlgEquiv.coe_toAlgHom,
          b.apply_symm_apply, y.property g])
      refine ⟨⟨b.symm (y : Mat K n), hy⟩, Subtype.ext (b.apply_symm_apply _)⟩
  · rintro ⟨f⟩
    let b := ρ.descentEquiv.symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) f).trans τ.descentEquiv)
    have hb (a : K) (x : ρ.fixedSubalgebra) : b (a • (x : Mat K n)) = a • (f x : Mat K n) := by
      change τ.descentEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) f
        (ρ.descentEquiv.symm (a • (x : Mat K n)))) = _
      rw [ρ.descentEquiv.symm_apply_eq.mpr (ρ.descentEquiv_tmul a x).symm]
      exact τ.descentEquiv_tmul a (f x)
    refine ⟨b, fun g x => ?_⟩
    change b (ρ.act g x) = τ.act g (b x)
    obtain ⟨t, rfl⟩ := ρ.descentEquiv.surjective x
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [ρ.descentEquiv_tmul, ρ.map_smul, x.property g, hb, hb, τ.map_smul, (f x).property g]
    | add x y hx hy => simp only [map_add, hx, hy]

private theorem cohomologous_iff_fixed_isomorphic (hn : 0 < n) (c d : Cocycle k K n) :
    Cohomologous k K n c d ↔
      Nonempty ((twist c).fixedSubalgebra ≃ₐ[k] (twist d).fixedSubalgebra) :=
  (cohomologous_iff_equivariant hn c d).trans (equivariant_iff_fixed_isomorphic _ _)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem trivial_act (g : Gal(K/k)) (x : Mat K n) :
    (twist (trivial k K n)).act g x = coefficient g x := by
  rw [twist_apply, show (trivial k K n).val g = 1 from rfl, map_one, AlgEquiv.one_apply]

private def matrixOverBase :
    Mat k n →ₐ[k] Mat K n where
  toRingHom := (algebraMap k K).mapMatrix
  commutes' a := by
    ext i j
    change algebraMap k K ((algebraMap k (Mat k n)) a i j) =
      (algebraMap k (Mat K n)) a i j
    by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

private noncomputable def trivial_fixed_equiv :
    Mat k n ≃ₐ[k] (twist (trivial k K n)).fixedSubalgebra := by
  let f := (matrixOverBase (k := k) (K := K) (n := n)).codRestrict
    (twist (trivial k K n)).fixedSubalgebra (fun x g => by
      rw [trivial_act]
      ext i j
      exact g.commutes (x i j))
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    ext i j
    apply (algebraMap k K).injective
    exact congrArg (fun z : (twist (trivial k K n)).fixedSubalgebra =>
      (z : Mat K n) i j) h
  · intro y
    have h (i j : Fin n) : ∃ a : k, algebraMap k K a = (y : Mat K n) i j := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed (F := k) ((y : Mat K n) i j)).2
      intro g
      have hy := y.property g
      rw [trivial_act] at hy
      exact congrArg (fun z : Mat K n => z i j) hy
    choose x hx using h
    exact ⟨x, Subtype.ext (Matrix.ext hx)⟩

private noncomputable def formOfCocycle (hn : 0 < n) (c : Cocycle k K n) : Form k K n :=
  ⟨CSA.toCSA (fixed_csa hn (twist c)), ⟨(twist c).descentEquiv⟩⟩

private noncomputable def chosenSplitting (A : Form k K n) :
    (K ⊗[k] A.val) ≃ₐ[K] Mat K n :=
  Classical.choice A.property

private noncomputable def chosenCocycle (hn : 0 < n) (A : Form k K n) : Cocycle k K n :=
  Classical.choose (twist_surjective hn (transport (chosenSplitting A)))

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem chosenCocycle_spec (hn : 0 < n) (A : Form k K n) :
    twist (chosenCocycle hn A) = transport (chosenSplitting A) :=
  Classical.choose_spec (twist_surjective hn (transport (chosenSplitting A)))

private theorem presentation_fixed (A : Form k K n) (s : (K ⊗[k] A.val) ≃ₐ[K] Mat K n)
    (ρ : AlgebraAction k K (Mat K n)) (c : Cocycle k K n)
    (hρ : IsTransport ρ s) (hc : Implements ρ c) :
    Nonempty ((A.val : Type v) ≃ₐ[k] (twist c).fixedSubalgebra) := by
  obtain rfl := (implements_iff c ρ).1 hc
  obtain ⟨f, _⟩ := recover_form s _ hρ
  exact ⟨f⟩

private theorem chosen_fixed (hn : 0 < n) (A : Form k K n) :
    Nonempty ((A.val : Type v) ≃ₐ[k] (twist (chosenCocycle hn A)).fixedSubalgebra) :=
  presentation_fixed A (chosenSplitting A) _ _ (transport_spec (chosenSplitting A))
    ((implements_iff _ _).2 (chosenCocycle_spec hn A))

private theorem relation_iff (hn : 0 < n) {A B : Form k K n} {c d : Cocycle k K n}
    (hc : Nonempty ((A.val : Type v) ≃ₐ[k] (twist c).fixedSubalgebra))
    (hd : Nonempty ((B.val : Type v) ≃ₐ[k] (twist d).fixedSubalgebra)) :
    Isomorphic k K n A B ↔ Cohomologous k K n c d := by
  obtain ⟨f⟩ := hc
  obtain ⟨g⟩ := hd
  rw [cohomologous_iff_fixed_isomorphic hn]
  exact ⟨fun ⟨h⟩ => ⟨f.symm.trans (h.trans g)⟩, fun ⟨h⟩ => ⟨f.trans (h.trans g.symm)⟩⟩

private noncomputable def classify (hn : 0 < n) : SplitClasses k K n → H1 k K n :=
  Quot.lift (fun A => Quot.mk _ (chosenCocycle hn A))
    (fun A B h => Quot.sound ((relation_iff hn (chosen_fixed hn A) (chosen_fixed hn B)).1 h))

private theorem classify_of_presentation (hn : 0 < n) (A : Form k K n) (c : Cocycle k K n)
    (hc : Nonempty ((A.val : Type v) ≃ₐ[k] (twist c).fixedSubalgebra)) :
    classify hn (Quot.mk _ A) = Quot.mk _ c :=
  Quot.sound ((relation_iff hn (chosen_fixed hn A) hc).1 ⟨AlgEquiv.refl⟩)

private theorem classify_bijective (hn : 0 < n) :
    Function.Bijective (classify (k := k) (K := K) hn) := by
  constructor
  · intro a b
    induction a using Quot.inductionOn with
    | h A =>
      induction b using Quot.inductionOn with
      | h B =>
        intro h
        apply Quot.sound
        exact (relation_iff hn (chosen_fixed hn A) (chosen_fixed hn B)).2
          ((h1_eq_iff _ _).1 h)
  · intro x
    induction x using Quot.inductionOn with
    | h c =>
      exact ⟨Quot.mk _ (formOfCocycle hn c),
        classify_of_presentation hn (formOfCocycle hn c) c ⟨AlgEquiv.refl⟩⟩

/-- Fixed-degree central simple forms are classified by pointed projective first cohomology. -/
theorem classification (hn : 0 < n) :
    ∃ e : SplitClasses k K n ≃ H1 k K n,
      (∀ (A : Form k K n) (s : (K ⊗[k] A.val) ≃ₐ[K] Mat K n)
          (ρ : AlgebraAction k K (Mat K n)) (c : Cocycle k K n),
        IsTransport ρ s → Implements ρ c →
        e (Quot.mk (Isomorphic k K n) A) = Quot.mk (Cohomologous k K n) c) ∧
      (∀ {B : Type w} [Ring B] [Algebra k B]
          (s : (K ⊗[k] B) ≃ₐ[K] Mat K n)
          (ρ : AlgebraAction k K (Mat K n)) (c : Cocycle k K n),
        IsTransport ρ s → Implements ρ c →
        ∃ A : Form k K n, Nonempty (B ≃ₐ[k] (A.val : Type v)) ∧
          e (Quot.mk (Isomorphic k K n) A) = Quot.mk (Cohomologous k K n) c) ∧
      (∀ (c : Cocycle k K n) (ρ : AlgebraAction k K (Mat K n)), Implements ρ c →
        ∃ A : Form k K n, Nonempty ((A.val : Type v) ≃ₐ[k] ρ.fixedSubalgebra) ∧
          e.symm (Quot.mk (Cohomologous k K n) c) = Quot.mk (Isomorphic k K n) A) ∧
      (∃ A : Form k K n, Nonempty ((A.val : Type v) ≃ₐ[k] Mat k n)) ∧
      (∀ A : Form k K n, Nonempty ((A.val : Type v) ≃ₐ[k] Mat k n) →
        e (Quot.mk (Isomorphic k K n) A) = Quot.mk (Cohomologous k K n) (trivial k K n)) := by
  let e : SplitClasses k K n ≃ H1 k K n :=
    Equiv.ofBijective (classify hn) (classify_bijective hn)
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro A s ρ c hs hc
    exact classify_of_presentation hn A c (presentation_fixed A s ρ c hs hc)
  · intro B _ _ s ρ c hs hc
    obtain rfl := (implements_iff c ρ).1 hc
    obtain ⟨f, _⟩ := recover_form s _ hs
    exact ⟨formOfCocycle hn c, ⟨f⟩,
      classify_of_presentation hn (formOfCocycle hn c) c ⟨AlgEquiv.refl⟩⟩
  · intro c ρ hc
    obtain rfl := (implements_iff c ρ).1 hc
    refine ⟨formOfCocycle hn c, ⟨AlgEquiv.refl⟩, e.symm_apply_eq.mpr ?_⟩
    exact (classify_of_presentation hn (formOfCocycle hn c) c ⟨AlgEquiv.refl⟩).symm
  · exact ⟨formOfCocycle hn (trivial k K n), ⟨trivial_fixed_equiv.symm⟩⟩
  · rintro A ⟨f⟩
    exact classify_of_presentation hn A (trivial k K n) ⟨f.trans trivial_fixed_equiv⟩

end FiniteGalois

/-- A positive-size splitting is exactly the condition of degree `n` and being split by `K`. -/
theorem form_iff_degree_splits {A : Type w} [Ring A] [Algebra k A]
    (hn : 0 < n) (hA : CSA.IsCentralSimple k A) :
    Nonempty ((K ⊗[k] A) ≃ₐ[K] Mat K n) ↔ CSA.degree k A = n ∧ CSA.Splits k K A := by
  constructor
  · rintro ⟨s⟩
    exact ⟨CSA.degree_eq_matrix_size hA s, n, hn, ⟨s⟩⟩
  · rintro ⟨hdeg, m, _, ⟨s⟩⟩
    rw [← hdeg, CSA.degree_eq_matrix_size hA s]
    exact ⟨s⟩

end RM03.Brauer.ProjectiveClassification
