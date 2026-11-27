import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.EmbeddingProblem
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.ProperSplitSolutions

/-! Proper weak solutions and the crossed homomorphisms of a split problem. -/

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

universe u v w

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

namespace WeakSolution

variable {P : FiniteEmbeddingProblem Γ B Q} (sol : P.WeakSolution)

/-- The image of a weak lift surjects onto the prescribed quotient. -/
theorem image_surjects_onto_quotient :
    Function.Surjective (fun h : sol.lift.toMonoidHom.range => P.pi (h : B)) := by
  intro q
  obtain ⟨γ, hγ⟩ := P.rho_surjective q
  exact ⟨⟨sol.lift γ, ⟨γ, rfl⟩⟩, (sol.commutes_apply γ).trans hγ⟩

/-- Intersecting the image of the lift with the kernel gives the image of `ker ρ`. -/
theorem image_inf_kernel :
    sol.lift.toMonoidHom.range ⊓ P.kernel =
      P.rho.toMonoidHom.ker.map sol.lift.toMonoidHom := by
  ext b
  constructor
  · rintro ⟨⟨γ, rfl⟩, hγ⟩
    change P.pi (sol.lift γ) = 1 at hγ
    exact ⟨γ, (sol.commutes_apply γ).symm.trans hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    change P.rho γ = 1 at hγ
    exact ⟨⟨γ, rfl⟩, (sol.commutes_apply γ).trans hγ⟩

/-- Properness is equivalent to the lift mapping `ker ρ` onto the kernel of the problem. -/
theorem proper_iff_map_kernel :
    sol.IsProper ↔ P.rho.toMonoidHom.ker.map sol.lift.toMonoidHom = P.kernel := by
  rw [← sol.image_inf_kernel]
  constructor
  · intro h
    rw [MonoidHom.range_eq_top_of_surjective _ h, top_inf_eq]
  · intro h b
    obtain ⟨x, hx⟩ := sol.image_surjects_onto_quotient (P.pi b)
    have hb : b * (x : B)⁻¹ ∈ P.kernel := by
      change P.pi (b * (x : B)⁻¹) = 1
      simp [hx]
    have hmem : b * (x : B)⁻¹ ∈ sol.lift.toMonoidHom.range ⊓ P.kernel := h.symm ▸ hb
    have hm := sol.lift.toMonoidHom.range.mul_mem hmem.1 x.property
    simpa using hm

end WeakSolution

/-- The action on the kernel by conjugation through a section. -/
abbrev sectionAction (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B) :
    Q →* MulAut P.kernel :=
  Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.sectionAction P s

/-- Continuous maps satisfying the crossed-homomorphism law for the section. -/
abbrev ContinuousCrossedHom (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B) :=
  Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.ContinuousCrossedHom P s

variable (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B)

private theorem section_apply (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q) (q : Q) :
    P.pi (s q) = q :=
  DFunLike.congr_fun hs q

private def kernelCoordinate (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q) (b : B) :
    P.kernel :=
  ⟨b * (s (P.pi b))⁻¹, by
    change P.pi (b * (s (P.pi b))⁻¹) = 1
    simp [section_apply P s hs]⟩

private def splitMulEquiv (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q) :
    SemidirectProduct P.kernel Q (sectionAction P s) ≃* B where
  toFun x := (x.left : B) * s x.right
  invFun b := ⟨kernelCoordinate P s hs b, P.pi b⟩
  left_inv x := by
    have hp : P.pi ((x.left : B) * s x.right) = x.right := by
      have ha : P.pi (x.left : B) = 1 := x.left.property
      simp [ha, section_apply P s hs]
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change ((x.left : B) * s x.right) * (s (P.pi ((x.left : B) * s x.right)))⁻¹ = _
      simp [hp]
    · exact hp
  right_inv b := by
    change b * (s (P.pi b))⁻¹ * s (P.pi b) = b
    simp
  map_mul' x y := by
    have hconj : ((sectionAction P s x.right y.left : P.kernel) : B) =
        s x.right * (y.left : B) * (s x.right)⁻¹ :=
      MulAut.conjNormal_apply (s x.right) y.left
    change (x.left : B) * (sectionAction P s x.right y.left : B) * s (x.right * y.right) =
      ((x.left : B) * s x.right) * ((y.left : B) * s y.right)
    rw [hconj, map_mul]
    simp [mul_assoc]

/-- The semidirect product identifies with the middle group by multiplying by the section. -/
theorem splitMulEquiv_exists (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q) :
    ∃ e : SemidirectProduct P.kernel Q (sectionAction P s) ≃* B,
      (∀ x, e x = (x.left : B) * s x.right) ∧
      (∀ b, (e.symm b).right = P.pi b) :=
  ⟨splitMulEquiv P s hs, fun _ => rfl, fun _ => rfl⟩

private theorem crossedHom_map_one (z : ContinuousCrossedHom P s) : z.val 1 = 1 := by
  have h : z.val 1 = z.val 1 * z.val 1 := by simpa using z.property 1 1
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

private def toWeakSolution (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q)
    (z : ContinuousCrossedHom P s) : P.WeakSolution where
  lift :=
    ⟨{
      toFun := fun γ => (z.val γ : B) * s (P.rho γ)
      map_one' := by simp [crossedHom_map_one P s z]
      map_mul' := fun γ η => by
        let e := splitMulEquiv P s hs
        change e ⟨z.val (γ * η), P.rho (γ * η)⟩ = e ⟨z.val γ, P.rho γ⟩ * e ⟨z.val η, P.rho η⟩
        rw [← map_mul]
        exact congrArg e (SemidirectProduct.ext (z.property γ η) (map_mul P.rho γ η))
    }, by
      let eval : P.kernel × Q → B := fun x => (x.1 : B) * s x.2
      exact (continuous_of_discreteTopology (f := eval)).comp
        (z.val.continuous_toFun.prodMk P.rho.continuous_toFun)⟩
  commutes := by
    apply ContinuousMonoidHom.ext
    intro γ
    change P.pi ((z.val γ : B) * s (P.rho γ)) = P.rho γ
    have ha : P.pi (z.val γ : B) = 1 := (z.val γ).property
    simp [ha, section_apply P s hs]

private def ofWeakSolution (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q)
    (sol : P.WeakSolution) : ContinuousCrossedHom P s :=
  ⟨⟨fun γ => kernelCoordinate P s hs (sol.lift γ),
    (continuous_of_discreteTopology (f := kernelCoordinate P s hs)).comp
      sol.lift.continuous_toFun⟩, by
    intro γ η
    let e := (splitMulEquiv P s hs).symm
    have h := congrArg SemidirectProduct.left
      ((e.toMonoidHom.comp sol.lift.toMonoidHom).map_mul γ η)
    change (e (sol.lift (γ * η))).left =
      (e (sol.lift γ)).left * sectionAction P s (P.pi (sol.lift γ)) (e (sol.lift η)).left at h
    rw [sol.commutes_apply] at h
    exact h⟩

private theorem weakSolution_ext {a b : P.WeakSolution} (h : a.lift = b.lift) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The section gives inverse correspondences between crossed homomorphisms and weak lifts. -/
theorem crossedHomEquivWeakSolution_exists (hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q) :
    ∃ e : ContinuousCrossedHom P s ≃ P.WeakSolution,
      (∀ z γ, (e z).lift γ = (z.val γ : B) * s (P.rho γ)) ∧
      (∀ sol γ, ((e.symm sol).val γ : B) = sol.lift γ * (s (P.rho γ))⁻¹) := by
  let e : ContinuousCrossedHom P s ≃ P.WeakSolution :=
    { toFun := toWeakSolution P s hs
      invFun := ofWeakSolution P s hs
      left_inv := by
        intro z
        apply Subtype.ext
        apply ContinuousMap.ext
        intro γ
        apply Subtype.ext
        have hp := (toWeakSolution P s hs z).commutes_apply γ
        change P.pi ((z.val γ : B) * s (P.rho γ)) = P.rho γ at hp
        change (z.val γ : B) * s (P.rho γ) *
          (s (P.pi ((z.val γ : B) * s (P.rho γ))))⁻¹ = _
        simp [hp]
      right_inv := by
        intro sol
        apply weakSolution_ext P
        apply ContinuousMonoidHom.ext
        intro γ
        change sol.lift γ * (s (P.pi (sol.lift γ)))⁻¹ * s (P.rho γ) = sol.lift γ
        simp [sol.commutes_apply] }
  exact ⟨e, fun _ _ => rfl, fun sol γ => by
    change sol.lift γ * (s (P.pi (sol.lift γ)))⁻¹ = _
    rw [sol.commutes_apply]⟩

/-- A crossed homomorphism restricts to a homomorphism on `ker ρ`, where surjectivity
characterizes properness of the associated lift. -/
theorem crossedHom_restriction_and_properness
    (_hs : P.pi.toMonoidHom.comp s = MonoidHom.id Q)
    (z : ContinuousCrossedHom P s) :
    ∃ f : P.rho.toMonoidHom.ker →* P.kernel,
      (∀ n, f n = z.val (n : Γ)) ∧
      ∀ sol : P.WeakSolution,
        (∀ γ, sol.lift γ = (z.val γ : B) * s (P.rho γ)) →
        (sol.IsProper ↔ Function.Surjective f) := by
  let f : P.rho.toMonoidHom.ker →* P.kernel :=
    { toFun := fun n => z.val (n : Γ)
      map_one' := crossedHom_map_one P s z
      map_mul' := fun n m => by
        change z.val ((n : Γ) * (m : Γ)) = z.val (n : Γ) * z.val (m : Γ)
        have hn : P.rho (n : Γ) = 1 := n.property
        simpa only [hn, map_one, MulAut.one_apply] using z.property (n : Γ) (m : Γ) }
  refine ⟨f, fun _ => rfl, ?_⟩
  intro sol hlift
  have hres (n : P.rho.toMonoidHom.ker) : sol.lift (n : Γ) = (z.val (n : Γ) : B) := by
    have hn : P.rho (n : Γ) = 1 := n.property
    simp [hlift, hn]
  rw [sol.proper_iff_map_kernel]
  constructor
  · intro h a
    have ha : (a : B) ∈ P.rho.toMonoidHom.ker.map sol.lift.toMonoidHom := h.symm ▸ a.property
    obtain ⟨γ, hγ, hγb⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨γ, hγ⟩, Subtype.ext ((hres ⟨γ, hγ⟩).symm.trans hγb)⟩
  · intro hf
    apply le_antisymm
    · rw [← sol.image_inf_kernel]
      exact inf_le_right
    · intro b hb
      obtain ⟨n, hn⟩ := hf ⟨b, hb⟩
      exact ⟨(n : Γ), n.property, (hres n).trans (congrArg Subtype.val hn)⟩

end GaloisFormalization.IG.FiniteEmbeddingProblem
