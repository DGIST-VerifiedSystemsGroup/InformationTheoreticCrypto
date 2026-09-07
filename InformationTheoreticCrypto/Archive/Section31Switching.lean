import InformationTheoreticCrypto.Section31
import InformationTheoreticCrypto.Archive.PermutationCompletion

/-!
# PRP/PRF switching inside the Section 3.1 framework

This module instantiates the abstract systems, query functions, transcript
distributions, and advantages from `Section31.lean`.  The bridge theorem below
shows that Section 3.1 interaction with a stateless system is exactly the
concrete runner used by the switching proof.
-/

namespace InformationTheoreticSecurity.Section31

open PRPPRFSwitching

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]

theorem last_ofList_eq_getLast (xs : List X) (h : xs ≠ []) :
    NonemptyHistory.last (NonemptyHistory.ofList xs h) = xs.getLast h := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x tail => rfl

theorem last_ofList_queries_append (tr : Transcript X X) (x : X) :
    NonemptyHistory.last
        (NonemptyHistory.ofList (queries tr ++ [x]) (by simp)) = x := by
  rw [last_ofList_eq_getLast]
  simp

/-- Section 3.1 interaction against a stateless oracle equals the original
transcript followed by the concrete runner's remaining transcript. -/
theorem interact_statelessSystem_eq_run (Q : QueryFunction X X) (f : X → X)
    (fuel : ℕ) (tr : Transcript X X) :
    interact Q (statelessSystem f) fuel tr =
      tr ++ PRPPRFSwitching.run Q.next f fuel (responses tr) := by
  induction fuel generalizing tr with
  | zero => simp [interact, PRPPRFSwitching.run]
  | succ fuel ih =>
      cases hnext : Q.next (responses tr) with
      | none => simp [interact, PRPPRFSwitching.run, hnext]
      | some x =>
          simp only [interact, PRPPRFSwitching.run, hnext, statelessSystem,
            last_ofList_queries_append]
          rw [ih]
          simp [responses, List.map_append, List.append_assoc]

theorem transcript_statelessSystem_eq_run (q : ℕ) (Q : QueryFunction X X)
    (f : X → X) :
    transcript q Q (statelessSystem f) =
      PRPPRFSwitching.run Q.next f q [] := by
  simpa [transcript, responses] using interact_statelessSystem_eq_run Q f q []

/-- The Section 3.1 random system obtained from a uniform random function. -/
noncomputable def randomFunctionSystem : RandomSystem X X :=
  randomStatelessSystem (PRPPRFSwitching.randomFunction X X)

/-- The Section 3.1 random system obtained from a uniform random permutation. -/
noncomputable def randomPermutationSystem : RandomSystem X X :=
  randomStatelessSystem (PRPPRFSwitching.randomPermutation X)

theorem transcriptDistribution_randomStatelessSystem
    (q : ℕ) (Q : QueryFunction X X) (F : PMF (X → X)) :
    transcriptDistribution q Q (randomStatelessSystem F) =
      PRPPRFSwitching.transcriptPMF Q.next q F := by
  rw [transcriptDistribution, randomStatelessSystem,
    PRPPRFSwitching.transcriptPMF, PMF.map_comp]
  apply congrArg (fun g => F.map g)
  funext f
  exact transcript_statelessSystem_eq_run q Q f

theorem transcriptDistribution_randomFunctionSystem
    (q : ℕ) (Q : QueryFunction X X) :
    transcriptDistribution q Q (randomFunctionSystem (X := X)) =
      PRPPRFSwitching.prfTranscripts X Q.next q := by
  simp [randomFunctionSystem, PRPPRFSwitching.prfTranscripts,
    transcriptDistribution_randomStatelessSystem]

theorem transcriptDistribution_randomPermutationSystem
    (q : ℕ) (Q : QueryFunction X X) :
    transcriptDistribution q Q (randomPermutationSystem (X := X)) =
      PRPPRFSwitching.prpTranscripts X Q.next q := by
  simp [randomPermutationSystem, PRPPRFSwitching.prpTranscripts,
    transcriptDistribution_randomStatelessSystem]

theorem acceptanceProbability_eq_eventProbability
    (A : DeterministicDistinguisher q X X) (S : RandomSystem X X) :
    acceptanceProbability A S =
      PRPPRFSwitching.eventProbability
        (transcriptDistribution q A.query S) A.decision := rfl

/-- PRP/PRF switching, stated directly with Section 3.1's systems,
deterministic distinguisher, and Equation (1) advantage. -/
theorem deterministic_prp_prf_switching
    (A : DeterministicDistinguisher q X X) :
    distinguishingAdvantage
        (randomFunctionSystem (X := X))
        (randomPermutationSystem (X := X)) A ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  rw [distinguishingAdvantage, acceptanceProbability_eq_eventProbability,
    acceptanceProbability_eq_eventProbability,
    transcriptDistribution_randomFunctionSystem,
    transcriptDistribution_randomPermutationSystem]
  exact PRPPRFSwitching.Lazy.switchingBound_all A.query.next q A.decision

/-- The same bound for the randomized distinguisher of Section 3.1.  This is
the convex closure of the deterministic theorem: first condition on the
sampled pair `(Q,d)`, apply the deterministic bound, and average. -/
theorem randomized_prp_prf_switching (A : Distinguisher q X X) :
    randomizedAdvantage
        (randomFunctionSystem (X := X))
        (randomPermutationSystem (X := X)) A ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  let S₀ := randomFunctionSystem (X := X)
  let S₁ := randomPermutationSystem (X := X)
  let B : ℝ := (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X)
  let w : DeterministicDistinguisher q X X → ℝ := fun a => (A a).toReal
  let u : DeterministicDistinguisher q X X → ℝ := fun a => acceptanceProbability a S₀
  let v : DeterministicDistinguisher q X X → ℝ := fun a => acceptanceProbability a S₁
  have hw : Summable w := by
    apply ENNReal.summable_toReal
    rw [A.tsum_coe]
    simp
  have hw_nonneg : ∀ a, 0 ≤ w a := fun _ => ENNReal.toReal_nonneg
  have hw_sum : ∑' a, w a = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => A.apply_ne_top a), A.tsum_coe]
    rfl
  have hu_nonneg : ∀ a, 0 ≤ u a := fun _ => ENNReal.toReal_nonneg
  have hv_nonneg : ∀ a, 0 ≤ v a := fun _ => ENNReal.toReal_nonneg
  have hu_one : ∀ a, u a ≤ 1 := by
    intro a
    exact PRPPRFSwitching.Lazy.eventProbability_le_one
      (transcriptDistribution q a.query S₀) a.decision
  have hv_one : ∀ a, v a ≤ 1 := by
    intro a
    exact PRPPRFSwitching.Lazy.eventProbability_le_one
      (transcriptDistribution q a.query S₁) a.decision
  have hwu : Summable (fun a => w a * u a) := by
    apply Summable.of_nonneg_of_le
    · intro a
      exact mul_nonneg ENNReal.toReal_nonneg (hu_nonneg a)
    · intro a
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hu_one a)
    · exact hw
  have hwv : Summable (fun a => w a * v a) := by
    apply Summable.of_nonneg_of_le
    · intro a
      exact mul_nonneg ENNReal.toReal_nonneg (hv_nonneg a)
    · intro a
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hv_one a)
    · exact hw
  have hdiff : Summable (fun a => w a * (u a - v a)) := by
    have h := hwu.sub hwv
    have heq : (fun a => w a * u a - w a * v a) =
        (fun a => w a * (u a - v a)) := by
      funext a
      ring
    rwa [heq] at h
  have hnorm : Summable (fun a => ‖w a * (u a - v a)‖) := hdiff.norm
  have habsSummable : Summable (fun a => w a * |u a - v a|) := by
    convert hnorm using 1
    funext a
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nonneg a)]
  have hbound : ∀ a, |u a - v a| ≤ B := by
    intro a
    simpa [u, v, S₀, S₁, B, distinguishingAdvantage] using
      deterministic_prp_prf_switching (X := X) a
  rw [randomizedAdvantage, randomizedAcceptanceProbability]
  change |(∑' a, w a * u a) - ∑' a, w a * v a| ≤ B
  rw [← hwu.tsum_sub hwv]
  have htsum : (∑' a, (w a * u a - w a * v a)) =
      ∑' a, w a * (u a - v a) := by
    apply tsum_congr
    intro a
    ring
  rw [htsum]
  calc
    |∑' a, w a * (u a - v a)| = ‖∑' a, w a * (u a - v a)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' a, ‖w a * (u a - v a)‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' a, w a * |u a - v a| := by
      apply tsum_congr
      intro a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nonneg a)]
    _ ≤ ∑' a, w a * B := by
      apply Summable.tsum_le_tsum
      · intro a
        exact mul_le_mul_of_nonneg_left (hbound a) ENNReal.toReal_nonneg
      · exact habsSummable
      · exact hw.mul_right B
    _ = B := by rw [tsum_mul_right, hw_sum, one_mul]

end InformationTheoreticSecurity.Section31
