import Mathlib

/-!
# A minimal game model for the PRP/PRF switching lemma

This module deliberately implements only the part of Section 3.1 needed for a
single-user switching argument.  Randomness lives in the choice of the whole
oracle; the query strategy itself is deterministic and may be adaptive.
-/

namespace PRPPRFSwitching

universe u v

/-- A query/response transcript, in chronological order. -/
abbrev Transcript (X : Type u) (Y : Type v) := List (X × Y)

/--
A deterministic adaptive query strategy.  `none` means that the strategy has
stopped; otherwise the next query may depend on all previous responses.
-/
abbrev QueryStrategy (X : Type u) (Y : Type v) := List Y → Option X

/-- Run at most `fuel` oracle queries. -/
def run (A : QueryStrategy X Y) (oracle : X → Y) :
    ℕ → List Y → Transcript X Y
  | 0, _ => []
  | fuel + 1, responses =>
      match A responses with
      | none => []
      | some x =>
          let y := oracle x
          (x, y) :: run A oracle fuel (responses ++ [y])

@[simp]
theorem run_zero (A : QueryStrategy X Y) (oracle : X → Y)
    (responses : List Y) :
    run A oracle 0 responses = [] := rfl

theorem run_length_le (A : QueryStrategy X Y) (oracle : X → Y)
    (fuel : ℕ) (responses : List Y) :
    (run A oracle fuel responses).length ≤ fuel := by
  induction fuel generalizing responses with
  | zero => simp
  | succ fuel ih =>
      simp only [run]
      split <;> simp_all

/-- The transcript distribution induced by sampling an oracle once. -/
noncomputable def transcriptPMF (A : QueryStrategy X Y) (fuel : ℕ)
    (oracles : PMF (X → Y)) : PMF (Transcript X Y) :=
  oracles.map fun oracle => run A oracle fuel []

/-- A uniformly sampled function is the ideal PRF oracle. -/
noncomputable def randomFunction (X : Type u) (Y : Type v)
    [Fintype X] [Fintype Y] [DecidableEq X] [Nonempty Y] : PMF (X → Y) :=
  PMF.uniformOfFintype (X → Y)

/-- A uniformly sampled permutation, coerced to its forward function. -/
noncomputable def randomPermutation (X : Type u)
    [Fintype X] [DecidableEq X] [Nonempty X] : PMF (X → X) :=
  (PMF.uniformOfFintype (Equiv.Perm X)).map fun p => p

/-- Probability that a predicate accepts, converted to `ℝ`. -/
noncomputable def eventProbability
    (p : PMF Ω) (event : Ω → Bool) : ℝ :=
  ((p.map event) true).toReal

/-- Distinguishing advantage of a fixed decision predicate. -/
noncomputable def advantage
    (real ideal : PMF Ω) (decision : Ω → Bool) : ℝ :=
  |eventProbability real decision - eventProbability ideal decision|

/-- PRF-side transcript distribution. -/
noncomputable def prfTranscripts (X : Type u)
    [Fintype X] [DecidableEq X] [Nonempty X]
    (A : QueryStrategy X X) (q : ℕ) : PMF (Transcript X X) :=
  transcriptPMF A q (randomFunction X X)

/-- PRP-side transcript distribution. -/
noncomputable def prpTranscripts (X : Type u)
    [Fintype X] [DecidableEq X] [Nonempty X]
    (A : QueryStrategy X X) (q : ℕ) : PMF (Transcript X X) :=
  transcriptPMF A q (randomPermutation X)

/-- The response list extracted from a transcript. -/
def responses (t : Transcript X Y) : List Y := t.map Prod.snd

/-- The queries in a transcript are all distinct. -/
def HasFreshQueries [DecidableEq X] (t : Transcript X Y) : Prop :=
  (t.map Prod.fst).Nodup

/-- The responses in a transcript are all distinct. -/
def HasDistinctResponses [DecidableEq Y] (t : Transcript X Y) : Prop :=
  (responses t).Nodup

/-- A response collision is the bad event in the standard switching proof. -/
def HasResponseCollision [DecidableEq Y] (t : Transcript X Y) : Prop :=
  ¬ HasDistinctResponses t

theorem permutation_preserves_nodup [DecidableEq X]
    (p : Equiv.Perm X) (xs : List X) (h : xs.Nodup) :
    (xs.map p).Nodup := by
  exact h.map p.injective

/--
The conventional numerical PRP/PRF switching claim.  It is packaged as a
proposition so that the game model and the eventual main theorem have a stable
interface while the collision/coupling proof is developed separately.

The side condition `q ≤ |X|` is natural for the exact falling-factorial proof.
The looser birthday bound itself remains meaningful without it (and becomes
trivial once its right-hand side is at least one).
-/
def SwitchingBound (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X]
    (A : QueryStrategy X X) (q : ℕ) : Prop :=
  ∀ decision : Transcript X X → Bool,
    advantage (prfTranscripts X A q) (prpTranscripts X A q) decision
      ≤ (q * (q - 1) : ℝ) / (2 * Fintype.card X)

@[simp]
theorem transcriptPMF_zero (A : QueryStrategy X Y) (oracles : PMF (X → Y)) :
    transcriptPMF A 0 oracles = PMF.pure [] := by
  apply PMF.ext
  intro t
  by_cases h : t = []
  · subst t
    simpa [transcriptPMF, run, PMF.map_apply] using oracles.tsum_coe
  · simp [transcriptPMF, run, PMF.map_apply, h]

/-- The switching bound is exact when the adversary makes no queries. -/
theorem switchingBound_zero (X : Type u)
    [Fintype X] [DecidableEq X] [Nonempty X]
    (A : QueryStrategy X X) : SwitchingBound X A 0 := by
  intro decision
  rw [show prfTranscripts X A 0 = PMF.pure [] by
        simp [prfTranscripts],
      show prpTranscripts X A 0 = PMF.pure [] by
        simp [prpTranscripts]]
  norm_num [advantage]

/--
For one query, equality of every one-point oracle marginal is enough to make
the complete adaptive transcript distributions equal.
-/
theorem transcriptPMF_one_eq (A : QueryStrategy X Y)
    (left right : PMF (X → Y))
    (hMarginal : ∀ x, left.map (fun oracle => oracle x) =
      right.map (fun oracle => oracle x)) :
    transcriptPMF A 1 left = transcriptPMF A 1 right := by
  cases hA : A [] with
  | none =>
      change left.map (fun oracle => run A oracle 1 []) =
        right.map (fun oracle => run A oracle 1 [])
      have hc : (fun oracle => run A oracle 1 []) =
          Function.const (X → Y) [] := by
        funext oracle
        simp [run, hA]
      rw [hc, left.map_const, right.map_const]
  | some x =>
      rw [show transcriptPMF A 1 left =
          (left.map fun oracle => oracle x).map (fun y => [(x, y)]) by
            simp only [transcriptPMF, run, hA]
            rw [PMF.map_comp]
            rfl,
        show transcriptPMF A 1 right =
          (right.map fun oracle => oracle x).map (fun y => [(x, y)]) by
            simp only [transcriptPMF, run, hA]
            rw [PMF.map_comp]
            rfl,
        hMarginal x]

end PRPPRFSwitching
