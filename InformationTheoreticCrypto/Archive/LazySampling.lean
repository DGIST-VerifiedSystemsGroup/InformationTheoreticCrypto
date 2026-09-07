import InformationTheoreticCrypto.Archive.PRPPRFSwitching

/-!
# Lazy-sampling oracles

This is the proof-oriented layer for the PRP/PRF switching lemma.  The public
statement remains phrased using whole uniformly sampled functions and
permutations; the definitions here expose one fresh value at a time.
-/

namespace PRPPRFSwitching.Lazy

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The finite table exposed so far, together with its used range. -/
structure OracleState (X : Type u) [Fintype X] [DecidableEq X] where
  table : X → Option X
  usedOutputs : Finset X

def initialState (X : Type u) [Fintype X] [DecidableEq X] : OracleState X where
  table := fun _ => none
  usedOutputs := ∅

/-- Extend a lazy table at `x` with response `y`. -/
def store (s : OracleState X) (x y : X) : OracleState X where
  table := fun z => if z = x then some y else s.table z
  usedOutputs := insert y s.usedOutputs

@[simp]
theorem initialState_lookup (x : X) : (initialState X).table x = none := rfl

@[simp]
theorem initialState_usedOutputs : (initialState X).usedOutputs = ∅ := rfl

@[simp]
theorem store_lookup_same (s : OracleState X) (x y : X) :
    (store s x y).table x = some y := by
  simp [store]

theorem store_lookup_of_ne (s : OracleState X) {x z y : X} (h : z ≠ x) :
    (store s x y).table z = s.table z := by
  simp [store, h]

@[simp]
theorem store_usedOutputs (s : OracleState X) (x y : X) :
    (store s x y).usedOutputs = insert y s.usedOutputs := rfl

theorem response_mem_store (s : OracleState X) (x y : X) :
    y ∈ (store s x y).usedOutputs := by
  simp

/-- Every stored response is recorded in `usedOutputs`. -/
def CoversTable (s : OracleState X) : Prop :=
  ∀ ⦃x y⦄, s.table x = some y → y ∈ s.usedOutputs

/-- `usedOutputs` is exactly the range of the currently defined table. -/
def ExactUsed (s : OracleState X) : Prop :=
  ∀ y, y ∈ s.usedOutputs ↔ ∃ x, s.table x = some y

/-- The stored table is injective on defined inputs. -/
def InjectiveTable (s : OracleState X) : Prop :=
  ∀ ⦃x₁ x₂ y⦄, s.table x₁ = some y → s.table x₂ = some y → x₁ = x₂

theorem initialState_covers : CoversTable (initialState X) := by
  intro x y h
  simp at h

theorem initialState_exactUsed : ExactUsed (initialState X) := by
  intro y
  simp

theorem initialState_injective : InjectiveTable (initialState X) := by
  intro x₁ x₂ y h
  simp at h

theorem store_covers (s : OracleState X) (x y : X) (hs : CoversTable s) :
    CoversTable (store s x y) := by
  intro z w hzw
  by_cases hzx : z = x
  · subst z
    simp only [store_lookup_same] at hzw
    cases hzw
    simp
  · rw [store_lookup_of_ne s hzx] at hzw
    exact Finset.mem_insert_of_mem (hs hzw)

theorem store_exactUsed (s : OracleState X) (x y : X)
    (hx : s.table x = none) (hs : ExactUsed s) :
    ExactUsed (store s x y) := by
  intro w
  constructor
  · intro hw
    simp only [store_usedOutputs, Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact ⟨x, store_lookup_same s x w⟩
    · obtain ⟨z, hz⟩ := (hs w).mp hw
      have hzx : z ≠ x := by
        intro h
        subst z
        rw [hx] at hz
        contradiction
      exact ⟨z, by simpa only [store_lookup_of_ne s hzx] using hz⟩
  · rintro ⟨z, hz⟩
    by_cases hzx : z = x
    · subst z
      simp only [store_lookup_same] at hz
      cases hz
      simp
    · rw [store_lookup_of_ne s hzx] at hz
      exact Finset.mem_insert_of_mem ((hs w).mpr ⟨z, hz⟩)

theorem store_injective (s : OracleState X) (x y : X)
    (hs : InjectiveTable s) (hx : s.table x = none)
    (hy : y ∉ s.usedOutputs) (hc : CoversTable s) :
    InjectiveTable (store s x y) := by
  intro z₁ z₂ w h₁ h₂
  by_cases h₁x : z₁ = x
  · subst z₁
    simp only [store_lookup_same] at h₁
    cases h₁
    by_cases h₂x : z₂ = x
    · exact h₂x.symm
    · rw [store_lookup_of_ne s h₂x] at h₂
      exact False.elim (hy (hc h₂))
  · rw [store_lookup_of_ne s h₁x] at h₁
    by_cases h₂x : z₂ = x
    · subst z₂
      simp only [store_lookup_same] at h₂
      cases h₂
      exact False.elim (hy (hc h₁))
    · rw [store_lookup_of_ne s h₂x] at h₂
      exact hs h₁ h₂

/-- One oracle query transforms a lazy state probabilistically. -/
abbrev Step (X : Type u) [Fintype X] [DecidableEq X] :=
  X → OracleState X → PMF (X × OracleState X)

/--
Lazy random function: reuse a stored answer; for a fresh input sample uniformly
from the entire codomain.
-/
noncomputable def rfStep : Step X := fun x s =>
  match s.table x with
  | some y => PMF.pure (y, s)
  | none =>
      (PMF.uniformOfFintype X).map fun y => (y, store s x y)

/-- Outputs still available to a lazy random permutation. -/
def availableOutputs (s : OracleState X) : Finset X :=
  Finset.univ \ s.usedOutputs

theorem mem_availableOutputs_iff (s : OracleState X) (y : X) :
    y ∈ availableOutputs s ↔ y ∉ s.usedOutputs := by
  simp [availableOutputs]

theorem availableOutputs_nonempty_of_card_lt (s : OracleState X)
    (hcard : s.usedOutputs.card < Fintype.card X) :
    (availableOutputs s).Nonempty := by
  rw [availableOutputs, Finset.sdiff_nonempty]
  intro hsub
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_univ] at hc
  exact (Nat.not_le_of_lt hcard) hc

theorem store_used_card_le_succ (s : OracleState X) (x y : X) :
    (store s x y).usedOutputs.card ≤ s.usedOutputs.card + 1 := by
  simp only [store_usedOutputs]
  exact Finset.card_insert_le y s.usedOutputs

/--
One-step switching coupling.  The left coordinate is uniform on all outputs.
If it is unused, both sides return it.  On collision, the right coordinate is
resampled uniformly from the outputs still available to the permutation.
-/
noncomputable def freshOutputCoupling (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) : PMF (X × X) :=
  (PMF.uniformOfFintype X).bind fun y =>
    if y ∈ availableOutputs s then
      PMF.pure (y, y)
    else
      (PMF.uniformOfFinset (availableOutputs s) havailable).map fun z => (y, z)

theorem freshOutputCoupling_fst (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) :
    (freshOutputCoupling s havailable).map Prod.fst =
      PMF.uniformOfFintype X := by
  classical
  rw [freshOutputCoupling, PMF.map_bind]
  have hinner : ∀ y : X,
      (if y ∈ availableOutputs s then PMF.pure (y, y)
        else (PMF.uniformOfFinset (availableOutputs s) havailable).map
          fun z => (y, z)).map Prod.fst = PMF.pure y := by
    intro y
    by_cases hy : y ∈ availableOutputs s
    · simp only [hy, ↓reduceIte]
      exact PMF.pure_map Prod.fst (y, y)
    · simp only [hy, ↓reduceIte]
      rw [PMF.map_comp]
      have hf : (Prod.fst ∘ fun z : X => (y, z)) = Function.const X y := by
        funext z
        rfl
      rw [hf, PMF.map_const]
  simp_rw [hinner]
  exact PMF.bind_pure (p := PMF.uniformOfFintype X)

private theorem ennreal_mixture (N A U : ℕ) (hA : 0 < A) (h : A + U = N) :
    ((N : ENNReal)⁻¹) * (1 + (U : ENNReal) * (A : ENNReal)⁻¹) =
      (A : ENNReal)⁻¹ := by
  have hNn : N ≠ 0 := by omega
  have hAn : A ≠ 0 := Nat.ne_of_gt hA
  have hL : ((N : ENNReal)⁻¹) * (1 + (U : ENNReal) * (A : ENNReal)⁻¹) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [hNn]
    · exact ENNReal.add_ne_top.mpr ⟨by simp,
        ENNReal.mul_ne_top (by simp) (by simp [hAn])⟩
  have hR : (A : ENNReal)⁻¹ ≠ ⊤ := by simp [hAn]
  apply (ENNReal.toReal_eq_toReal_iff' hL hR).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_add (by simp) (by apply ENNReal.mul_ne_top <;> simp [hAn])]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_one]
  have hAr : (A : ℝ) ≠ 0 := by exact_mod_cast hAn
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hNn
  field_simp
  exact_mod_cast h

private theorem sum_mixture (S : Finset X) {a : X} (ha : a ∈ S) (c : ENNReal) :
    (∑ b : X, if b ∈ S then (if a = b then 1 else 0) else c) =
      1 + ((Fintype.card X - S.card : ℕ) : ENNReal) * c := by
  rw [Finset.sum_ite]
  simp [ha]
  congr 2
  norm_cast
  rw [show ({x : X | x ∉ S} : Finset X) = Finset.univ \ S by ext x; simp]
  rw [Finset.card_sdiff]
  simp

theorem freshOutputCoupling_snd (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) :
    (freshOutputCoupling s havailable).map Prod.snd =
      PMF.uniformOfFinset (availableOutputs s) havailable := by
  classical
  rw [freshOutputCoupling, PMF.map_bind]
  have hinner : ∀ y : X,
      (if y ∈ availableOutputs s then PMF.pure (y, y)
        else (PMF.uniformOfFinset (availableOutputs s) havailable).map
          fun z => (y, z)).map Prod.snd =
        if y ∈ availableOutputs s then PMF.pure y
        else PMF.uniformOfFinset (availableOutputs s) havailable := by
    intro y
    by_cases hy : y ∈ availableOutputs s
    · simp only [hy, ↓reduceIte]
      exact PMF.pure_map Prod.snd (y, y)
    · simp only [hy, ↓reduceIte, PMF.map_comp]
      have hf : (Prod.snd ∘ fun z : X => (y, z)) = id := by
        funext z
        rfl
      rw [hf, PMF.map_id]
  simp_rw [hinner]
  apply PMF.ext
  intro a
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFinset_apply]
  rw [tsum_fintype]
  by_cases ha : a ∈ availableOutputs s
  · simp only [ha, ↓reduceIte]
    have hterm : ∀ b : X,
        (if b ∈ availableOutputs s then PMF.pure b
          else PMF.uniformOfFinset (availableOutputs s) havailable) a =
          if b ∈ availableOutputs s then (if a = b then 1 else 0)
          else ((availableOutputs s).card : ENNReal)⁻¹ := by
      intro b
      by_cases hb : b ∈ availableOutputs s <;>
        simp [hb, ha, PMF.pure_apply, PMF.uniformOfFinset_apply]
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_mixture (availableOutputs s) ha]
    apply ennreal_mixture
    · exact Finset.card_pos.mpr havailable
    · exact Nat.add_sub_of_le (Finset.card_le_univ (availableOutputs s))
  · simp only [ha, ↓reduceIte]
    have hz : ∀ i : X,
        (if i ∈ availableOutputs s then PMF.pure i
          else PMF.uniformOfFinset (availableOutputs s) havailable) a = 0 := by
      intro i
      by_cases hi : i ∈ availableOutputs s
      · have hai : a ≠ i := by
          intro h
          subst i
          exact ha hi
        simp [hi, hai]
      · simp [hi, ha, PMF.uniformOfFinset_apply]
    simp_rw [hz]
    simp

/-- The probability that the one-step coupling returns different outputs. -/
noncomputable def freshOutputFailure (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) : ℝ :=
  (((freshOutputCoupling s havailable).map fun yz => yz.1 != yz.2) true).toReal

theorem freshOutputFailure_eq (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) :
    freshOutputFailure s havailable =
      (s.usedOutputs.card : ℝ) / Fintype.card X := by
  classical
  rw [freshOutputFailure, freshOutputCoupling, PMF.map_bind]
  have hinner : ∀ y : X,
      (if y ∈ availableOutputs s then PMF.pure (y, y)
        else (PMF.uniformOfFinset (availableOutputs s) havailable).map
          fun z => (y, z)).map (fun yz => yz.1 != yz.2) =
        PMF.pure (decide (y ∉ availableOutputs s)) := by
    intro y
    by_cases hy : y ∈ availableOutputs s
    · simp [hy, PMF.pure_map]
    · simp only [hy, ↓reduceIte, PMF.map_comp]
      apply PMF.ext
      intro b
      cases b with
      | false =>
          simp [PMF.map_apply, PMF.uniformOfFinset_apply, tsum_fintype, hy]
      | true =>
          rw [PMF.map_apply, tsum_fintype]
          have ht : ∀ z : X,
              (@ite ENNReal
                (true = ((fun yz : X × X => yz.1 != yz.2) ∘ fun z => (y, z)) z)
                (Classical.propDecidable _)
                ((PMF.uniformOfFinset (availableOutputs s) havailable) z) 0) =
                if z ∈ availableOutputs s then
                  ((availableOutputs s).card : ENNReal)⁻¹ else 0 := by
            intro z
            by_cases hz : z ∈ availableOutputs s
            · have hyz : y ≠ z := by
                intro h
                subst z
                exact hy hz
              simp [hz, hyz, PMF.uniformOfFinset_apply]
            · simp [hz, PMF.uniformOfFinset_apply]
          rw [show (PMF.pure (decide (¬False)) : PMF Bool) true = 1 by simp]
          calc
            _ = ∑ z : X, if z ∈ availableOutputs s then
                ((availableOutputs s).card : ENNReal)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro z _
              exact ht z
            _ = 1 := by
              rw [Finset.sum_ite]
              simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
                nsmul_eq_mul]
              have hfilter : Finset.univ.filter (fun x => x ∈ availableOutputs s) =
                  availableOutputs s := by
                ext x
                simp
              rw [hfilter]
              apply ENNReal.mul_inv_cancel
              · exact_mod_cast Finset.card_ne_zero.mpr havailable
              · simp
  simp_rw [hinner]
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]
  rw [tsum_fintype]
  simp [availableOutputs, Finset.sum_ite, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv]

/--
Lazy random permutation: reuse a stored answer; for a fresh input sample
uniformly from unused outputs.  The final branch is unreachable while a valid
partial permutation still has an unassigned input, but makes the transition
total and will be ruled out by an invariant.
-/
noncomputable def rpStep : Step X := fun x s =>
  match s.table x with
  | some y => PMF.pure (y, s)
  | none =>
      if h : (availableOutputs s).Nonempty then
        (PMF.uniformOfFinset (availableOutputs s) h).map fun y =>
          (y, store s x y)
      else
        PMF.pure (Classical.choice ‹Nonempty X›, s)

/-- Run an adaptive strategy against a lazy oracle for at most `fuel` queries. -/
noncomputable def runLazy (A : QueryStrategy X X) (step : Step X) :
    ℕ → List X → OracleState X → PMF (Transcript X X × OracleState X)
  | 0, _, s => PMF.pure ([], s)
  | fuel + 1, history, s =>
      match A history with
      | none => PMF.pure ([], s)
      | some x =>
          (step x s).bind fun ys =>
            (runLazy A step fuel (history ++ [ys.1]) ys.2).map fun out =>
              ((x, ys.1) :: out.1, out.2)

noncomputable def lazyRF (A : QueryStrategy X X) (q : ℕ) :
    PMF (Transcript X X × OracleState X) :=
  runLazy A rfStep q [] (initialState X)

noncomputable def lazyRP (A : QueryStrategy X X) (q : ℕ) :
    PMF (Transcript X X × OracleState X) :=
  runLazy A rpStep q [] (initialState X)

/-- Forget the internal lazy-sampling state. -/
noncomputable def visible (p : PMF (Transcript X X × OracleState X)) :
    PMF (Transcript X X) :=
  p.map Prod.fst

@[simp]
theorem runLazy_zero (A : QueryStrategy X X) (step : Step X)
    (history : List X) (s : OracleState X) :
    runLazy A step 0 history s = PMF.pure ([], s) := rfl

/-- Sum of the per-step collision budgets used by the switching proof. -/
noncomputable def collisionBudget (q : ℕ) (N : ℝ) : ℝ :=
  ∑ i ∈ Finset.range q, (i : ℝ) / N

theorem collisionBudget_eq (q : ℕ) {N : ℝ} (hN : N ≠ 0) :
    collisionBudget q N = (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  induction q with
  | zero => simp [collisionBudget]
  | succ q ih =>
      rw [collisionBudget, Finset.sum_range_succ, ← collisionBudget, ih]
      push_cast
      field_simp
      ring

/-- Pointwise per-query bounds add up to the collision budget. -/
theorem sum_le_collisionBudget (q : ℕ) (N : ℝ) (p : ℕ → ℝ)
    (h : ∀ i ∈ Finset.range q, p i ≤ (i : ℝ) / N) :
    ∑ i ∈ Finset.range q, p i ≤ collisionBudget q N := by
  rw [collisionBudget]
  exact Finset.sum_le_sum fun i hi => h i hi

section Coupling

variable {Ω : Type*}

/-- Independent product of two probability mass functions. -/
noncomputable def pmfProduct (p : PMF Α) (q : PMF Β) : PMF (Α × Β) :=
  p.bind fun a => q.map fun b => (a, b)

@[simp]
theorem pmfProduct_map_fst (p : PMF Α) (q : PMF Β) :
    (pmfProduct p q).map Prod.fst = p := by
  rw [pmfProduct, PMF.map_bind]
  have h : ∀ a : Α, (q.map fun b => (a, b)).map Prod.fst = PMF.pure a := by
    intro a
    rw [PMF.map_comp]
    have hc : (Prod.fst ∘ fun b : Β => (a, b)) = Function.const Β a := by
      funext b
      rfl
    rw [hc, PMF.map_const]
  simp_rw [h]
  exact PMF.bind_pure p

@[simp]
theorem pmfProduct_map_snd (p : PMF Α) (q : PMF Β) :
    (pmfProduct p q).map Prod.snd = q := by
  rw [pmfProduct, PMF.map_bind]
  have h : ∀ a : Α, (q.map fun b => (a, b)).map Prod.snd = q := by
    intro a
    rw [PMF.map_comp]
    have hid : (Prod.snd ∘ fun b : Β => (a, b)) = id := by
      funext b
      rfl
    rw [hid, PMF.map_id]
  simp_rw [h]
  exact PMF.bind_const p q

/-- ENNReal-valued mass of a Boolean event. -/
noncomputable def eventMass (p : PMF Α) (event : Α → Bool) : ENNReal :=
  (p.map event) true

theorem freshOutputFailure_mass_eq (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) :
    eventMass (freshOutputCoupling s havailable) (fun yz => yz.1 != yz.2) =
      (s.usedOutputs.card : ENNReal) * (Fintype.card X : ENNReal)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (by simp) (by simp))).mp
  simpa [eventMass, freshOutputFailure, div_eq_mul_inv,
    ENNReal.toReal_mul, ENNReal.toReal_inv] using
      freshOutputFailure_eq s havailable

/-- Union bound for an event observed after a probabilistic bind. -/
theorem eventMass_bind_le (p : PMF Α) (k : Α → PMF Β)
    (event : Β → Bool) (bad : Α → Bool) (c : ENNReal)
    (h : ∀ a, eventMass (k a) event ≤
      (if bad a then 1 else 0) + c) :
    eventMass (p.bind k) event ≤ eventMass p bad + c := by
  rw [eventMass, PMF.map_bind, PMF.bind_apply]
  calc
    (∑' a, p a * ((k a).map event) true) ≤
        ∑' a, p a * ((if bad a then 1 else 0) + c) := by
      apply ENNReal.tsum_le_tsum
      intro a
      gcongr
      exact h a
    _ = (∑' a, p a * (if bad a then 1 else 0)) +
          ∑' a, p a * c := by
      simp_rw [mul_add]
      exact ENNReal.tsum_add
    _ = eventMass p bad + c := by
      rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
      congr 1
      rw [eventMass, PMF.map_apply]
      apply tsum_congr
      intro a
      by_cases ha : bad a = true <;> simp [ha]

/-- Birthday budget starting after at most `i` outputs have been exposed. -/
noncomputable def ennCollisionBudgetFrom (N : ℕ) : ℕ → ℕ → ENNReal
  | _, 0 => 0
  | i, fuel + 1 =>
      (i : ENNReal) * (N : ENNReal)⁻¹ + ennCollisionBudgetFrom N (i + 1) fuel

theorem ennCollisionBudgetFrom_mono_fuel (N i fuel : ℕ) :
    ennCollisionBudgetFrom N i fuel ≤ ennCollisionBudgetFrom N i (fuel + 1) := by
  induction fuel generalizing i with
  | zero => simp [ennCollisionBudgetFrom]
  | succ fuel ih =>
      simp only [ennCollisionBudgetFrom]
      change (i : ENNReal) * (N : ENNReal)⁻¹ +
          ennCollisionBudgetFrom N (i + 1) fuel ≤
        (i : ENNReal) * (N : ENNReal)⁻¹ +
          ennCollisionBudgetFrom N (i + 1) (fuel + 1)
      gcongr
      exact ih (i + 1)

theorem ennCollisionBudgetFrom_ne_top (N i fuel : ℕ) (hN : N ≠ 0) :
    ennCollisionBudgetFrom N i fuel ≠ ⊤ := by
  induction fuel generalizing i with
  | zero => simp [ennCollisionBudgetFrom]
  | succ fuel ih =>
      rw [ennCollisionBudgetFrom]
      exact ENNReal.add_ne_top.mpr ⟨
        ENNReal.mul_ne_top (by simp) (by simp [hN]), ih (i + 1)⟩

/-- Real-valued counterpart of `ennCollisionBudgetFrom`. -/
noncomputable def realCollisionBudgetFrom (N : ℕ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | i, fuel + 1 =>
      (i : ℝ) / (N : ℝ) + realCollisionBudgetFrom N (i + 1) fuel

theorem ennCollisionBudgetFrom_toReal (N i fuel : ℕ) (hN : N ≠ 0) :
    (ennCollisionBudgetFrom N i fuel).toReal =
      realCollisionBudgetFrom N i fuel := by
  induction fuel generalizing i with
  | zero => simp [ennCollisionBudgetFrom, realCollisionBudgetFrom]
  | succ fuel ih =>
      rw [ennCollisionBudgetFrom, realCollisionBudgetFrom,
        ENNReal.toReal_add
          (ENNReal.mul_ne_top (by simp) (by simp [hN]))
          (ennCollisionBudgetFrom_ne_top N (i + 1) fuel hN),
        ENNReal.toReal_mul, ENNReal.toReal_inv (N : ENNReal), ih]
      simp [div_eq_mul_inv]

theorem realCollisionBudgetFrom_eq (N i fuel : ℕ) (hN : N ≠ 0) :
    realCollisionBudgetFrom N i fuel =
      (fuel : ℝ) * (2 * (i : ℝ) + (fuel : ℝ) - 1) /
        (2 * (N : ℝ)) := by
  induction fuel generalizing i with
  | zero => simp [realCollisionBudgetFrom]
  | succ fuel ih =>
      rw [realCollisionBudgetFrom, ih]
      push_cast
      field_simp
      ring

theorem realCollisionBudgetFrom_zero_eq (N q : ℕ) (hN : N ≠ 0) :
    realCollisionBudgetFrom N 0 q = collisionBudget q (N : ℝ) := by
  rw [realCollisionBudgetFrom_eq N 0 q hN,
    collisionBudget_eq q (by exact_mod_cast hN)]
  ring

/-- Add the current query/response pair to a lazy execution result. -/
def prependResult (x y : X) (out : Transcript X X × OracleState X) :
    Transcript X X × OracleState X :=
  ((x, y) :: out.1, out.2)

/-- The observable bad event for a pair of stateful executions. -/
def resultMismatch
    (out : (Transcript X X × OracleState X) ×
      (Transcript X X × OracleState X)) : Bool :=
  out.1.1 != out.2.1

theorem eventMass_map_prepend_same
    (p : PMF ((Transcript X X × OracleState X) ×
      (Transcript X X × OracleState X))) (x y : X) :
    eventMass (p.map fun out =>
      (prependResult x y out.1, prependResult x y out.2)) resultMismatch =
      eventMass p resultMismatch := by
  rw [eventMass, PMF.map_comp]
  have hf : (resultMismatch ∘ fun out =>
      (prependResult x y out.1, prependResult x y out.2)) = resultMismatch := by
    funext out
    simp only [Function.comp_apply, resultMismatch, prependResult]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    simp
  rw [hf]
  rfl

theorem eventMass_map_prepend_ne
    (p : PMF ((Transcript X X × OracleState X) ×
      (Transcript X X × OracleState X))) (x y₁ y₂ : X) (h : y₁ ≠ y₂) :
    eventMass (p.map fun out =>
      (prependResult x y₁ out.1, prependResult x y₂ out.2)) resultMismatch = 1 := by
  rw [eventMass, PMF.map_comp]
  have hc : (resultMismatch ∘ fun out :
      (Transcript X X × OracleState X) × (Transcript X X × OracleState X) =>
      (prependResult x y₁ out.1, prependResult x y₂ out.2)) =
      Function.const _ true := by
    funext out
    simp [resultMismatch, prependResult, h]
  rw [hc, PMF.map_const]
  simp

/--
Global switching coupling, maintained only while both executions agree.

At the first fresh-output disagreement, the remaining RF and RP executions
are sampled independently.  This is what permits an adaptive strategy to ask
different future queries while preserving both exact marginals.
-/
noncomputable def runCoupled (A : QueryStrategy X X) :
    ℕ → List X → OracleState X →
      PMF ((Transcript X X × OracleState X) ×
        (Transcript X X × OracleState X))
  | 0, _, s => PMF.pure (([], s), ([], s))
  | fuel + 1, history, s =>
      match A history with
      | none => PMF.pure (([], s), ([], s))
      | some x =>
          match hx : s.table x with
          | some y =>
              (runCoupled A fuel (history ++ [y]) s).map fun out =>
                (prependResult x y out.1, prependResult x y out.2)
          | none =>
              if havailable : (availableOutputs s).Nonempty then
                (freshOutputCoupling s havailable).bind fun yz =>
                  if hsame : yz.1 = yz.2 then
                    (runCoupled A fuel (history ++ [yz.1])
                      (store s x yz.1)).map fun out =>
                        (prependResult x yz.1 out.1,
                          prependResult x yz.2 out.2)
                  else
                    (pmfProduct
                      (runLazy A rfStep fuel (history ++ [yz.1])
                        (store s x yz.1))
                      (runLazy A rpStep fuel (history ++ [yz.2])
                        (store s x yz.2))).map fun out =>
                          (prependResult x yz.1 out.1,
                            prependResult x yz.2 out.2)
              else
                pmfProduct (runLazy A rfStep (fuel + 1) history s)
                  (runLazy A rpStep (fuel + 1) history s)

theorem map_prepend_pair_fst
    (p : PMF ((Transcript X X × OracleState X) ×
      (Transcript X X × OracleState X))) (x y₁ y₂ : X) :
    (p.map (fun out => (prependResult x y₁ out.1,
      prependResult x y₂ out.2))).map Prod.fst =
      (p.map Prod.fst).map (prependResult x y₁) := by
  rw [PMF.map_comp, PMF.map_comp]
  rfl

theorem map_prepend_pair_snd
    (p : PMF ((Transcript X X × OracleState X) ×
      (Transcript X X × OracleState X))) (x y₁ y₂ : X) :
    (p.map (fun out => (prependResult x y₁ out.1,
      prependResult x y₂ out.2))).map Prod.snd =
      (p.map Prod.snd).map (prependResult x y₂) := by
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- The left marginal of the global coupling is the lazy random function. -/
theorem runCoupled_map_fst (A : QueryStrategy X X) (fuel : ℕ)
    (history : List X) (s : OracleState X) :
    (runCoupled A fuel history s).map Prod.fst =
      runLazy A rfStep fuel history s := by
  induction fuel generalizing history s with
  | zero => simp [runCoupled, runLazy, PMF.pure_map]
  | succ fuel ih =>
      rw [runCoupled, runLazy]
      cases hA : A history with
      | none => simp [hA, runLazy, PMF.pure_map]
      | some x =>
          simp only [hA]
          cases hx : s.table x with
          | some y =>
              simp only [hx, rfStep, PMF.pure_bind]
              rw [map_prepend_pair_fst, ih]
              rfl
          | none =>
              simp only [hx, rfStep]
              split
              · rename_i havailable
                rw [PMF.map_bind]
                have hinner : ∀ yz : X × X,
                    ((if hsame : yz.1 = yz.2 then
                        (runCoupled A fuel (history ++ [yz.1])
                          (store s x yz.1)).map fun out =>
                            (prependResult x yz.1 out.1,
                              prependResult x yz.2 out.2)
                      else
                        (pmfProduct
                          (runLazy A rfStep fuel (history ++ [yz.1])
                            (store s x yz.1))
                          (runLazy A rpStep fuel (history ++ [yz.2])
                            (store s x yz.2))).map fun out =>
                              (prependResult x yz.1 out.1,
                                prependResult x yz.2 out.2))).map Prod.fst =
                      (runLazy A rfStep fuel (history ++ [yz.1])
                        (store s x yz.1)).map (prependResult x yz.1) := by
                  rintro ⟨a, b⟩
                  by_cases hsame : a = b
                  · subst b
                    simp only [dite_true]
                    rw [map_prepend_pair_fst, ih]
                  · simp only [hsame, dite_false]
                    rw [map_prepend_pair_fst, pmfProduct_map_fst]
                simp_rw [hinner]
                rw [PMF.bind_map]
                rw [← freshOutputCoupling_fst s havailable]
                rw [PMF.bind_map]
                rfl
              · exact pmfProduct_map_fst _ _

/-- The right marginal of the global coupling is the lazy random permutation. -/
theorem runCoupled_map_snd (A : QueryStrategy X X) (fuel : ℕ)
    (history : List X) (s : OracleState X) :
    (runCoupled A fuel history s).map Prod.snd =
      runLazy A rpStep fuel history s := by
  induction fuel generalizing history s with
  | zero => simp [runCoupled, runLazy, PMF.pure_map]
  | succ fuel ih =>
      rw [runCoupled, runLazy]
      cases hA : A history with
      | none => simp [hA, runLazy, PMF.pure_map]
      | some x =>
          simp only [hA]
          cases hx : s.table x with
          | some y =>
              simp only [hx, rpStep, PMF.pure_bind]
              rw [map_prepend_pair_snd, ih]
              rw [show runLazy A rpStep (fuel + 1) history s =
                  (runLazy A rpStep fuel (history ++ [y]) s).map
                    (prependResult x y) by
                  simp [runLazy, hA, rpStep, hx, prependResult]
                  rfl]
          | none =>
              simp only [hx, rpStep]
              split
              · rename_i havailable
                rw [PMF.map_bind]
                have hinner : ∀ yz : X × X,
                    ((if hsame : yz.1 = yz.2 then
                        (runCoupled A fuel (history ++ [yz.1])
                          (store s x yz.1)).map fun out =>
                            (prependResult x yz.1 out.1,
                              prependResult x yz.2 out.2)
                      else
                        (pmfProduct
                          (runLazy A rfStep fuel (history ++ [yz.1])
                            (store s x yz.1))
                          (runLazy A rpStep fuel (history ++ [yz.2])
                            (store s x yz.2))).map fun out =>
                              (prependResult x yz.1 out.1,
                                prependResult x yz.2 out.2))).map Prod.snd =
                      (runLazy A rpStep fuel (history ++ [yz.2])
                        (store s x yz.2)).map (prependResult x yz.2) := by
                  rintro ⟨a, b⟩
                  by_cases hsame : a = b
                  · subst b
                    simp only [dite_true]
                    rw [map_prepend_pair_snd, ih]
                  · simp only [hsame, dite_false]
                    rw [map_prepend_pair_snd, pmfProduct_map_snd]
                simp_rw [hinner]
                rw [show runLazy A rpStep (fuel + 1) history s =
                    ((PMF.uniformOfFinset (availableOutputs s) havailable).map
                      fun y => (y, store s x y)).bind fun ys =>
                        (runLazy A rpStep fuel (history ++ [ys.1]) ys.2).map
                          fun out => ((x, ys.1) :: out.1, out.2) by
                    simp [runLazy, hA, rpStep, hx, havailable]]
                rw [PMF.bind_map]
                rw [← freshOutputCoupling_snd s havailable]
                rw [PMF.bind_map]
                rfl
              · exact pmfProduct_map_snd _ _

/-- The global bad-event probability is bounded by the remaining birthday budget. -/
theorem runCoupled_failureMass_le (A : QueryStrategy X X)
    (fuel i : ℕ) (history : List X) (s : OracleState X)
    (hcard : s.usedOutputs.card ≤ i)
    (hcap : i + fuel ≤ Fintype.card X) :
    eventMass (runCoupled A fuel history s) resultMismatch ≤
      ennCollisionBudgetFrom (Fintype.card X) i fuel := by
  induction fuel generalizing i history s with
  | zero => simp [runCoupled, eventMass, resultMismatch,
      ennCollisionBudgetFrom, PMF.pure_map]
  | succ fuel ih =>
      rw [runCoupled]
      cases hA : A history with
      | none => simp [hA, eventMass, resultMismatch,
          ennCollisionBudgetFrom, PMF.pure_map]
      | some x =>
          simp only [hA]
          cases hx : s.table x with
          | some y =>
              rw [eventMass_map_prepend_same]
              exact le_trans
                (ih i (history ++ [y]) s hcard (by omega))
                (ennCollisionBudgetFrom_mono_fuel (Fintype.card X) i fuel)
          | none =>
              have hlt : s.usedOutputs.card < Fintype.card X := by
                exact lt_of_le_of_lt hcard (by omega)
              have havailable : (availableOutputs s).Nonempty :=
                availableOutputs_nonempty_of_card_lt s hlt
              simp only [hx, havailable, dite_true]
              let c := ennCollisionBudgetFrom (Fintype.card X) (i + 1) fuel
              have hkernel : ∀ yz : X × X,
                  eventMass
                    (if hsame : yz.1 = yz.2 then
                      (runCoupled A fuel (history ++ [yz.1])
                        (store s x yz.1)).map fun out =>
                          (prependResult x yz.1 out.1,
                            prependResult x yz.2 out.2)
                    else
                      (pmfProduct
                        (runLazy A rfStep fuel (history ++ [yz.1])
                          (store s x yz.1))
                        (runLazy A rpStep fuel (history ++ [yz.2])
                          (store s x yz.2))).map fun out =>
                            (prependResult x yz.1 out.1,
                              prependResult x yz.2 out.2))
                    resultMismatch ≤
                    (if yz.1 != yz.2 then 1 else 0) + c := by
                rintro ⟨a, b⟩
                by_cases hab : a = b
                · subst b
                  simp only [dite_true]
                  rw [eventMass_map_prepend_same]
                  have hs : (store s x a).usedOutputs.card ≤ i + 1 := by
                    exact le_trans (store_used_card_le_succ s x a)
                      (Nat.add_le_add_right hcard 1)
                  have hi := ih (i + 1) (history ++ [a]) (store s x a) hs (by omega)
                  simpa [c] using hi
                · simp only [hab, dite_false]
                  rw [eventMass_map_prepend_ne _ x a b hab]
                  simp [hab]
              refine le_trans
                (eventMass_bind_le (freshOutputCoupling s havailable) _
                  resultMismatch (fun yz => yz.1 != yz.2) c hkernel) ?_
              rw [freshOutputFailure_mass_eq]
              simp only [ennCollisionBudgetFrom, c]
              gcongr

/-- A joint distribution with prescribed left and right marginals. -/
structure Coupling (left right : PMF Ω) where
  joint : PMF (Ω × Ω)
  map_fst : joint.map Prod.fst = left
  map_snd : joint.map Prod.snd = right

/-- Push a coupling through the same observation on both sides. -/
noncomputable def Coupling.map {left right : PMF Ω} (c : Coupling left right)
    (f : Ω → Γ) : Coupling (left.map f) (right.map f) where
  joint := c.joint.map fun z => (f z.1, f z.2)
  map_fst := by
    rw [PMF.map_comp]
    have hf : (Prod.fst ∘ fun z : Ω × Ω => (f z.1, f z.2)) =
        f ∘ Prod.fst := by funext z; rfl
    rw [hf, ← PMF.map_comp, c.map_fst]
  map_snd := by
    rw [PMF.map_comp]
    have hf : (Prod.snd ∘ fun z : Ω × Ω => (f z.1, f z.2)) =
        f ∘ Prod.snd := by funext z; rfl
    rw [hf, ← PMF.map_comp, c.map_snd]

/-- The global runner packaged as a coupling of the stateful lazy games. -/
noncomputable def lazyStateCoupling (A : QueryStrategy X X) (q : ℕ) :
    Coupling (lazyRF A q) (lazyRP A q) where
  joint := runCoupled A q [] (initialState X)
  map_fst := runCoupled_map_fst A q [] (initialState X)
  map_snd := runCoupled_map_snd A q [] (initialState X)

/-- Coupling of the externally visible RF and RP transcripts. -/
noncomputable def lazyTranscriptCoupling (A : QueryStrategy X X) (q : ℕ) :
    Coupling (visible (lazyRF A q)) (visible (lazyRP A q)) :=
  (lazyStateCoupling A q).map Prod.fst

@[simp]
theorem lazyTranscriptCoupling_joint (A : QueryStrategy X X) (q : ℕ) :
    (lazyTranscriptCoupling A q).joint =
      (runCoupled A q [] (initialState X)).map
        (fun z => (z.1.1, z.2.1)) := rfl

/-- The fresh-output construction, packaged as an actual coupling. -/
noncomputable def freshOutputAsCoupling (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) :
    Coupling (PMF.uniformOfFintype X)
      (PMF.uniformOfFinset (availableOutputs s) havailable) where
  joint := freshOutputCoupling s havailable
  map_fst := freshOutputCoupling_fst s havailable
  map_snd := freshOutputCoupling_snd s havailable

/-- Its disagreement probability is exactly the occupied fraction of the range. -/
theorem freshOutputAsCoupling_failure_eq (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) :
    (((freshOutputAsCoupling s havailable).joint.map
      fun yz => yz.1 != yz.2) true).toReal =
      (s.usedOutputs.card : ℝ) / Fintype.card X := by
  exact freshOutputFailure_eq s havailable

/-- A convenient indexed upper bound for the per-query coupling failure. -/
theorem freshOutputFailure_le (s : OracleState X)
    (havailable : (availableOutputs s).Nonempty) {i : ℕ}
    (hcard : s.usedOutputs.card ≤ i) :
    freshOutputFailure s havailable ≤ (i : ℝ) / Fintype.card X := by
  rw [freshOutputFailure_eq]
  gcongr

/-- Probability that the two components of a coupling disagree. -/
noncomputable def Coupling.decisionFailure {left right : PMF Ω}
    (c : Coupling left right) (decision : Ω → Bool) : ℝ :=
  ((c.joint.map fun z => decision z.1 != decision z.2) true).toReal

/-- Probability that the coupled outcomes themselves disagree. -/
noncomputable def Coupling.fullFailure [DecidableEq Ω] {left right : PMF Ω}
    (c : Coupling left right) : ℝ :=
  ((c.joint.map fun z => z.1 != z.2) true).toReal

/-- Applying a decision function cannot create disagreement from equal outcomes. -/
theorem Coupling.decisionFailure_le_fullFailure [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) :
    c.decisionFailure decision ≤ c.fullFailure := by
  have htop : (c.joint.map (fun z => z.1 != z.2)) true ≠ ⊤ :=
    PMF.apply_ne_top _ _
  rw [Coupling.decisionFailure, Coupling.fullFailure, PMF.map_apply, PMF.map_apply]
  apply ENNReal.toReal_mono
  · simpa only [PMF.map_apply] using htop
  · apply ENNReal.tsum_le_tsum
    intro z
    rcases z with ⟨a, b⟩
    by_cases hz : a = b
    · subst b
      simp
    · by_cases hd : decision a = decision b <;> simp [hz, hd]

/--
The fundamental coupling inequality specialized to Boolean distinguishers:
the distinguishing advantage is at most the coupling's failure probability.
-/
theorem advantage_le_coupling_failure [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) :
    advantage left right decision ≤ c.decisionFailure decision := by
  let j : PMF (Bool × Bool) := c.joint.map fun z => (decision z.1, decision z.2)
  have hleft : left.map decision = j.map Prod.fst := by
    rw [← c.map_fst, PMF.map_comp, PMF.map_comp]
    rfl
  have hright : right.map decision = j.map Prod.snd := by
    rw [← c.map_snd, PMF.map_comp, PMF.map_comp]
    rfl
  have hfail : c.decisionFailure decision =
      (j (true, false)).toReal + (j (false, true)).toReal := by
    rw [Coupling.decisionFailure]
    have hmap : c.joint.map (fun z => decision z.1 != decision z.2) =
        j.map (fun z => z.1 != z.2) := by
      simp only [j, PMF.map_comp]
      rfl
    rw [hmap, PMF.map_apply]
    rw [tsum_fintype]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_bool]
    simp only [Fintype.sum_bool]
    norm_num
    rw [ENNReal.toReal_add (j.apply_ne_top _) (j.apply_ne_top _)]
  have hleftProb : eventProbability left decision =
      (j (true, true)).toReal + (j (true, false)).toReal := by
    rw [eventProbability, hleft, PMF.map_apply]
    rw [tsum_fintype]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true, add_zero]
    rw [ENNReal.toReal_add (j.apply_ne_top _) (j.apply_ne_top _)]
  have hrightProb : eventProbability right decision =
      (j (true, true)).toReal + (j (false, true)).toReal := by
    rw [eventProbability, hright, PMF.map_apply]
    rw [tsum_fintype]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true, zero_add]
    simp only [add_zero, zero_add]
    rw [ENNReal.toReal_add (j.apply_ne_top _) (j.apply_ne_top _)]
  rw [advantage, hleftProb, hrightProb, hfail]
  have h₁ : 0 ≤ (j (true, false)).toReal := ENNReal.toReal_nonneg
  have h₂ : 0 ≤ (j (false, true)).toReal := ENNReal.toReal_nonneg
  rw [add_sub_add_left_eq_sub]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The standard identical-until-bad wrapper used by the switching game hop. -/
theorem advantage_le_coupling_fullFailure [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) :
    advantage left right decision ≤ c.fullFailure :=
  le_trans (advantage_le_coupling_failure c decision)
    (c.decisionFailure_le_fullFailure decision)

/-- Every lazy RF/RP distinguisher is bounded by the global coupling's bad event. -/
theorem lazy_advantage_le_bad (A : QueryStrategy X X) (q : ℕ)
    (decision : Transcript X X → Bool) :
    advantage (visible (lazyRF A q)) (visible (lazyRP A q)) decision ≤
      (lazyTranscriptCoupling A q).fullFailure :=
  advantage_le_coupling_fullFailure (lazyTranscriptCoupling A q) decision

@[simp]
theorem lazyTranscriptCoupling_fullFailure_zero (A : QueryStrategy X X) :
    (lazyTranscriptCoupling A 0).fullFailure = 0 := by
  simp [Coupling.fullFailure, lazyTranscriptCoupling, lazyStateCoupling,
    Coupling.map, runCoupled, visible, lazyRF, lazyRP, PMF.pure_map]

theorem lazyTranscriptCoupling_fullFailure_eq (A : QueryStrategy X X) (q : ℕ) :
    (lazyTranscriptCoupling A q).fullFailure =
      (eventMass (runCoupled A q [] (initialState X)) resultMismatch).toReal := by
  rw [Coupling.fullFailure, lazyTranscriptCoupling_joint]
  unfold eventMass resultMismatch
  rw [PMF.map_comp]
  apply congrArg (fun p : PMF Bool => (p true).toReal)
  apply congrArg (fun f => (runCoupled A q [] (initialState X)).map f)
  funext out
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, bne_iff_ne]

theorem lazyTranscriptCoupling_fullFailure_le (A : QueryStrategy X X) (q : ℕ)
    (hq : q ≤ Fintype.card X) :
    (lazyTranscriptCoupling A q).fullFailure ≤
      collisionBudget q (Fintype.card X : ℝ) := by
  rw [lazyTranscriptCoupling_fullFailure_eq]
  have hmass := runCoupled_failureMass_le A q 0 [] (initialState X)
    (by simp) (by simpa using hq)
  refine le_trans
    (ENNReal.toReal_mono
      (ennCollisionBudgetFrom_ne_top (Fintype.card X) 0 q Fintype.card_ne_zero)
      hmass) ?_
  rw [ennCollisionBudgetFrom_toReal _ _ _ Fintype.card_ne_zero,
    realCollisionBudgetFrom_zero_eq _ _ Fintype.card_ne_zero]

/-- Lazy-sampling PRP/PRF switching lemma for the nontrivial range `q ≤ |X|`. -/
theorem lazy_switching_bound (A : QueryStrategy X X) (q : ℕ)
    (hq : q ≤ Fintype.card X) (decision : Transcript X X → Bool) :
    advantage (visible (lazyRF A q)) (visible (lazyRP A q)) decision ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  calc
    advantage (visible (lazyRF A q)) (visible (lazyRP A q)) decision ≤
        (lazyTranscriptCoupling A q).fullFailure :=
      lazy_advantage_le_bad A q decision
    _ ≤ collisionBudget q (Fintype.card X : ℝ) :=
      lazyTranscriptCoupling_fullFailure_le A q hq
    _ = (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
      apply collisionBudget_eq
      exact_mod_cast Fintype.card_ne_zero

theorem Coupling.fullFailure_le_one [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right) : c.fullFailure ≤ 1 := by
  rw [Coupling.fullFailure]
  have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
    (PMF.coe_le_one (c.joint.map fun z => z.1 != z.2) true)
  simpa using h

/-- Lazy-sampling switching bound for every query count. -/
theorem lazy_switching_bound_all (A : QueryStrategy X X) (q : ℕ)
    (decision : Transcript X X → Bool) :
    advantage (visible (lazyRF A q)) (visible (lazyRP A q)) decision ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  by_cases hq : q ≤ Fintype.card X
  · exact lazy_switching_bound A q hq decision
  · have hbad : advantage (visible (lazyRF A q)) (visible (lazyRP A q)) decision ≤ 1 :=
      le_trans (lazy_advantage_le_bad A q decision)
        (Coupling.fullFailure_le_one (lazyTranscriptCoupling A q))
    have hNnat : 0 < Fintype.card X := Fintype.card_pos
    have hqnat : Fintype.card X + 1 ≤ q := by omega
    have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast hNnat
    have hN1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hNnat
    have hqreal : (Fintype.card X : ℝ) + 1 ≤ q := by exact_mod_cast hqnat
    have hone : (1 : ℝ) ≤
        (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card X)).2
      have hq2 : (2 : ℝ) ≤ q := by nlinarith
      have hminus : (Fintype.card X : ℝ) ≤ (q : ℝ) - 1 := by nlinarith
      have hprod := mul_le_mul hq2 hminus (le_of_lt hN)
        (by positivity : (0 : ℝ) ≤ q)
      nlinarith
    exact le_trans hbad hone

end Coupling

end PRPPRFSwitching.Lazy
