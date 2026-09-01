import LeanTestproj
import Mathlib


abbrev tstar (T: Type) : Type := List T

abbrev tplus (T: Type) : Type := T × List T

namespace TPlus

  def last {T: Type} (x : tplus T) : T :=
    List.getLast (Prod.fst x :: Prod.snd x) (by simp)

  def of_star {T: Type} (x: tstar T) : x ≠ [] → tplus T :=
    match x with
    | [] => fun _ => by contradiction
    | h :: t => fun _ => (h, t)

  def to_star (x: tplus T) : tstar T :=
    match x with | (h, t) => h :: t

end TPlus


section
  -- variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

  abbrev RS (X Y: Type): Type := tplus X → Y
  -- do we only consider stateless ftns? otherwise PD may be complex
  abbrev PD_SRS (X Y: Type): Type := PMF (X → Y)

  def stateless (S: RS X Y) : Prop :=
    ∃ (f: X → Y), ∀ xi : tplus X, S xi = f (TPlus.last xi)

  def SRS : Set (RS X Y) := { S | stateless S}

  -- query functions

  -- using PFun

  def prefix_closed (Q: tstar Y →. X) : Prop :=
    ∀ y : tstar Y, (Q y).Dom → ∀ a, a <+: y → (Q a).Dom

  def QFb (X Y: Type) : Set (tstar Y →. X) :=
    { Q | prefix_closed Q }

  section

    variable (q: ℕ) (Q: tstar Y →. X)

    def q_tractable : Prop :=
      ∀ y : tstar Y, (Q y).Dom -> List.length y < q

    def q_intractable : Prop := ¬ q_tractable q Q

    -- what if |y|=|z| but only Q(y) exists?
    def non_adaptive : Prop :=
      ∀ y z (D1: (Q y).Dom) (D2: (Q z).Dom),
      List.length y = List.length z → (Q y).get D1 = (Q z).get D2

  end

  def QF (q: ℕ) (X Y: Type) : Set (tstar Y →. X) :=
    { Q | Q ∈ QFb X Y ∧ q_tractable q Q }

  def NQF (q: ℕ) (X Y: Type) : Set (tstar Y →. X) :=
    { Q | Q ∈ QF q X Y ∧ non_adaptive Q }

  -- def transc_i (q: ℕ) (Q: tstar Y →. X) (S: tplus X → Y) (acc: List (X × Y))
  --   : List (X × Y) :=
  --   match q with
  --   | Nat.zero => acc
  --   | Nat.succ q' =>
  --     Q (map snd acc)


  -- def transc (q: ℕ) (Q: _) (HQF: Q ∈ QF q X Y) (S: RS X Y): List (X × Y) :=
  --   let xi := S yi in
  --   let yi := Q (.., xi) in
  --   transc


  -- def pmf_SRS : Type := PMF (↥ (SRS X Y))

-- set_option trace.Meta.synthInstance true in
--   #check PMF.uniformOfFintype (X → Y)
-- #check PMF.uniformOfFintype (X → Y)

end

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
