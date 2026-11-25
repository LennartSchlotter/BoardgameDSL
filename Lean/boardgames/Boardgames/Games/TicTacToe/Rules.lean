inductive Player | X | O
  deriving DecidableEq, Repr

def Player.other : Player → Player
  | .X => .O
  | .O => .X

abbrev Board := Fin 9 → Option Player

structure State where
  board : Board
  turn  : Player

def State.init : State := { board := fun _ => none, turn := .X }

def lines : List (Fin 9 × Fin 9 × Fin 9) :=
  [(0,1,2), (3,4,5), (6,7,8), (0,3,6), (1,4,7), (2,5,8), (0,4,8), (2,4,6)]

def hasLine (b : Board) (p : Player) : Bool :=
  lines.any fun (a, c, d) => decide (b a = some p ∧ b c = some p ∧ b d = some p)

def full (b : Board) : Bool :=
  decide (∀ i : Fin 9, (b i).isSome = true)

inductive Outcome | win (p : Player) | draw | ongoing
  deriving DecidableEq

def State.outcome (s : State) : Outcome :=
  if hasLine s.board .X then .win .X
  else if hasLine s.board .O then .win .O
  else if full s.board then .draw
  else .ongoing

def State.Legal (s : State) (i : Fin 9) : Prop :=
  s.outcome = .ongoing ∧ s.board i = none

def State.apply (s : State) (i : Fin 9) : State :=
  { board := fun j => if j = i then some s.turn else s.board j
    turn  := s.turn.other }

inductive Reachable : State → Prop
  | init : Reachable State.init
  | step {s : State} {i : Fin 9} : Reachable s → s.Legal i → Reachable (s.apply i)

/--
Making a move updates the square to the current player's mark
-/
theorem apply_sets (s : State) (i : Fin 9) :
    (s.apply i).board i = some s.turn := by simp [State.apply]

/-
If a position's outcome is "ongoing" then neither player has completed a line on the board
-/
theorem outcome_ongoing {s : State} (h : s.outcome = .ongoing) :
    hasLine s.board .X = false ∧ hasLine s.board .O = false := by
  unfold State.outcome at h --unfold the abstract State.outcome by its concrete definition
  split at h -- case analysis on the conditionals / match that appear in h
  · simp_all
  · split at h
    · simp_all
    · simp_all

/-
Placing a player in an empty or occupied board position cannot destroy an existing winning line for another player
-/
theorem hasLine_set {b : Board} {i : Fin 9} {p q : Player} (hne : p ≠ q) :
    hasLine (fun j => if j = i then some p else b j) q = true →
    hasLine b q = true := by
  intro h
  simp only [hasLine, List.any_eq_true, decide_eq_true_eq] at h ⊢ -- Unfold hasLine
  obtain ⟨⟨a, c, d⟩, hmem, ha, hc, hd⟩ := h --Extracts the winning line
  refine ⟨(a, c, d), hmem, ?_, ?_, ?_⟩ --Proposes the exact same winning line for the original board
  · by_cases h : a = i
    · simp [h] at ha
      exact absurd ha hne
    · simpa [h] using ha
  · by_cases h : c = i
    · simp [h] at hc
      exact absurd hc hne
    · simpa [h] using hc
  · by_cases h : d = i
    · simp [h] at hd
      exact absurd hd hne
    · simpa [h] using hd

/-
Only one player can win
-/
theorem not_both_win {s : State} (h : Reachable s) :
    ¬ (hasLine s.board .X = true ∧ hasLine s.board .O = true) := by
  cases h with -- splits reachable into its two constructors
  | init => simp [State.init, hasLine, lines] --Base case, unfolding the init/hasLine/lines and closes the goal as no lines
  | @step s' i _ hl => --inductive step, a move from a prior reachable state leads to the current state
    obtain ⟨hx, ho⟩ := outcome_ongoing hl.1
    rintro ⟨hx', ho'⟩
    cases ht : s'.turn
    · have := hasLine_set (b := s'.board) (p := .X) (q := .O) (by decide)
        (by simpa [State.apply, ht] using ho')
      simp_all
    · have := hasLine_set (b := s'.board) (p := .O) (q := .X) (by decide)
        (by simpa [State.apply, ht] using hx')
      simp_all
