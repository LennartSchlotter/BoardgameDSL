inductive Outcome (P: Type) | win(p : P) | draw | Outcome.ongoing

structure Game where
  State   : Type
  Move    : Type
  Player  : Type
  init    : State
  toMove  : State → Player
  legal   : State → Move → Prop
  apply   : State → Move → State
  outcome : State → Outcome Player

inductive Reachable (g : Game) : g.State → Prop
  | init : Reachable g g.init
  | step {s m} : Reachable g s → g.legal s m → Reachable g (g.apply s m)

theorem Game.invariant (g : Game) (P : g.State → Prop)
    (h0 : P g.init) (hs : ∀ s m, P s → g.legal s m → P (g.apply s m)) :
    ∀ s, Reachable g s → P s := by
  intro s h
  induction h with
  | init => exact h0
  | step _ hl ih => exact hs _ _ ih hl
