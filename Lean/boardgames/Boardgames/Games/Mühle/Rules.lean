abbrev Pos := Fin 24

def adjacent (a b : Pos) : Bool :=
  let (ra, ka, rb, kb) := (a.val / 8, a.val % 8, b.val / 8, b.val % 8)
  (ra == rb && ((ka + 1) % 8 == kb || (kb + 1) % 8 == ka)) ||
  (ka == kb && ka % 2 == 1 && (ra + 1 == rb || rb + 1 == ra))

def mills : List (Pos × Pos × Pos) :=
  [(0,1,2),(2,3,4),(4,5,6),(6,7,0), (8,9,10),(10,11,12),(12,13,14),(14,15,8),
   (16,17,18),(18,19,20),(20,21,22),(22,23,16), (1,9,17),(3,11,19),(5,13,21),(7,15,23)]
example : mills.length = 16 := by decide

inductive Player | white | black  deriving DecidableEq, Repr
inductive Move | place (q : Pos) | slide (a b : Pos) | jump (a b : Pos) | remove (q : Pos)

structure State where
  board      : Pos → Option Player
  hand       : Player → Nat
  turn       : Player
  mustRemove : Bool

def State.RuleLegal (s : State) : Move → Prop
  | .place q  => s.mustRemove = false ∧ 0 < s.hand s.turn ∧ s.board q = none
  | .remove q => s.mustRemove = true ∧ s.board q = some s.turn.other ∧
                 (¬ inMill s.board q ∨ ∀ r, s.board r = some s.turn.other → inMill s.board r)
  | _ => sorry   -- slide/jump analog | on_board = 3 trennt die beiden

def State.Legal (s : State) (m : Move) : Prop := s.outcome = .ongoing ∧ s.RuleLegal m
