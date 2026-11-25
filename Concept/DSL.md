# Tic Tac Toe
```
game TicTacToe
  players: X, O, abwechselnd
  board:   grid(3,3) -- Positionen, Nachbarschaft, lines(3) aus dem Konstruktor
  rule place(p):
    pre: empty(p)
    do: put(me, p)
    trace: Place(me, p)
  end: win(me) when line(3, me);  draw when board_full
end
check:
  ∀ trace: length ≤ 9
  ∀ trace: nie gewinnen beide
```

# Mühle
```
game Mühle
  players: Weiß, Schwarz, abwechselnd
  board: rings(3)
  state: hand(p) = 9,  control ∈ {play, must_remove}

  rule place(q):
    pre: control = play, hand(me) > 0, empty(q)
    do: put(me, q); hand(me) -= 1; if forms_line(q) then control := must_remove
    trace: Place(me, q)
  rule slide(a, b):
    pre: control = play, hand(me) = 0, on_board(me) > 3, mine(a), empty(b), adjacent(a, b)
    do: move(a, b);  if forms_line(b) then control := must_remove
    trace: Slide(me, a, b)
  rule jump(a, b): -- wie slide, aber on_board(me) = 3, ohne adjacent
  rule remove(q):
    pre: control = must_remove, theirs(q), (not in_line(q) or all_in_line(them))
    do: delete(q); control := play
    trace: Remove(me, q)

  next player: Gegner, außer control = must_remove
  end: lose(me) when on_board(me) + hand(me) < 3 or (control = play and no legal move)
end
check:
  ∀ trace: auf Place/Slide/Jump mit Mühle folgt unmittelbar Remove desselben Spielers
  ∃ trace: beliebig lang -- Existenzaussage: erwartet Nicht-Terminierung
```

# Mensch Ärgere Dich Nicht
```
game MÄDN
  players: 4, reihum
  board: ring(40); je Spieler haus(4), ziel(4); start(p) = Ringfeld 10·Nr(p)
  state: roll ∈ {none, 1..6}

  chance roll_die:
    pre: roll = none
    do: roll := random(1..6)
    trace: Roll(me, roll)
  rule enter(c):
    pre: roll = 6, c ∈ haus(me), not mine(start(me))
    do: put(c, start(me)), fremde Figur dort ins Haus schlagen
    trace: Enter(me, c)
  rule advance(c):
    pre: roll ≠ none, c auf Ring/Ziel, Ziel = c + roll erreichbar und nicht eigene Figur
    do: move(c, c + roll), ggf. schlagen
    trace: Advance(me, c, roll)
  rule pass:
    pre: roll ≠ none, keine andere Regel anwendbar
    trace: Pass(me)

  after enter | advance | pass:  roll := none;  Zugrecht bleibt bei me, wenn roll vorher 6 war
  priority (Variante "streng"): enter > Startfeld räumen > schlagen > frei
end
check:
  ∀ trace: nie zwei Figuren auf einem Ringfeld          -- Sicherheit, für jede Würfelfolge
  terminiert, falls jeder Wurfwert immer wiederkehrt      -- mit Fairness-Annahme
```
