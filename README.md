# BB(5) Decimal Macro-Grammar

This repository contains a structural macro-analysis of the 
Marxen–Buntrock BB(5) step champion (47,176,870 steps).

## Core Ideas

- Decimal encoding of state-symbol trace
- Oscillator blocks (159^M)
- Layer termination via (K, K+2)
- Gate bifurcation (lead02 vs lead14)
- Ones-on-tape invariant

## Verified Results

Full run verified:
47,176,870 steps — halting confirmed.

Layer sequence (M):
1, 3, 6, 12, 22, 39, 66, 112, 189, 316, 529, 883, 1473, 2456, 4095

## Formal Proof (Coq)

The layer grammar is now **proved in Coq**, not only checked by simulation.
See [`coq/`](coq/) — the main theorem `bb5_decimal_trace` states that the
full decimal trace is exactly `0246` followed by the layer grammar.

Proved for every layer size: the oscillator block `(159)^M`, the rung law
(B = A+1 inside, B = A+2 at the end, steps of 5), the two gates, the gate law
((K+2) mod 3: 0 → Gate 1, 1 → Gate 2, 2 → halt), the recurrence
M(n+1) = ⌊(K+2)/3⌋ + 1, and halting after 15 layers.

## Scripts

- [`scripts/verify_gate_law.py`](scripts/verify_gate_law.py) — runs all
  47,176,870 steps and checks the gate law, the ones law
  (3M+g ones before each Ω block, M+g after) and the recurrence,
  reading everything from the trace itself.

## Status

Layer grammar formally proved in Coq.
Still to formalize: the exact step count and ones count.