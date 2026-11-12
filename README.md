# BB(5) Decimal Macro-Grammar

This repository contains a structural macro-analysis of the 
Marxen–Buntrock BB(5) step champion (47,176,870 steps).

The champion's high-level Collatz-like rule is due to Buro (1990) and
Michel (1993). This work describes the champion's full transcript at the
level of single steps, and proves that description in Coq.

## Paper

**A Proved Transcript Grammar for the BB(5) Champion** — Vishnu Vaidyanathan, November 2026.

- SSRN: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6520560
- PDF and LaTeX source: [`Paper/v4/`](Paper/v4/)

## Core Ideas

- Decimal encoding of state-symbol trace
- Oscillator blocks (159^M)
- Layer termination via (K, K+2)
- Gate bifurcation (02 vs 1)
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

## BB(6)

The same transcript method applied to the BB(6) champion gives exact step
counts for every move of the machine, proved in Coq. See [`bb6/`](bb6/).
The tape rules there are the work of mxdys; this repo adds the step counts.

## BB(7)

The same method on the claimed BB(7) champion: a grammar that writes its
digits without running the machine, and a Coq proof of its one move and of
the halting gate. See [`bb7/`](bb7/). The machine is due to Jeff Ketchersid;
its bound is not verified here.

Work in progress: `bb7/design/` has notes and code for designing a BB(7)
machine from parts (loop, fuel, gate, restart). See `bb7/design/README.md`.
