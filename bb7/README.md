# Claimed BB(7) champion: a transcript grammar, and a Coq proof of its move

Machine (found by Jeff Ketchersid, October 2026; the BusyBeaverWiki lists its
bound as not independently verified):

    1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB

This folder does **not** verify the claimed bound and does **not** prove that
the machine halts. It describes what the run is made of, and proves the pieces.

## In short

One digit per step (`2*state + symbol`, written `0-9` then `a b c d`).
After a fixed start of 319 digits the run is one move, repeated:

    1^P 0^(2j) 1^Z ...   becomes   (1100)^(j-1) 1^(3P+8-2j) 00 1^(Z-2) ...

- Gap of 2 (`j = 1`): `P` becomes `3P + 6`. This is the tripling.
- Larger gap: new `1100` units appear in front and the old `P` becomes a counter.
- When a block is used up, two gaps join, and the growth goes up one level.
- **The gate.** When the block is a single `1`: `P` even halts; `P` odd (and
  the `1` is the last cell) restarts with `(3P-1)/2` fresh units. The real run
  meets the gate once with `P = 13` (restart, 19 units). After that everything
  stays even, so the next single `1`, the last cell of the tape, is the halt.

The notes ([`bb7_grammar_notes.pdf`](bb7_grammar_notes.pdf)) give the words,
the rule, the tests and the open questions.

## Files

| File | What it is |
| --- | --- |
| `bb7_grammar.py` | Writes the digits from the grammar alone. `python3 bb7_grammar.py 100000` prints digits; add `--check` to compare with the machine. |
| `BB7Moves.v` | Coq 8.18, no axioms, about 3 seconds. |
| `bb7_grammar_notes.pdf`, `.tex` | Working notes. |

## Tested (not proofs)

- The grammar equals the machine on the first 60,000,000 digits.
- Single moves, `P = 2..15` odd and even, gaps 2 to 12: 756 of 756 match.
- Complete small runs to the halt: 169 of 169 identical.

## Proved in Coq (`BB7Moves.v`)

| Name | Statement |
| --- | --- |
| `move` | The move above, for all `P`, `j >= 1`, `Z >= 2`, whenever `m = 3P + 3 - 2j >= 1` |
| `wcost_closed` | It takes exactly `3P² + 27P + 44 + 2j + (2j-1)(2m + 2j + 8)` steps |
| `triple` | `j = 1`: `P -> 3P + 6` in `3P² + 33P + 58` steps |
| `chain`, `tri_closed` | `n` triplings in a row; `P` ends as `(P+3)·3^n - 3` |
| `halts_gen` | The gate: `P` even and a single last `1` halts the machine |
| `start` | Blank tape to the clean shape at step 3,954 (`P = 16`, 19 units) |
| `at_5656` | The tape at step 5,656 (`P = 12`, counter 50) |
| `tripling_chain` | After 25 triplings: `P = 15·3^25 - 3`, gap 6, 18 units left |

The step in `tripling_chain` is `5656 + chcost 25 12`, which is
60,572,642,711,595,382,146,057,206 (computed outside Coq from the same formula).

## Not proved

- That the run stays inside the rule (`m >= 1`) until the end. Without this
  there is no proof of halting and no exact halting time.
- The restart for general odd `P`.
- The digit strings themselves (the step counts equal their lengths).
- The claimed bound.

## Next: designing a machine from parts

`design/` holds working notes and search code for building a BB(7) machine
part by part (loop, fuel, gate, restart) instead of searching whole tables.
Start with `design/README.md`. No bigger machine has been found yet; the best
designed machine so far is predicted to halt after about 5.5 × 10^328 steps
(not proved, and tiny next to the claimed champion).
