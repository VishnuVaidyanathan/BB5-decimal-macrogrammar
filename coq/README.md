# Coq proof of the BB(5) decimal macro-grammar

`BB5Omega.v` proves, in Coq (checked with Coq 8.18, Rocq-compatible),
that the decimal trace of the Marxen–Buntrock BB(5) champion

    1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA

is exactly the layer grammar described in the paper. No axioms are used
(`Print Assumptions bb5_decimal_trace` reports "Closed under the global context").

Digit map: digit = 2 * state_index + symbol (A0=0, A1=1, ..., E1=9).

## Main results

| Coq name | What it proves |
| --- | --- |
| `omega_block`, `omega_block_tr` | M copies of Ω turn 3M ones into M copies of `001`; digits `(159)^M` |
| `rung`, `rung_tr` | internal rung `4·7^(n+2)·60·3^(n+3)·2` (B = A+1), block grows by 5 |
| `ladder`, `ladder_tr` | r rungs grow the block by exactly 5r |
| `terminal_rung`, `terminal_rung_tr` | terminal rung `4·7^(n+2)·60·3^(n+4)·2` (B = A+2) |
| `layer_gate1_tr`, `layer_gate2_tr`, `layer_halt_tr` | full layers as digit strings: Gate 1 (`02`), Gate 2 (`1`), halt (`158`) |
| `layer_correct_tr` | every layer follows the layer map `next_layer` |
| `gate_law` | next gate is set by (K+2) mod 3: 0 → Gate 1, 1 → Gate 2, 2 → halt |
| `recurrence_8_1` | M(n+1) = ⌊(K+2)/3⌋ + 1 |
| `M_sequence` | M = 1, 3, 6, 12, 22, 39, 66, 112, 189, 316, 529, 883, 1473, 2456, 4095 |
| `bb5_champion_halts` | from a blank tape the machine halts (after 15 layers) |
| `bb5_decimal_trace` | **the whole decimal trace is exactly `0246` followed by the layer grammar** |
| `bb5_steps_from_grammar` | the number of steps is 4 + the length of the grammar |

## Check it yourself

    coqc BB5Omega.v

## Not yet in Coq

- The step count 47,176,870, the 4,098 ones and the halt position
  (they follow from the step formulas in the file, but need binary numbers in Coq).
- The observation "Gate 1 ⇔ M odd" (seen in all 14 layers, not proved).
