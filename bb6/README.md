# BB(6) champion: exact step counts, proved in Coq

Machine (found by mxdys, June 2025; runs for more than 2↑↑↑5 steps):

    1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE

## Credit

The tape shapes and the rules "this shape reaches that shape" are the work of
**mxdys** (busycoq, `verify/SOBCv5.v`, module `TM62`, where the same machine is
written with renamed states). That proof shows the machine halts. It does not
count steps.

This folder adds the **exact number of steps of every move**, and from them an
exact formula for the halting time. Nothing here is a new fact about what the
machine does. What is new is the exact bookkeeping, and its formal proof.

## What is proved (`BB6Steps.v`, Coq 8.18, no axioms)

Notation: `N = 2^b - 1`, `j` = borrow length of a counter step, `q` = number
of ones after the marker `10` (so `q = m + 3a` in mxdys' numbers).

| Coq name | Move | Exact steps |
| --- | --- | --- |
| `tick` | counter − 1, right block + `111` (mxdys `Inc0`) | `12b + 12j + 48` |
| `full_ticks`, `T_closed` | all `N` ticks of an epoch | `6N² + 54N − 12b` |
| `load` | start of an epoch | `4q + 12j₀ + 3b + 63` |
| `epoch` | load + ticks (mxdys `Rst2/Rst1/Rst0`) | sum of the two above |
| `restart` | outer counter is zero, `q = 3a+1` (mxdys `Rst1'`) | `12·len0 + 12a + 3b + 97`, then the ticks |
| `last_move` | outer counter is zero, `q = 3a`: halt | `12·len0 + 12a + 60` |
| `init` | blank tape → S1(3, 7, 2, 6, 63) | `27,965` |
| `first_epoch` | end of the first epoch | `27,965 + 332 + T 63 0` |
| `runF_ok`, `runTop_ok` | any number of epochs in a row | given by the functions `runF`, `runTop` |
| `halt_ones` | ones on the tape after the halt | `len0 + a + 3b + 16` ones |
| **`bb6_halts_exactly`** | **the machine halts after exactly `halting_time` steps, and not before** | |
| **`bb6_final_ones`** | **the final tape holds exactly `final_ones` ones** | |

`halting_time` and `final_ones` are closed Coq terms built from the formulas
above (`final_ones = len0 + a + 3b + 16` at the last shape). They follow
the three passes of mxdys' proof (7 epochs, restart, second pass, restart,
third pass, halt). The remainders that decide "restart or halt" are proved
again here, in this model (`runF_inv`, `runTop_inv`).

The numbers themselves cannot be written out: they have far too many digits.
The theorems fix which numbers they are.

The first epoch ends at step

    510423550381407695582443536695552928613

## Check it yourself

    coqc BB6Steps.v        # about 5 seconds; prints "Closed under the global context"
    python3 check_steps.py # tests the formulas against plain simulation

## Not in Coq yet

- The transcript (digit string) of each move. The tick, written in digits
  with one digit per state–symbol pair (`0`=A0 … `9`=E1, `a`=F0, `b`=F1), is

      Tick(b, j≥1) = 9 (479)^(3j−1) 478602 (5b9)^(j+1) 4786025a
                     1^(3b+3) 02 (479)^(3b+5) 47879 (479)^2 47

  and the proof follows exactly these words, but the digit strings are not
  stated as theorems.
- A link to mxdys' Coq development. The two proofs use different tape models.
