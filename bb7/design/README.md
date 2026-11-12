# Designing a BB(7) machine from parts

Working notes, 12 November 2026. Vishnu Vaidyanathan, with Claude.

**Status: work in progress. No machine bigger than the known one has been found.**
What we have is a method, four working parts, one rule that explains why most
designs fail, and (section 10) one designed machine that runs from a blank tape
and is predicted to halt after about 5.5 × 10^328 steps. That is tiny next to
the claimed champion. Everything below can be rerun from the files in this folder.

**Important.** Sections 3 to 7 test parts on prepared tapes, not from a blank
tape. A table from those sections is not a Busy Beaver machine. For example
`1RB1LA_1RE0LC_---1LD_0LA0LB_0RF1RA_1LA1LF` stops after 9 steps from a blank
tape. Only section 10 runs things from blank.

---

## 1. The idea

The usual way to look for Busy Beaver machines is to try tables and watch what
they do. We turn this around.

We read the claimed BB(7) champion with the transcript lens (see `../README.md`)
and saw that its table is not random. It is made of parts, and each part has a job:

| Part | Job |
|---|---|
| Loop | multiply a block of ones by a fixed number |
| Fuel | allow one multiplication per fuel unit, then stop |
| Gate | when the fuel is gone, test the block (odd / even, or mod 3) |
| Restart | turn the block into new fuel and start again |
| Halt | one empty wire that the gate can reach |

So the question becomes: **what is the grammar of the table itself?**
Which small sets of wires can do each job, and how do the parts join?

### Words used here

- **Wire**: one entry of the table, for example `1RB` = write 1, move right, go to state B.
  A 7-state machine has 14 wires.
- **Empty wire** `---`: an entry not yet chosen.
- **Door**: an empty wire that the machine reaches at a meaningful moment
  (for example, exactly when a job is finished). Parts are joined at doors.
- **Contract**: what a part must do, written as "tape before → tape after".
- **Lazy search**: we do not try every table. We run the machine, and only when
  it reaches an empty wire do we try the 28 ways to fill it. Wires never reached
  are never filled. This is what makes the searches small.

---

## 2. First try: keep the champion's loop, change the rest

File: `src/0_family_scan.c`

The champion is `1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB`.
Nine of its wires make the tripling loop (A0, B0, B1, C0, D0, D1, E0, E1, F0).
We kept those nine and let the other five be anything: 3,073,280 tables.

| Kind | Tables |
|---|---|
| Halt early | 917,505 (none later than step 2,000, checked to 200,000 steps) |
| Run off to one side | 15,834 |
| Stay tiny | 305,855 |
| Still alive | 1,834,086 |
| Alive and tripling | about 5,900 |

- Most triplers carry no fuel.
- A few dozen are "adders": each round adds a fuel unit instead of eating one. Never halt.
- Only the champion (and one twin differing in G0) eats pre-built fuel.

**Lesson.** On this loop the champion is alone. Its five free wires are all
used, so nothing nearby can be bigger. A bigger machine needs a different design.

---

## 3. Part 1: the Loop

File: `src/1_loops.c`

Contract: start on `1^n 00 1^P`, end with one solid block, gaining a fixed
number of ones per old one.

| Loop | Smallest wiring found | Size |
|---|---|---|
| ×3 | `0LB0LA_1RC0LA_0RA---` | 3 states, 5 wires |
| ×4 | `0LB0LA_0LC0LA_1RD---_0RB---` | 4 states, 6 wires |
| ×5, ×6 | several | 8 wires |

**Lesson.** Multiplying is cheap. The champion uses 6 states and 9 wires for
it; 3 states and 5 wires are enough. There are thousands of such loops.

### Engines (loops that feed themselves)

File: `src/2_engines.c`, check with `src/engine_check.py`

Contract: `[A] 0^g 1^P` comes back to the same shape with `kP + c`, forever.

| Engine | Wiring | Checked |
|---|---|---|
| ×3 | `1RA0RB_1LD0LC_1RB---_0LA0LD` | 2 → 6 → 18 → 54 → 162 → 486 → 1458 → 4374 |
| ×4 | `0RB1LC_0LC1RA_1LA0LD_1LB---` | 2 → 7 → 27 → 107 → 427 |
| ×5 | `1LB1LA_1RC0LA_---0RD_1RA0RB` | 2 → 25 → 140 → 715 |

With 7 wires there are 57 ×3 engines, three ×4, one ×5. List: `results/engines_7wires.txt`.

**Lesson (a mistake we made).** These engines are *closed*. Their one empty
wire is never reached, so nothing can be attached to them. A part is only
useful if it has a real door.

---

## 4. Loops with a door

File: `src/3_loops_with_door.c`

New contract: `[A] 0^g 1^P` → one solid block `1^(kP+c)`, **and at that moment
the machine reaches an empty wire**. That wire is the door. It means
"the old block is used up".

The simplest one: `0LB0LA_1RB1RC_---1LA` (3 states, 5 wires, ×3).
It can be read like a sentence:

- **A**: erase everything to the left, then step one more left.
- **B**: fill ones to the right until the old block.
- **C**: look at the next cell. If 1, go back and repeat. If 0, finished: door `C0`.

We found 1,648 such loops (×3 and ×4) with up to 7 wires.
Lists: `results/door_loops_5_6_wires.txt`, `results/door_loops_7_wires.txt.gz`.

---

## 5. Part 2: Fuel

File: `src/4_fuel.c`

Contract: put fuel units to the right of the block. Then

- each unit gives exactly one more multiplication, and
- when the fuel is gone, a second door opens with the tape as one clean block.

The search takes each door-loop, adds a few wires, and tests with 0, 1, 2 and 3 units.

| Total size | Found |
|---|---|
| 8 wires, 5 states | 1 machine |
| 9 wires, 5 or 6 states | 396 different machines (most ×3, some ×4) |

List: `results/engine_fuel_machines.txt` (table, door, door offset, fuel shapes that work).

The 8-wire one: `1RB1LA_1RE0LC_---1LD_0LA0LB_---1RA`

- Tape: `[A] 0 11 0` then units `110`.
- Each unit turns the block Q into 3Q + 8.
- Checked for 0 to 5 units: 8 → 32 → 104 → 320 → 968 → 2912 ones, each time
  ending as one solid block at the door `E0`.

We also built one by hand on the simple loop (add a "look right" state and a
"walk back left" state: `0LB0LA_1RB1RC_1RE1LA_0LB1LD_---0LD`). It works, and the
search found the same kind. So reading and searching agree.

**Budget.** The champion spends 9 wires on tripling + fuel and has 5 left.
The 8-wire machine leaves 6.

---

## 6. Part 3: Gate + Restart

File: `src/5_gate_restart.c`, independent check: `src/door.py`

Start at the fuel door: tape is a solid block `1^Q`. Add up to 3 to 5 wires.
For each small Q the run must either

- come back to the same door with a bigger block Q' (**restart**), or
- stop at an empty wire (**halt**).

This worked much faster than expected. Two examples, both checked separately in Python:

**A mod-3 gate** — `1RB1LA_1RE0LC_---1LD_0LA0LB_0RF1RA_1LA1LF` (11 wires, 6 states)

| Q mod 3 | What happens |
|---|---|
| 0 | small step: Q → Q + 5 |
| 1 | restart: 4 → 41, 7 → 131, 10 → 401 (triples for every +3 in Q) |
| 2 | halt (at wire `C0`) |

**A mod-2 gate** — `1RA1RB_1RD1LC_0LA0LC_0LE1LD_0RA0LF_---1LE` (11 wires, 6 states)

| Q | What happens |
|---|---|
| odd | halt (at wire `F0`) |
| even | restart: 4 → 9, 6 → 30, 8 → 93, 10 → 282, 12 → 849 |

So **Loop + Fuel + Gate + Restart + Halt fits in 6 states and 12 wires.**
The seventh state is completely free.

Lists: `results/gates_add3_all_machines.txt.gz` (3 added wires, on all 397
Engine+Fuel machines, 2,663 gates) and `results/gates_add5_best_machine.txt.gz`
(up to 5 added wires on the 8-wire machine, 3,616 gates).

---

## 7. The rule that decides everything: collapse

A restart gives a block of the form

    Q' = a · b^n + c        (b = the base, n grows with Q)

The gate then tests Q' modulo m. Here is the problem:

- base 3, gate mod 3: `3^n` is 0 mod 3, so Q' is always in the **same** class.
- base 3, gate mod 2: `3^n` is always odd, so Q' always has the **same** parity.
- base 4, gate mod 3: `4^n` is always 1 mod 3. Same again.

We call this **collapse**. After the first restart the machine always lands in
one fixed class. That class either halts (the run ends after one big step) or
restarts (the run never ends). There is no long finite run.

Of the gates found that can halt and grow: about 1,600 collapse, about 380 do not.

The ones that do not collapse have a division in the formula. Example, the
mod-2 gate above:

    Q' = (21 · 3^n − 3) / 2,   n = (Q − 4) / 2

Now the parity of Q' depends on whether n is odd or even. But following it one
level further:

- n even → Q' is odd → halt.
- n odd → Q' is 2 mod 4 → the next n is odd again → the same forever.

So this one also settles, just one level later: it halts after one restart or
never.

**The general rule.** The classes form a small finite map. A finite run can
pass through each class at most once. So the number of big restarts before
halting is at most (number of classes − 1). A tall finite tower needs a gate
with many classes that feed each other in a long chain before reaching "halt".

This is the real target now. It is no longer "find a tripler". It is
**"find a gate whose class map has a long path to halt"**.

---

## 8. What is done and what is not

Done:

- [x] Loop: many, down to 3 states / 5 wires.
- [x] Fuel: 397 machines, best 8 wires.
- [x] Gate + Restart + Halt: thousands, in 6 states.
- [x] The collapse rule.

Not done:

- [ ] A gate whose class map has a path of length 2 or more to halt.
      Ideas: base and modulus that do not collapse (base 2 or 5 with mod 3,
      base 3 with mod 4); fuel units of length 4; use the free seventh state
      to add classes.
- [x] A boot from a blank tape (section 10).
- [x] A first calculator for the class map (`src/fate.py`). It handles simple
      maps only; 343 maps were too irregular for it.
- [x] Why the champion is tall (section 11): a stack of counters and a swap
      move, not a clever gate.
- [x] A design with the swap move (section 12): 13 wires, works on prepared tapes.
- [ ] The same with a restart and a halt inside 14 wires (one wire short now).
- [ ] Any proof. Nothing in this folder is proved in Coq.

Limits of the searches (so nobody over-reads them):

- Loops and engines: up to 8 wires, 6 states, only the tape shapes described.
- Fuel: only fuel on the right, only units `1, 10, 100, 110, 1100, 1110, 1000, 101`.
- Gates: tested only for Q = 3 to 14. Formulas are fitted from those values.
- Only a handful of machines were re-checked by a second program
  (the ones named in this file).

---

## 9. How to rerun

    cd src
    gcc -O2 -o loops   1_loops.c
    gcc -O2 -o engines 2_engines.c
    gcc -O2 -o dloops  3_loops_with_door.c
    gcc -O2 -o fuel    4_fuel.c
    gcc -O2 -o gate    5_gate_restart.c

    ./loops 8 6 2 3            # max wires, max states, gap, n     (4 minutes)
    ./engines 7 6 0 2          # max wires, max states, n, gap     (40 seconds)
    ./dloops 7 6 1             # max wires, max states, gap        (15 seconds)
    ./fuel 4 < ../results/door_loops_5_6_wires.txt   # add up to 4 wires
    ./gate 3 1RB1LA_1RE0LC_---1LD_0LA0LB_---1RA E0 1 tag
                               # add wires, table, door wire, door offset, label

    python3 t2.py 0LB0LA_1RB1RC_---1LA "[]0111" 40        # step-by-step trace
    python3 engine_check.py 1RA0RB_1LD0LC_1RB---_0LA0LD 0 2 7
    python3 door.py 1RA1RB_1RD1LC_0LA0LC_0LE1LD_0RA0LF_---1LE E1 0 3 12
    python3 mixing.py gates.txt                           # collapse / no collapse

Reading the output of `gate`: `res:` lists what happens for Q = 3, 4, 5, …, 14.
A number is the new block size; `H` means it stopped at the empty wire named in
`haltwire`.

---

## 10. Boot: running from a blank tape

Files: `src/6_boot_from_blank.c`, `src/7_long_run.c`, `src/8_doors_and_map.c`,
`src/fate.py`, `src/verify_best.py`

From here on the rule is: **a candidate counts only if it is run from a blank tape.**

### The search

- Take all 6,154 gate tables (`results/gate_tables_all.txt`).
- Try each of the 7 states as the start state.
- Allow one extra wire (28 choices) when the run reaches an empty wire.
- An empty wire that is reached counts as a halt.

| Result | Count |
|---|---|
| Runs tried | about 430,000 |
| Halt before 100,000 steps (and after step 300) | 1,125, longest 45,661 steps |
| Still running at 100,000 steps | 260,671 |
| Of those, with an empty wire left | 101,880 |
| Halt between 100,000 and 3,000,000 steps | 24, longest 448,484 steps |
| Still running at 3,000,000 steps | 101,856 |
| Of those, with a gate that can halt at all | 4,499 |

### Working out the fate without running to the end

For each of the 4,499 we record two things (`8_doors_and_map.c`):

1. **Doors from blank**: the block sizes Q at the moments the tape is one solid
   block with the head at the door.
2. **The gate map**: what the gate does from the door for Q = 3 to 14.

`fate.py` then fits the map (halt / small step / restart, by Q mod m) and
follows it from the last door seen.

| Predicted fate | Count |
|---|---|
| Runs forever in small steps | 1,481 + 1,092 |
| Restarts forever (or more than 6 levels) | 1,427 |
| Map too irregular to fit | 343 |
| **Halts after one big restart** | **154** |

List: `results/predicted_halters_from_blank.txt`.

### A bug the direct run caught

The first version of `fate.py` predicted 158 halters. We ran the 16 smallest
in full. Twelve halted exactly as predicted (the largest after 3,632,116,441
steps with 49,210 ones). Four did not: their gate had halted for Q = 4 only,
and had given no answer for other even Q, and the script had read that as
"even halts". Fixed: a class counts as "halt" only if every tested Q in it
halts. That left 154.

**Lesson.** Always run the smallest predicted cases to the end.

### The best one

In standard form (start state A):

    1LC---_1RB1RC_1RE1LD_0LB0LD_1LF1LE_0LB1LG_---0LF

(the two `---` are halt wires; only `G0` is reached). State A is used for one
step only. The other six states are loop, fuel, gate and restart.

What it does from a blank tape:

| Step | Tape |
|---|---|
| 39 | solid block of 11 ones, at the door |
| 177,133 | solid block of 689 ones, at the door |
| about 5.5 × 10^328 | block of (17·3^343 + 1)/2 ones, which is even → halt |

Its gate:

- Q even: halts after Q − 1 more steps, leaving Q/2 + 1 ones.
  Checked for every even Q from 4 to 200 and for 256, 1024, 2066, 4096.
- Q odd: restart, new block = (17·3^n + 1)/2 with n = (Q − 3)/2.
  Checked for Q = 3 to 15.
- Steps for the restart = (867/32)·9^n − (17/2)·3^n + (17/4)·n + 109/32.
  Fitted on five values of n, then matched two more exactly.
- Full run from a block of 13: halts at step 1,599,883 with 1,034 ones.
  The formulas give exactly 1,599,883 and 1,034.

Predicted halting step (329 digits):

    54707876372742107360416375538201134556804738790941900885463162812560
    20390464824462986165083797230109705483114959239029815932511193440313
    46498063467309452668560388555827379996928518037997114163468011693339
    96414960043027674691102359828234042016866081564249513537575500690798
    196494676879822444841073191707331145687998679996296675620

Ones left on the tape: (17·3^343 + 1)/4 + 1, a 165-digit number.

**What this is and is not.**

- It is a machine designed from parts that runs from a blank tape, with its
  halting time predicted from formulas.
- It is **not proved**. The formulas are fitted to small cases and checked on a
  few more. A Coq proof would be needed to claim it.
- It is **not big** by today's standards. The claimed BB(7) champion is listed
  with a bound of 3↑^20 3, and even BB(6) is known to be far beyond 10^328.
  This machine does one big restart and stops, exactly as the collapse rule says.

To check: `python3 verify_best.py` (about 5 minutes).

### What the boot search tells us

- The boot is not the hard part. One step of a seventh state was enough to
  reach the door.
- The size is decided by the gate map. Every halting design found does one big
  restart. To get further we need a gate map with a longer path to halt
  (section 7).

## 11. How the champion really gets tall: one rule, a stack of counters

After section 10 we asked the wrong question ("how do we make the gate
cleverer?"). Going back to the champion's own move rule (`../bb7_grammar.py`,
function `move`, proved in `../BB7Moves.v`) gives a different answer.

### The tape is a stack

The clean shape is `1^P`, then a list of (gap, block) pairs. The leftmost block
is always P. The blocks after it are **counters**.

### One rule, three behaviours, chosen by the gap

| Gap after P | What the move does |
|---|---|
| 2 | **Triple.** P → 3P + 6. First counter loses 2. |
| 4 | **Swap.** The tripled block becomes a new counter. A fresh P = 2 is planted on its left. The old first counter loses 2. |
| 6 | Swap, and also plant one extra small counter (a block of 2). |

And one more fact: **when a counter reaches 0 its two gaps join** (2 + 2 = 4,
2 + 4 = 6). So an empty counter makes a wider gap, and a wider gap makes a swap.
That is how "this level is finished" is passed up to the next level. Nothing
tests it. The gap width is the signal.

### Seen on the real tape

    step 3954   [G] 1^16  0000  11 00 11 00 ... (19 units) ... 1
    step 5520   [G] 11 00 1^52  0000  11 00 ... (18 units) ... 1     <- one move, gap 4
    step 5656   [G] 1^12  00  1^50  0000  11 00 ...                  <- next move, gap 2

After the gap-4 move the old block (now 52) is the counter and P is 2.
Then 25 triplings use it up.

### The run, in the big-number form

    start    P=13            | gap4 1
    RESTART  P=16            | gap4 2 , gap2 2 (x18) , gap2 1
    swap     P=2             | gap2 52 , gap4 2 , gap2 2 (x17) , gap2 1
    x3 (25)  P=4236443047212 | gap2 2 , gap4 2 , gap2 2 (x17) , gap2 1
    x3       P=12709329141642| gap6 2 , gap2 2 (x17) , gap2 1
    gap 6    P=2             | gap2 2 , gap2 38127987424928 , gap4 2 , gap2 2 (x16) , gap2 1
    x3       P=12            | gap4 38127987424928 , gap4 2 , ...
    swap     P=2             | gap2 40 , gap2 38127987424926 , gap4 2 , ...
    x3 (19)  P=5811307332    | gap2 2 , gap2 38127987424926 , ...
    x3       P=17433922002   | gap4 38127987424926 , gap4 2 , ...
    swap     P=2             | gap2 52301766010 , gap2 38127987424924 , ...
    next: 26,150,883,004 triplings in a row. P becomes about 3^(2.6 x 10^10).

Look at the counter 38127987424924. Each swap takes only 2 from it, and each
swap turns the whole current P into a new counter, which is one
exponentiation. So this single counter gives about 1.9 x 10^13 exponentiations
stacked on each other. And 16 more units are still waiting behind it.

So the champion has not two levels but a ladder:

| Level | Counted by | One step does |
|---|---|---|
| 1 | first counter, gap 2 | tripling |
| 2 | second counter, gap 4 | exponentiation (swap) |
| 3 | the units, gap 6 | a whole tower of level 2 |

### Which wires do it

The gap-2 move and the gap-4 move use the same loops. The differences:

- **Count lines** (wires F1, A1, G1): 2j − 1 of them for a gap of 2j. They
  carry the new block across the gap, so they measure the gap.
- **Wait lines** (wire G0): j − 1 of them. Each one plants a `11 00` on the
  left. With gap 2 there are none. With gap 4 there is one, and that planted
  `11` is the new P.

So the whole ladder costs the champion **one wire** (G0) on top of tripling
and counting. No wire is spent per level.

### What this changes for the design

Our parts list in section 1 was too flat. The champion is not
"loop + fuel + gate + restart" as four boxes. It is:

1. one **move** that takes the gap as a parameter (triple or swap),
2. counters that **join gaps when empty**,
3. a **restart** that makes many units from P,
4. a **gate** only for the very end.

The boot is not a separate part. The champion's first 319 steps only reach a
clean tape with P = 13 (odd) and no fuel. The restart then makes the 19 units.

Our designed machines (section 10) have 1-level fuel only: a unit buys one
tripling, and nothing ever swaps. That, and not the collapse rule, is why they
stop at 10^328.

**The new contract to search for** (on prepared tapes first, then from blank):

    1^P  gap2  1^Z  rest   ->   1^(3P+c)  gap2  1^(Z-2)  rest             (triple)
    1^P  gap4  1^Z  rest   ->   1^s  gap2  1^(3P+c')  gap2  1^(Z-2)  rest  (swap)
    a counter at 0 joins its gaps

## 12. The swap move: found, and one wire short

Files: `src/9_swap.c`, `src/ladder.c`, `src/canon.c`, `src/wire_use.c`

### The search

Seeds: the 71 Engine+Fuel machines whose fuel is a solid counter block
(`results/counter_block_seeds.txt`). They already do the first line of the
contract (gap a: triple, counter − 1). We add wires for the second line:

    [A] 0^g 1^P 0^(2a) 1^Z   ->   [A] 0^g 1^s 0^a 1^N 0^a 1^(Z-1)

with s small and N growing with P.

| Added wires | Total | Found |
|---|---|---|
| 3 | 12 | 0 |
| 4 | 13 | 64 |

List: `results/swap_machines_13wires.txt`.

### It works as a ladder (on prepared tapes)

Machine `0LB0LA_1RB1RC_1RD1LA_1RF0LE_0RC1LE_---0LG_1LC1LG`
(tape written as block sizes, gaps in brackets):

| Start tape | Result |
|---|---|
| `2 (1) 1` | halts, 23 ones |
| `2 (1) 2` | halts, 68 ones |
| `2 (1) 3` | halts, 203 ones (×3 per counter unit) |
| `1 (2) 1` | halts at step 448,431 with 1,094 ones = (3^7 + 1)/2 |
| `2 (2) 1` | halts at step 326,886,086 with 29,525 ones = (3^10 + 1)/2 |
| `1 (2) 2` | still running at 2 × 10^10 steps, on its way to about 3^1094 |

A step-by-step view (`canon`), start `1 (2) 2`:

    1 (2) 2
    1 (1) 5 (1) 1          <- swap: new P = 1, old block is now a counter of 5
    4 (1) 4 (1) 1
    13 (1) 3 (1) 1
    40 (1) 2 (1) 1
    121 (1) 1 (1) 1
    364 (2) 1              <- counter empty: the gaps joined into a double gap
    1 (1) 1094             <- swap again: 364 became a counter of 1094
    4 (1) 1093 ...

So in these machines: **gap 1 = triple, gap 2 = swap, gap 3 = halt.**
The second counter counts exponentiations, as in the champion.

### From a blank tape: nothing

All 64 machines, from every start state: 296 runs halt within 22 steps, the
other 152 run off to one side filling ones. They have 13 wires and one halt
wire. Nothing is left to make the first counters.

### Filling the last wire: a tower from blank, but no halt

We filled the halt wire in all 28 ways and ran from blank (12,544 runs).
Some now build counters by themselves. Example
`1RB1LA_0LC0LB_1RC1RD_1RE1LB_1RF0LA_1LF0LG_0RE1LG`, start A, blank tape:

    step 18           2 (2) 1
    step 46           2 (1) 5
    step 89,339       486                 <- everything used up
    step 799,395      2 (1) 1456 (1) 1    <- RESTART: 486 became a counter of 1456
    step 581,989,164  39366 (1) 1447 (1) 1 ...

So the filled wire acts as a **restart**: a finished block Q becomes a counter
of about 3Q. That is a tower growing forever from a blank tape. But with all
14 wires used it can never halt.

In 542 of these runs the swap wire `F1` is never used (there is never a second
counter), so triple + restart alone need only 11 to 13 wires.

### Where this stands

| Part | Wires |
|---|---|
| Loop + counter (triple) | 9 |
| Swap | 4 |
| Restart (makes the first counters from blank) | 1 |
| Halt | 1 |
| **Total** | **15** |

We have 14. **We are one wire short.** The champion fits the same jobs into
14 by letting its restart reuse the wires of its move.

Ways forward:

1. A cheaper swap. A looser version of the contract gives candidates with 10
   and 11 wires (`results/loose_swap_candidates.txt`). The few we
   looked at use a different tape code (P stored as separated single ones) and
   have **not** been checked as ladders.
2. A cheaper triple (the 8-wire machine uses `110` units, not a block, so it
   cannot be swapped as it is).
3. Let the restart share wires with the swap, as the champion does.

### Follow-up: the cheaper candidates are not ladders

File: `src/ladder_check.c`, results in `results/loose_swap_ladder_check.txt`

We tested all 678 loose candidates (10 to 12 wires) with a second counter of
1, 2 and 3. A real ladder finishes with 1 and explodes with 2. The best
11-wire candidate, `0LB0LC_1LC1LB_1RD1LA_0RE1RC_1RF0LA_1LE---`, gives

| Second counter | Ones at the end |
|---|---|
| 1 | 6,144 |
| 2 | 24,576 |
| 3 | 98,304 |

That is ×4 per unit: plain multiplication. These machines are one level lower
than we need. Their two levels are "add" and "multiply", where ours must be
"multiply" and "exponentiate". A third counter does not add a level either: it
is simply merged into the second.

We also checked the idea "let the unused swap wire be the halt". In the 3,222
blank-tape runs where the swap wire `F1` is unused, the clean tape never has a
third block waiting, so `F1` would never be reached. No halting machine there.

**So lead 1 is closed. We are still one wire short.** Leads 2 and 3 remain.

## 13. The champion is one oscillator (and one try at finding another)

### Reading the restart

The champion's restart (steps 319 to 3,954 of the real run) uses no loop of
its own. Phase by phase, with the real tape after each phase:

    before        1 0 [G] 0  1^13  0000  1
    1. triple     1^42 [B] 000000 1                         (Open + Build)
    2. cross gap  1 0 1 0 1 0 [F] 0  1^40  00  1            (Close + 3 Count lines)
    3. meet       1 0 1 0 1 0  1^42 [B] 0                   (the last 1 is swallowed)
    4. go down    1 0 1 0 11 0 1 0 1 0 ... (42 pairs) [F] 0 1    (42 Count lines)
    5. pack       1 0 1 0 11 [F] 0 1 0  11 00 11 00 ... (19 units) ... 1   (21 Wait lines)
    6. ending     1 0 [G] 0  1^16  0000  11 00 ... (19 units) ... 1

Vishnu's reading: this is not a restart. It is the **down phase of an
oscillator**. The tape must nest down before it can go up.

That fits the wires exactly. At the right end of the block the head looks two
cells ahead (state D):

| D reads | Digit | Stroke | Effect |
|---|---|---|---|
| 1 | 7 | up (a Round, `2476…`) | take one cell from the block on the right; the working block gains 3 |
| 0 | 6 | down (a Count line, `…2468…`) | the block loses 1; a `1 0` pair is left on the left |

So:

| What we called it | What it is |
|---|---|
| tripling | up-strokes, while there is something on the right |
| crossing a gap | a few down-strokes, until the next block is in view |
| swap | a longer down, then up on the next block |
| restart | down-strokes with nothing on the right, all the way to the bottom |

Down is the default, because blank tape is 0. That is why the champion's
restart costs no wire, and why our box-by-box designs came out one wire over:
each box had its own wire to ask "is anything on the right?".

At the bottom, state G reads 0 instead of 1 (digit c instead of d). That starts
the Wait loop, which packs `1 0 1 0` into `11 00`. Then it goes up again.

### Checking the oscillator reading on the real run

File: `src/13_oscillator_check.c` (`gcc -O2 -o chk 13_oscillator_check.c && ./chk 60000000`)

A "look" is state D reading a cell right after B0, C0. At each look we measure
the working block (the solid run of ones ending where B just wrote) and the
trail of ones on its left, and compare with the next look.
First 60,000,000 steps from a blank tape:

| D read | Prediction | Looks | Exactly as predicted | Different |
|---|---|---|---|---|
| 1 | up: block +3 | 7,739 | 7,718 | 21 |
| 0 | down: block −1, trail +1 | 78 | 75 | 3 |

The 24 differences are all of two kinds:

- 13 have a bottom turn (G reads 0) between the two looks, so the next look is
  on a new block. Expected.
- 11 are "block +4, trail −1": the block gains its 3 and also swallows one
  trail cell that was touching it. This happens once per move, at the first
  up-stroke after a down phase.

No other case occurs. So in 7,817 looks the rule "1 ahead = up, 0 ahead = down"
never fails; it only needs the two footnotes above.

### One try at finding another oscillator

Files: `src/10_down_stroke.c`, `src/11_oscillator.c`, `src/12_signature.c`

1. **Down-stroke.** For each of the 1,648 up-stroke loops, add up to 3 wires
   so that a solid block with nothing on its right is taken apart into small
   pieces. Found 103,535 (the test is loose).
2. **Up again.** On those with 9 wires or fewer, add up to 2 wires so that a
   block twice the first top appears afterwards. Found 30,938 candidates
   (27,780 different tables, `results/oscillator_candidates_loose.txt.gz`).
3. **From a blank tape**, every start state, one extra wire allowed:
   692 halts (longest 90,917 steps), 872,870 runs still going at 100,000 steps.
4. **Signature** (small units present, big block growing, units getting
   fewer). This scan was stopped early. Its hits were ordinary machines caught
   in the middle of a pass, or machines that grow in a straight line with their
   units untouched. We found no run where units are eaten one at a time the way
   the champion eats them.

**Result of this try: nothing.** The tests in steps 1, 2 and 4 are too loose
to pick out an oscillator from the many machines that merely grow. A sharper
contract is needed, written directly from the two strokes above.

## 14. Credits

The BB(7) machine that started this is Jeff Ketchersid's. The method of
reading a table as parts with jobs came out of the transcript-grammar work in
this repository.
