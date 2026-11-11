"""Transcript grammar of the claimed BB(7) champion
    1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB

This script writes the digits of the run WITHOUT running the machine.
One digit per step: 2*state + symbol read, written 0-9 then a, b, c, d.

The run is:   START   R(13, 2)   W(P, j)  W(P, j)  W(P, j) ...   and at the end   H(P, j).

START is a fixed word of 319 digits (given below, with x(n) = n copies of x).
After it the tape, to the right of the head, is a row of blocks of ones:

    1^P  0^g1  1^c1  0^g2  1^c2  ...          state = (P, [(g1, c1), (g2, c2), ...])

One move reads only P, the first gap g1 = 2j and the first block c1 = Z:

    1^P 0^(2j) 1^Z ...   becomes   (11 00)^(j-1)  1^(3P+8-2j)  00  1^(Z-2) ...

and it prints the word W(P, j).  When Z is a single 1 there is nothing to take
2 from, and the parity of P decides (the gate):
    P even                          the machine halts and prints H(P, j);
    P odd, the 1 is the last cell   restart: it prints R(P, j) and builds
                                    (3P-1)/2 fresh units 1100.
In the real run the gate is met once with P = 13 (odd: restart, 19 units) and
after that everything stays even, so the next single 1 is the halt.
All of this was found by reading the digits and is checked against plain
simulation (run with --check).  It is a test, not a proof.
"""
import re, sys

# ---------- the words ----------
def Round(n): return "2476" + "9" * n + "8a0" + "3" * n          # one build round
def Build(P): return "".join(Round(3 * i + 1) for i in range(1, P + 1))
def Close(n): return "2468" + "b" * n
def Count(k): return "a1d" + "3" * k + "2468" + "b" * (k + 1)    # one countdown line
OPEN = "c47698a03"
WAIT = "c476998ba1"                                              # one waiting line

def head(P, j):
    return (OPEN + Build(P) + Close(3 * P + 4)
            + "".join(Count(k) for k in range(3 * P + 2, 3 * P + 3 - 2 * j, -1)))

def W(P, j):
    """The move word.  Length 3P^2 + 27P + 44 + 2j + (2j-1)(6P + 14 - 2j)."""
    m = 3 * P + 3 - 2 * j
    return (head(P, j) + "a1d" + "3" * m + Round(m + 1)
            + "2476" + "9" * (m + 5) + "8ba1" + WAIT * (j - 1))

def H(P, j):
    """The halting word.  It ends in 5 (C reads 1), the only 5 of the run."""
    m = 3 * P + 3 - 2 * j
    return (head(P, j) + "a1d" + "3" * m + Round(m + 1) + Close(m + 5)
            + "".join(Count(k) for k in range(m + 3, -1, -1))
            + "a1c47698b" + "a1c476998b" * ((m + 3) // 2) + "ba1d25")

RESTART_TAIL = {   # fixed endings of the restart word, and the new P
    1: ("a1c47699" + "98a0333" + Round(6) + Round(9) + Close(12) + Count(10)
        + "a1d" + "3" * 9 + Round(10) + "2476" + "9" * 14 + "8ba1", 14),
    2: ("a1c47699" + "98b" + "a1c476998a033" + Round(5) + Round(8) + Round(11) + Close(14)
        + Count(12) + "a1d" + "3" * 11 + Round(12) + "2476" + "9" * 16 + "8ba1", 16),
}

def R(P, j):
    """The restart word (P odd, j = 1 or 2)."""
    m = 3 * P + 3 - 2 * j
    return (head(P, j) + "a1d" + "3" * m + Round(m + 1) + Close(m + 5)
            + "".join(Count(k) for k in range(m + 3, -1, -1))
            + "a1c47698b" + "a1c476998b" * (m // 2 + 1) + RESTART_TAIL[j][0])

# ---------- the state rule ----------
def move(P, rest):
    """One move.  Returns (word, new P, new rest); new P is None at the halt.
    Returns None when the state is outside the tested range of the rule."""
    if not rest:
        return None
    (g, Z), tail = rest[0], rest[1:]
    j = g // 2
    N = 3 * P + 8 - 2 * j
    if g % 2 or N < 6:
        return None
    if Z == 1:
        if P % 2 == 0:
            return H(P, j), None, None                           # the halt
        if tail or j not in RESTART_TAIL:
            return None
        units = (3 * P - 1) // 2                                 # the restart
        return R(P, j), RESTART_TAIL[j][1], [(4, 2)] + [(2, 2)] * (units - 1) + [(2, 1)]
    new = [(2, 2)] * (j - 2) + ([(2, N)] if j >= 2 else [])
    if Z > 2:
        new += [(2, Z - 2)] + tail
    elif tail:
        new += [(2 + tail[0][0], tail[0][1])] + tail[1:]          # the two gaps join
    else:
        return None
    return W(P, j), (2 if j >= 2 else N), new

# ---------- the start ----------
START = re.sub(r"\s+", "", """
02468b(2)a1d2468ba1c47698ba1c47698a0324769(4)8a03(4)2468b(7)a1d3(5)2468b(6)a
1d3(4)2468b(5)a1d3(3)2468b(4)a1d3(2)2468b(3)a1d32468b(2)a1d2468ba1c47698ba1c
4769(2)8ba1c4769(2)8ba1c4769(2)8a03(2)24769(5)8a03(5)24769(8)8a03(8)2468b(11
)a1d3(9)2468b(10)a1d3(8)24769(9)8a03(9)24769(13)8ba1
""")
START = re.sub(r"([39b])\((\d+)\)", lambda m: m.group(1) * int(m.group(2)), START)
START_STATE = (13, [(4, 1)])                                      # tape after START

def digits(n):
    """The first n digits of the run, from the grammar alone."""
    parts, total = [START], len(START)
    P, rest = START_STATE
    while total < n:
        r = move(P, rest)
        if r is None:
            raise ValueError("state outside the tested rule: P=%d, first gap %d" % (P, rest[0][0]))
        parts.append(r[0]); total += len(r[0])
        if r[1] is None:
            break
        P, rest = r[1], r[2]
    return "".join(parts)[:n]

# ---------- check against the machine (only used with --check) ----------
def simulate(n):
    TM = "1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB"
    T = []
    for s in TM.split("_"):
        for r in (0, 1):
            c = s[3 * r:3 * r + 3]
            T.append((int(c[0]), 1 if c[1] == "R" else -1, ord(c[2]) - 65))
    size = 1 << 23; tape = bytearray(size); p = size // 2; s = 0; out = bytearray()
    for _ in range(n):
        k = 2 * s + tape[p]; out.append(b"0123456789abcd"[k])
        w, d, nx = T[k]; tape[p] = w; p += d; s = nx
        if s == 25: break
    return out.decode()

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a != "--check"]
    n = int(args[0]) if args else 100_000
    d = digits(n)
    if "--check" in sys.argv:
        print("first %d digits: grammar == machine: %s" % (n, d == simulate(n)))
    else:
        sys.stdout.write(d + "\n")
