"""Test of the transcript words given in the paper (Section "Transcript words").

For each move of the BB(6) champion 1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE
this builds the word from its formula and compares it, character by
character, with the transcript of a plain simulation started from the
matching tape shape.  It also checks that the champion's run from the blank
tape joins the run started in state B (busycoq's TM63) after 15 and 9 steps.

One character per step: 0=A0, 1=A1, 2=B0, 3=B1, 4=C0, 5=C1, 6=D0, 7=D1,
8=E0, 9=E1, a=F0, b=F1.  This is a test, not a proof.
"""
SPEC = "1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE"
TT = []
for st in SPEC.split("_"):
    for i in (0, 3):
        TT.append((int(st[i]), 1 if st[i + 1] == "R" else -1,
                   -1 if st[i + 2] == "Z" else ord(st[i + 2]) - 65))
DIGITS = "0123456789ab"
MARK = {2: "1011", 1: "101", 0: "10"}


def LC(n, x):
    """A counter of n bits with value x, high bit first: 1 = 100, 0 = 111."""
    return "" if n == 0 else LC(n - 1, x // 2) + ("100" if x % 2 else "111")


def shape(len0, a0, m, len1, a1, b):
    """Tape of S1(len0, a0, m, len1, a1, b); the head is on the last cell of
    the left part, in state E."""
    left = "1110" + "11" + LC(len0, a0) + "100" + MARK[m] + LC(len1, a1)
    right = "0" + "11100" + "111" * (1 + b)
    return left, right


def transcript(left, right, state, n):
    size = 1 << 14
    tape = bytearray(2 * size)
    for i, ch in enumerate(left):
        tape[size - len(left) + 1 + i] = int(ch)
    for i, ch in enumerate(right):
        tape[size + 1 + i] = int(ch)
    pos, s, out = size, state, []
    for _ in range(n):
        k = 2 * s + tape[pos]
        w, mv, ns = TT[k]
        tape[pos] = w
        pos += mv
        s = ns
        out.append(DIGITS[k])
        if s < 0:
            break
    return "".join(out)


W, F = "479", "5b9"
PHI = "4786025a02" + W * 2 + "47879" + W * 2 + "47"


def opening(q):
    return "9" + W * (q - 1) + "47878602" if q > 0 else "878602"


def turn(L):
    return W * (3 * L + 5) + "47879" + W + "4786025b8602" + F * (L + 2) + "478602"


def tick(b, j):
    p = "9" + W * (3 * j - 1) + "478602" if j > 0 else "8602"
    return (p + F * (j + 1) + "4786025a" + "1" * (3 * b + 3) + "02"
            + W * (3 * b + 5) + "47879" + W * 2 + "47")


def load(q, j0, b):
    return (opening(q) + W * (3 * j0 + 3) + "478602" + F * (j0 + 1) + "5a"
            + "1" * (q + 3) + "02" + F * (b + 1) + PHI)


def restart(q, L, b):
    a = (q - 1) // 3
    return (opening(q) + turn(L) + F * (a + 1) + "5b8602" + F * (b + 1) + PHI)


def halt(q, L):
    return opening(q) + turn(L) + F * (q // 3 + 1) + "5a03"


def v2(n):
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def configs(start, n):
    """Configurations of a run from the blank tape, up to a shift."""
    tape, pos, s, out = {}, 0, start, []
    for i in range(n + 1):
        ones = sorted(k for k, v in tape.items() if v)
        lo = ones[0] if ones else pos
        hi = ones[-1] if ones else pos
        out.append((s, pos - lo, tuple(tape.get(k, 0) for k in range(lo, hi + 1))))
        w, mv, ns = TT[2 * s + tape.get(pos, 0)]
        tape[pos] = w
        pos += mv
        s = ns
    return out


if __name__ == "__main__":
    E = 4
    good = total = 0
    for m in (0, 1, 2):
        for a in range(3):
            for b in range(3):
                q = m + 3 * a
                for len0, a0 in ((2, 1), (2, 2), (3, 4), (3, 7)):
                    l, r = shape(len0, a0, m, a, 0, b)
                    w = load(q, v2(a0), b)
                    total += 1
                    good += transcript(l, r, E, len(w)) == w
                for L in (0, 1, 3):
                    l, r = shape(L, 0, m, a, 0, b)
                    if m == 1:
                        w = restart(q, L, b)
                        total += 1
                        good += transcript(l, r, E, len(w)) == w
                    if m == 0:
                        w = halt(q, L)
                        total += 1
                        good += transcript(l, r, E, len(w) + 5) == w
    for len1 in (3, 4):
        for n in range(1, 2 ** len1):
            for b in (0, 1, 3):
                l, r = shape(2, 1, 2, len1, n, b)
                w = tick(b, v2(n))
                total += 1
                good += transcript(l, r, E, len(w)) == w
    print("transcript words: %d of %d cases match the simulation" % (good, total))

    fromA, fromB = configs(0, 30020), configs(1, 30020)
    merge = all(fromA[15 + k] == fromB[9 + k] for k in range(30000))
    print("run from A after 15 steps = run from B after 9 steps, and they "
          "stay equal for the next 30000 steps:", merge)
