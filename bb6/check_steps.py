"""Independent check of the step formulas proved in BB6Steps.v.

Runs the BB(6) champion 1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE by plain
simulation and compares with the formulas.  This is a test, not a proof; the
proof is the Coq file.

Shape S1(len0, a0, m, a, b) (mxdys, busycoq SOBCv5.v, module TM62), written
for this machine, left to right:

    1110 11  LC(len0,a0)  100  10 1^m  (111)^a  [head E on last cell]
    0 11100 (111)^(1+b)

LC writes a number in binary, high bit first: bit 1 = 100, bit 0 = 111.
"""
SPEC = "1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE"
TT = []
for st in SPEC.split("_"):
    for i in (0, 3):
        TT.append((int(st[i]), 1 if st[i + 1] == "R" else -1,
                   -1 if st[i + 2] == "Z" else ord(st[i + 2]) - 65))


def LC(n, x):
    return "" if n == 0 else LC(n - 1, x // 2) + ("100" if x % 2 else "111")


def s1(len0, a0, m, a, b):
    left = "1110" + "11" + LC(len0, a0) + "100" + "10" + "1" * m + "111" * a
    right = "0" + "11100" + "111" * (1 + b)
    return left, right


def run(left, right, state, max_steps):
    """Head starts on the last cell of `left`.  Returns (steps, ones) at halt."""
    size = 1 << 20
    tape = bytearray(2 * size)
    for i, ch in enumerate(left):
        tape[size - len(left) + 1 + i] = int(ch)
    for i, ch in enumerate(right):
        tape[size + 1 + i] = int(ch)
    pos, s = size, state
    for n in range(1, max_steps + 1):
        w, mv, ns = TT[2 * s + tape[pos]]
        tape[pos] = w
        pos += mv
        s = ns
        if s < 0:
            return n, sum(tape)
    return None


def v2(n):
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def ticks(b):                      # T b 0 in the Coq file
    N = 2 ** b - 1
    return 6 * N * N + 54 * N - 12 * b


def predict(len0, a0, m, a, b, limit=10 ** 7):
    """Halting step from S1(len0,a0,m,a,b), using only the formulas."""
    t = 0
    while t <= limit:
        N = 2 ** b - 1
        if a0 > 0:                                   # epoch
            t += 12 * a + 3 * b + 12 * v2(a0) + 63 + 4 * m + ticks(b)
            a0, m, a, b = a0 - 1, (m - 1) % 3, a + b + (2 if m else 1), N
        elif m == 1:                                 # restart
            t += 12 * len0 + 12 * a + 3 * b + 97 + ticks(b)
            len0, a0, m, a, b = (len0 + 2 + a,
                                 ((2 ** len0 - 1) * 4 + 3) * 2 ** a - 1, 2, b, N)
        elif m == 0:                                 # halt
            return t + 12 * len0 + 12 * a + 60, len0 + a + 3 * b + 16
        else:
            return None
    return None


if __name__ == "__main__":
    E = 4  # state E
    cases = good = 0
    for len0 in (1, 2, 3):
        for a0 in range(2 ** len0):
            for m in (0, 1, 2):
                for a in (0, 1, 2):
                    for b in (0, 1, 2):
                        p = predict(len0, a0, m, a, b)
                        if p is None:
                            continue
                        left, right = s1(len0, a0, m, a, b)
                        cases += 1
                        good += run(left, right, E, 2 * 10 ** 7) == p
    print("small runs to halt: %d of %d predicted exactly (steps and ones)"
          % (good, cases))
    N = 2 ** 63 - 1
    print("blank tape reaches S1(3,7,2,6,63) at step", 821 + ticks(6))
    print("first epoch ends at step",
          27965 + 12 * 6 + 3 * 63 + 63 + 4 * 2 + ticks(63))
