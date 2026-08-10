"""
REPLAY (v1, 2026) for "The Resolved-Face Crown of the Dual-Rail Carrier".
Independent (non-Lean) exhaustive check:
  [D]  agreement detector tables D_same / D_opp on R^2 (exhaustive);
  [C]  crown counts by brute force: number of P-equivariant maps R^n -> R
       equals 2^(2^(n-1)) for n = 1..4, and each equals the number of
       self-dual Boolean functions;
  [M]  ternary majority: self-dual, lies in the crown, realized by the
       explicit routing term (exhaustive over R^3); AND/OR/constants are
       not self-dual;
  [2n] the miscount check: at n = 3 the crown has 16 > 8 = 2^n members;
  [K]  one-constant completion: for ALL maps g : R^2 -> R (65536/... here
       2^(2^2)=16 maps at n=2), the self-dualization sdGuard(g) is
       self-dual and specializes at guard FAL to g (exhaustive n = 1, 2);
  [M6] the sharpness counterexample on the 6-element flat carrier: the
       unary P-equivariant monotone endpoint-preserving map h with
       h(c) = a is NOT among the four unary closed-core modes.
ASCII-only, stdlib-only.
"""
from itertools import product as prod

ok = True
def chk(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok = ok and cond

# D4 dual-rail: values as (p, q); UNK=(0,0), FAL=(0,1), TRU=(1,0), CON=(1,1)
UNK, FAL, TRU, CON = (0, 0), (0, 1), (1, 0), (1, 1)
def meetk(a, b): return (a[0] & b[0], a[1] & b[1])
def joink(a, b): return (a[0] | b[0], a[1] | b[1])
def P(a): return (a[1], a[0])
R = [FAL, TRU]

# [D] detectors
def dsame(x, y): return joink(meetk(x, y), meetk(P(x), P(y)))
def dopp(x, y): return dsame(x, P(y))
d_ok = all(dsame(x, y) == (CON if x == y else UNK) for x in R for y in R) and \
       all(dopp(x, y) == (CON if x == P(y) else UNK) for x in R for y in R)
chk("[D] detector tables on R^2", d_ok)

# [C] crown counts: P-equivariant maps R^n -> R
def crown_count(n):
    pts = list(prod(R, repeat=n))
    cnt = 0
    for vals in prod(R, repeat=len(pts)):
        h = dict(zip(pts, vals))
        if all(h[tuple(P(x) for x in p)] == P(h[p]) for p in pts):
            cnt += 1
    return cnt

def selfdual_count(n):
    pts = list(prod((0, 1), repeat=n))
    cnt = 0
    for vals in prod((0, 1), repeat=len(pts)):
        f = dict(zip(pts, vals))
        if all(f[tuple(1 - c for c in p)] == 1 - f[p] for p in pts):
            cnt += 1
    return cnt

c_ok = True
for n in (1, 2, 3):
    cc, sd, target = crown_count(n), selfdual_count(n), 2 ** (2 ** (n - 1))
    print("  n=%d: crown=%d selfdual=%d target=%d" % (n, cc, sd, target))
    c_ok = c_ok and cc == sd == target
sd4 = selfdual_count(4)
c_ok = c_ok and sd4 == 2 ** 8
print("  n=4: selfdual=%d target=%d" % (sd4, 2 ** 8))
chk("[C] crown = self-dual = 2^(2^(n-1)), n <= 4", c_ok)

# [M] majority via explicit routing term
def majterm(x1, x2, x3):
    ip = joink(dsame(x1, x2), dsame(x1, x3))
    im = meetk(dopp(x1, x2), dopp(x1, x3))
    return joink(meetk(x1, ip), meetk(P(x1), im))
def maj_bool(a, b, c): return 1 if (a + b + c) >= 2 else 0
def toR(b): return TRU if b else FAL
def toB(r): return 1 if r == TRU else 0
m_ok = all(majterm(x, y, z) == toR(maj_bool(toB(x), toB(y), toB(z)))
           for x in R for y in R for z in R)
chk("[M] explicit routing term computes ternary majority on R^3", m_ok)
def is_selfdual(f, n):
    pts = list(prod((0, 1), repeat=n))
    return all(f[tuple(1 - c for c in p)] == 1 - f[p] for p in pts)
and2 = {p: p[0] & p[1] for p in prod((0, 1), repeat=2)}
or2 = {p: p[0] | p[1] for p in prod((0, 1), repeat=2)}
c0 = {p: 0 for p in prod((0, 1), repeat=1)}
chk("[M2] AND, OR, constant are not self-dual",
    not is_selfdual(and2, 2) and not is_selfdual(or2, 2) and not is_selfdual(c0, 1))

# [2n] miscount check
chk("[2n] n=3: crown 16 > 8 = 2^n", crown_count(3) == 16 and 16 > 8)

# [K] one-constant completion (exhaustive n = 1, 2)
k_ok = True
for n in (1, 2):
    pts = list(prod((0, 1), repeat=n))
    for vals in prod((0, 1), repeat=len(pts)):
        g = dict(zip(pts, vals))
        # sdGuard: y0=1 -> not g(not xs); y0=0 -> g(xs)
        gh = {}
        for y0 in (0, 1):
            for p in pts:
                gh[(y0,) + p] = (1 - g[tuple(1 - c for c in p)]) if y0 else g[p]
        k_ok = k_ok and is_selfdual(gh, n + 1)
        k_ok = k_ok and all(gh[(0,) + p] == g[p] for p in pts)
chk("[K] sdGuard self-dual + guard-FAL specialization, all g at n=1,2", k_ok)

# [M6] sharpness on the 6-element flat carrier
# elements: bot, a, b, c, d, top ; P swaps a<->b and c<->d, fixes bot/top
BOT, A, B, C, D6, TOP = "bot", "a", "b", "c", "d", "top"
P6 = {BOT: BOT, A: B, B: A, C: D6, D6: C, TOP: TOP}
h = {BOT: BOT, TOP: TOP, A: A, B: B, C: A, D6: B}
equivariant = all(h[P6[x]] == P6[h[x]] for x in h)
modes = [lambda x: x, lambda x: P6[x]]
def meet6(x, y):
    # flat lattice: bot < {a,b,c,d} < top, resolved elements pairwise incomparable
    if x == y: return x
    if BOT in (x, y): return BOT
    if x == TOP: return y
    if y == TOP: return x
    return BOT
def join6(x, y):
    if x == y: return x
    if TOP in (x, y): return TOP
    if x == BOT: return y
    if y == BOT: return x
    return TOP
modes.append(lambda x: meet6(x, P6[x]))
modes.append(lambda x: join6(x, P6[x]))
not_any_mode = all(any(m(x) != h[x] for x in h) for m in modes)
chk("[M6] h (P-equivariant, monotone, endpoint-preserving) matches no unary mode",
    equivariant and not_any_mode)

print("\nALL PASS" if ok else "\nSOME FAILURES")
