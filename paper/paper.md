# The Resolved-Face Crown of the Dual-Rail Carrier: Self-Dual Completeness, the Exact Count, and One-Constant Completion

**Won Chul Yang** — Independent Researcher, Seoul, Republic of Korea — wcy0969@gmail.com

*Public edition v1.0 (2026). Companion note to* The Price of NOT on D4
*(Paper II, DOI: 10.5281/zenodo.21800033): it proves in full the two crown
facts that Paper II's Appendix A.4–A.5 uses as boundary context and
attributes to a companion line. Every headline result is machine-verified
in dependency-minimal Lean 4 (core only; no mathlib; no `native_decide`;
no `sorry`; kernel axiom profile at most `[propext, Quot.sound]`).*

**Abstract.** On the four-state dual-rail carrier D4 with closed core
G = Clo{∧_k, ∨_k, P}, consider the resolved face R = {FAL, TRU} and the
outer fragment G|_R of R-valued restrictions of closed-core terms on Rⁿ.
We prove the crown theorem: G|_R^(n) is exactly the set of P-equivariant
maps Rⁿ → R — equivalently, under the Boolean reading of the face, exactly
the self-dual Boolean functions of arity n. The count is therefore
2^(2^(n−1)): the diagonal P-action on Rⁿ is free, and an equivariant map
freely chooses one output per orbit. The self-dual reading corrects a
natural miscount: 2ⁿ counts per-coordinate routing data, not functions —
odd-arity majority is self-dual and lies in the crown, while AND, OR, and
both constants do not. We then prove one-constant completion: adjoining a
single resolved constant to the crown realizes every map Rⁿ → R, by an
explicit self-dualization with one guard variable. Finally we record why
the crown is a genuinely dual-rail (single-orbit) phenomenon: for resolved
faces with two or more P-orbits, P-equivariance strictly over-approximates
the outer fragment, witnessed by an explicit unary counterexample.

**Keywords:** clone theory; self-dual Boolean functions; dual-rail
carriers; equivariant maps; functional completeness; Lean 4.

**MSC 2020:** 03B50, 06D30, 08A40, 94C10.

---

## 1 Introduction

The companion paper [5] studies the four-state dual-rail carrier
D4 = {UNK, FAL, TRU, CON} with closed core G = Clo{∧_k, ∨_k, P} and proves
the exact negation-complexity law ν(f) = dec(f) on the resolved face
R = {FAL, TRU} after the confinement-breaking operation σ_s is adjoined.
Before σ_s enters, the closed core already induces an *outer fragment* on
the resolved face: the family

G|_R^(n) = { t|_{Rⁿ} : t an n-ary term of G, t(Rⁿ) ⊆ R }

of R-valued restrictions of closed-core terms. Paper II's Appendix A.4–A.5
uses two facts about this fragment as boundary context — that it consists
exactly of the P-equivariant maps and has cardinality 2^(2^(n−1)), and
that one adjoined resolved constant completes it to all maps Rⁿ → R —
attributing both to a companion line. This note is that companion: it
states and proves both facts in full, together with the structural reading
that makes them stable, and it machine-verifies the results in Lean 4 on
top of the published mechanization of [5].

Three points deserve emphasis.

**The self-dual reading.** Under the Boolean encoding TRU = 1, FAL = 0 of
the face, P acts as negation, and P-equivariance of h : Rⁿ → R becomes
h(¬x) = ¬h(x): the crown is exactly the clone-theoretic class of
*self-dual* Boolean functions [3, 2]. This immediately calibrates what the
crown does and does not exclude: AND, OR, and the constants are not
self-dual and are excluded; odd-arity majority *is* self-dual and is
included, realized inside the carrier as orbit-dependent routing
(Proposition 4.1 gives the explicit ternary-majority term). In
particular, the correct count of the crown is the count of self-dual
functions, 2^(2^(n−1)) — not 2ⁿ, which counts per-coordinate routing data
rather than functions; at n = 3 the crown has 16 elements, including
majority, against 8 = 2³ (Remark 4.2).

**The two-layer proof.** Necessity is inherited: closed-core terms are
P-equivariant on all of D4ⁿ by the qualitative soundness theorem of [5],
so their R-valued restrictions are P-equivariant on the face. Sufficiency
is where the dual-rail geometry enters: inside the ambient Boolean cube
{0,1}^(2n) of rail bits, the face Rⁿ is a one-hot *antichain*, so any
labeling of it extends monotonically to the full cube; the resulting
positive (negation-free) Boolean formula lifts to a closed-core term by
the rail-swap normal form of [5], and on the face the lifted term
reproduces the given equivariant map. No step uses σ_s.

**The boundary.** The crown is a single-orbit phenomenon. On resolved
faces with two or more P-orbits, a resolved value carries both a
within-pair bit and an orbit label; P-equivariance constrains only the
former, while closed-core terms are confined to orbits. Section 6 records
the minimal unary counterexample. This is why the crown theorem is stated
for the dual-rail carrier and claimed for nothing larger.

Everything below is machine-verified (Section 7); the Lean development
extends the published artifact of [5] and builds with kernel axiom profile
at most `[propext, Quot.sound]`.

## 2 Preliminaries

We use the setting of [5, §2]. D4 = {UNK, FAL, TRU, CON} is identified
with {0,1}² via UNK = (0,0), FAL = (0,1), TRU = (1,0), CON = (1,1); the
knowledge order is the componentwise order; ∧_k and ∨_k are componentwise
meet and join; P is rail swap, P(a,b) = (b,a). The closed core is
G = Clo{∧_k, ∨_k, P}. The resolved face is R = {FAL, TRU}, on which P
restricts to the transposition exchanging FAL and TRU.

**Boolean reading of the face.** Encode TRU = 1, FAL = 0. Then P|_R = ¬,
and a map h : Rⁿ → R is P-equivariant — h(Px₁, …, Pxₙ) = P h(x₁, …, xₙ)
— exactly when its Boolean form satisfies h(¬x) = ¬h(x), i.e. when h is
**self-dual** [3, 2].

**Rail bits and the one-hot face.** Writing x_i = (p_i, q_i) and
bits(x) = (p₁, q₁, …, pₙ, qₙ) ∈ {0,1}^(2n), a point x lies in Rⁿ exactly
when each pair (p_i, q_i) is one-hot: p_i + q_i = 1. Let S denote the
rail swap on bit tuples (exchanging each p_i ↔ q_i). On the face,
S(bits(x)) = bits(Px).

We use one published fact from [5], machine-verified there:

- **(E)** (Theorem 2.1 of [5], qualitative closed-core soundness): every
  term operation of G is monotone for the knowledge order, preserves both
  endpoints, and is P-equivariant on D4ⁿ.

We also use the elementary evaluation table of the internal operations on
resolved and endpoint values (all immediate from the componentwise
definitions, and machine-checked in the present artifact): for r, r′ ∈ R,

TRU ∧_k TRU = TRU, FAL ∧_k FAL = FAL, TRU ∧_k FAL = UNK,
TRU ∨_k UNK = TRU, FAL ∨_k UNK = FAL, UNK ∧_k v = UNK,
UNK ∨_k UNK = UNK,

together with P-equivariance of ∧_k, ∨_k and P(FAL) = TRU.

## 3 The Crown Theorem

**Theorem 3.1** (crown; self-dual completeness of the outer fragment).
*For every arity n ≥ 1,*

G|_R^(n) = { h : Rⁿ → R | h is P-equivariant }
= { self-dual Boolean functions of arity n }.

*Proof.* The second equality is the Boolean reading of Section 2. We
prove the first.

(⊆) Let t be an n-ary closed-core term with t(Rⁿ) ⊆ R. By (E), t is
P-equivariant on D4ⁿ; restricting to Rⁿ (which is P-invariant) gives a
P-equivariant map Rⁿ → R.

(⊇) Let h : Rⁿ → R be P-equivariant. First, h attains the value TRU:
P-equivariance gives h(Px⃗) = P h(x⃗) ≠ h(x⃗), so h is nonconstant, and
a map into R that is nonconstant attains both values. Let
A = { y ∈ Rⁿ : h(y) = TRU }; A is nonempty, and P(A) is exactly the set
where h = FAL (equivariance), so A contains no P-pair: y ∈ A ⟹
Py ∉ A.

For each y ∈ A define the **orbit-literal minterm**

M_y(x⃗) = ⋀_k { ℓ₁(x₁), …, ℓₙ(xₙ) },  where ℓᵢ(xᵢ) = xᵢ if yᵢ = TRU,
and ℓᵢ(xᵢ) = Pxᵢ if yᵢ = FAL,

a closed-core term (only ∧_k and P occur). Evaluate M_y on a face point
z⃗ ∈ Rⁿ. Each literal value ℓᵢ(zᵢ) is resolved, and equals TRU exactly
when zᵢ = yᵢ. On resolved values the componentwise meet satisfies
TRU ∧_k TRU = TRU, FAL ∧_k FAL = FAL, and TRU ∧_k FAL = UNK, with UNK
absorbing (UNK ∧_k v = UNK). Hence:

- if z⃗ = y⃗, every literal is TRU and M_y(z⃗) = TRU;
- if z⃗ = Py⃗, every literal is FAL and M_y(z⃗) = FAL;
- otherwise the literals are mixed and M_y(z⃗) = UNK.

Now set t = ⋁_k { M_y : y ∈ A } (a join over the nonempty family A;
again a closed-core term). Evaluate t on z⃗ ∈ Rⁿ:

- if h(z⃗) = TRU, then z⃗ ∈ A, so the minterm M_{z⃗} contributes TRU;
  every other y ∈ A has y ≠ z⃗ and also Py ≠ z⃗ (else z⃗ = Py with
  y ∈ A, so h(z⃗) = h(Py) = P h(y) = FAL, contradiction), so every other
  minterm contributes UNK. Since TRU ∨_k UNK = TRU and
  UNK ∨_k UNK = UNK, the join is TRU = h(z⃗).
- if h(z⃗) = FAL, then Pz⃗ ∈ A, so the minterm M_{Pz⃗} evaluates at z⃗
  = P(Pz⃗) to FAL; every other y ∈ A has y ≠ z⃗ (as h(y) = TRU) and
  y ≠ Pz⃗, so every other minterm contributes UNK. Since
  FAL ∨_k UNK = FAL and no minterm contributes TRU (that would require
  z⃗ ∈ A), the join is FAL = h(z⃗).

In both cases t(z⃗) = h(z⃗) ∈ R. Hence t|_{Rⁿ} = h with t(Rⁿ) ⊆ R, so
h ∈ G|_R^(n). ∎

**Remark 3.2.** The construction realizes h with a term whose only
generators are ∧_k, ∨_k, P — one orbit-literal minterm per TRU-point of
h. An alternative route extends the face labeling monotonically through
the ambient rail cube (the face is a one-hot antichain in {0,1}^(2n)) and
lifts the resulting positive formula; the direct construction above is
the one mechanized.

**Theorem 3.3** (the exact count). *For every n ≥ 1,*

|G|_R^(n)| = 2^(2^(n−1)).

*Proof.* By Theorem 3.1 it suffices to count P-equivariant maps
h : Rⁿ → R. The diagonal P-action on Rⁿ is free: P has no fixed point on
R, so Px⃗ = x⃗ is impossible already in the first coordinate. Hence Rⁿ
(of size 2ⁿ) splits into 2^(n−1) orbits of size two; each orbit has a
unique representative with first coordinate TRU. A P-equivariant h is
freely determined by its values on the 2^(n−1) representatives — the
value on the partner point is forced to be the P-image — and every such
assignment defines an equivariant map. This is a bijection between
G|_R^(n) and the set of maps from the 2^(n−1) representatives to R, of
cardinality 2^(2^(n−1)). ∎

For n = 1, 2, 3, 4, 5 the counts are 2, 4, 16, 256, 65 536.

## 4 What the Crown Contains — and the Corrected Count

**Proposition 4.1** (calibration). *Under the Boolean reading:*

1. *AND, OR, and both constants do not lie in G|_R (none is self-dual;
   constants are moreover not P-equivariant).*
2. *Odd-arity majority lies in G|_R. Explicitly, for n = 3, with the
   agreement detectors*

   D_same(x, y) = (x ∧_k y) ∨_k (Px ∧_k Py),
   D_opp(x, y) = D_same(x, Py),

   *which are E-valued on R² (E = {UNK, CON}) with D_same = CON iff
   x = y, and D_opp = CON iff x = Py, the term*

   MAJ₃(x₁, x₂, x₃) =
   (x₁ ∧_k (D_same(x₁,x₂) ∨_k D_same(x₁,x₃)))
   ∨_k (Px₁ ∧_k (D_opp(x₁,x₂) ∧_k D_opp(x₁,x₃)))

   *is a closed-core term whose restriction to R³ is ternary majority.*

*Proof.* (1) f(¬x) = ¬f(x) fails for AND at x = (1,0) (AND self-dual
would force AND(0,1) = ¬AND(1,0), i.e. 0 = ¬0), and dually for OR;
constants c satisfy Pc ≠ c on R, so P-equivariance fails at once.
(2) Majority of odd arity satisfies MAJ(¬x₁, …, ¬x_m) = ¬MAJ(x₁, …, x_m)
(complementing all inputs complements the strict majority), so it is
self-dual and lies in the crown by Theorem 3.1. For the explicit term:
on resolved inputs the detectors are E-valued as stated, by direct
evaluation of the four resolved pairs (this is Proposition A.1 of [5]).
On E, ∧_k and ∨_k act as Boolean AND/OR with CON = true, UNK = false.
The first branch is active (its guard is CON) exactly when x₂ = x₁ or
x₃ = x₁, in which case the majority value is x₁; the second branch is
active exactly when both x₂ ≠ x₁ and x₃ ≠ x₁, in which case the majority
value is Px₁. On R², the guard values UNK and CON absorb correctly:
UNK ∧_k r = UNK, CON ∧_k r = r, and r ∨_k UNK = r, so the inactive branch
contributes UNK and the active branch passes its routed value through.
Exhaustive evaluation over R³ (machine-checked; Section 7) confirms the
restriction is majority. ∎

**Remark 4.2** (the corrected count: routing data versus functions). A
natural first count of the crown reads each coordinate as carrying an
independent forward/backward routing choice and arrives at 2ⁿ. That
figure counts *routing data*, not functions: already at n = 3 the crown
contains 16 functions (Theorem 3.3) — including ternary majority
(Proposition 4.1), which is not of the form x⃗ ↦ x_i or x⃗ ↦ Px_i for
any fixed i — strictly more than 2³ = 8. An earlier internal manuscript
in the author's series stated the 2ⁿ figure for this fragment; the
present note supersedes it. The stable statement is Theorem 3.1: the
crown is self-dual completeness, and its size is the size of the
self-dual class.

## 5 One-Constant Completion

**Theorem 5.1** (one resolved constant completes the outer fragment).
*Fix either resolved constant, say c = FAL. For every map g : Rⁿ → R
(not necessarily equivariant) there exist a P-equivariant map
ĝ : R^(n+1) → R and a term realization*

g(x⃗) = ĝ(c, x⃗),

*where ĝ ∈ G|_R^(n+1) by Theorem 3.1. Hence the clone generated on the
face by G|_R together with the constant c contains all 2^(2^n) maps
Rⁿ → R.*

*Proof.* In the Boolean reading (c = 0), define the self-dualization of
g with one guard variable:

ĝ(x₀, x⃗) = g(x⃗) if x₀ = 0, and ¬g(¬x⃗) if x₀ = 1.

ĝ is self-dual: complementing all n+1 arguments swaps the two branches
and complements the output —

ĝ(¬x₀, ¬x⃗) = g(¬x⃗) if x₀ = 1, and ¬g(x⃗) if x₀ = 0,

which in both cases equals ¬ĝ(x₀, x⃗). Specializing the guard to the
constant 0 gives ĝ(0, x⃗) = g(x⃗). By Theorem 3.1, ĝ is the restriction
of a closed-core term t of arity n+1; substituting the constant c for the
guard slot of t (a composition in the clone generated by G|_R ∪ {c})
realizes g on Rⁿ. The count 2^(2^n) is the number of all maps Rⁿ → R. ∎

**Remark 5.2.** Theorem 5.1 is the zero/one accessibility contrast used
by [5, Appendix A.5]: without constants the outer fragment is the proper
self-dual class; a single resolved constant jumps it to everything. (In
clone-theoretic terms this reflects the maximality of the self-dual clone
in Post's lattice [3]; the proof above is self-contained and does not
invoke the classification.)

## 6 Sharpness: the Crown Is a Single-Orbit Phenomenon

**Remark 6.1** (failure for larger resolved faces). Suppose the resolved
face has 2k ≥ 4 elements, R = O₁ ⊔ ⋯ ⊔ O_k with P-pairs O_i = {a_i, b_i}.
A resolved value now carries two pieces of information: the within-pair
bit and the orbit label. P-equivariance constrains only the former.
Closed-core terms, however, are orbit-confined: a unary term evaluated at
a resolved r can output only values in {r, Pr} together with the
endpoints, because the generators ∧_k, ∨_k, P cannot manufacture an
absolute orbit label from a single input. Concretely, on the six-element
flat carrier with R = {a, b, c, d}, P(a) = b, P(c) = d, the unary map

h(a) = a, h(b) = b, h(c) = a, h(d) = b

(extended by fixing the endpoints) is monotone, endpoint-preserving, and
P-equivariant, yet no closed-core term restricts to it: unary closed-core
terms act in one of the four global modes x, Px, x ∧_k Px, x ∨_k Px, and
none maps c into {a, b}. Hence for |R| ≥ 4, P-equivariance strictly
over-approximates the outer fragment, and the correct description is a
routing/signature theory rather than the crown. The crown theorem is
therefore stated here only for the dual-rail carrier, where R is a single
P-orbit and the two notions coincide.

## 7 Mechanization

The note ships with a Lean 4 development that extends the published
artifact of [5] (core Lean 4 only; no mathlib; no `native_decide`; no
`sorry`; toolchain pinned; kernel axiom profile at most
`[propext, Quot.sound]`):

- **necessity** — the restriction of any closed-core term to the face is
  P-equivariant: immediate from the mechanized Theorem 2.1 of [5]
  (`cterm_equivariant`);
- **sufficiency** — for every P-equivariant Boolean h, an explicit
  closed-core term whose restriction is h: the orbit-literal minterm
  construction of Theorem 3.1, with the resolved/endpoint evaluation
  table machine-checked;
- **the count** — the explicit bijection between P-equivariant maps and
  assignments on the 2^(n−1) first-coordinate-TRU representatives;
- **calibration** — majority ∈ crown at n = 3 with the explicit term of
  Proposition 4.1 (kernel `decide` over the 8-point face), and
  AND/OR/constant exclusion;
- **one-constant completion** — the self-dualization ĝ, its
  self-duality, and the guard specialization ĝ(0, x⃗) = g(x⃗).

An independent replay script exhaustively checks the finite claims
(detector tables, the majority term over R³, the n ≤ 4 counts by brute
force over equivariant assignments, and the M₆ counterexample of
Remark 6.1). The frozen output ships alongside.

## References

1. Yu. I. Janov, A. A. Muchnik. *On the existence of k-valued closed
   classes without a finite basis.* Doklady Akademii Nauk SSSR,
   127:44–46, 1959.
2. Dietlinde Lau. *Function Algebras on Finite Sets.* Springer, 2006.
   doi:10.1007/3-540-36023-9.
3. Emil L. Post. *The Two-Valued Iterative Systems of Mathematical
   Logic.* Princeton University Press, 1941. doi:10.1515/9781400882366.
4. Ivo G. Rosenberg. *Complete sets of operations for finite algebras.*
   Mathematische Nachrichten, 44(1–6):253–258, 1970.
   doi:10.1002/mana.19700440120.
5. Won Chul Yang. *The Price of NOT on D4.* Public edition v1.0, 2026.
   DOI: 10.5281/zenodo.21800033.
   https://github.com/ycmath/price-of-not-on-d4
6. Won Chul Yang. *Finite-Energy Epistemic Logic with Conservative
   Pointed Extension and Negation Geometry.* Public edition v1.0, 2026.
   DOI: 10.5281/zenodo.21800031.

---

## Authorship & provenance

Won Chul Yang, independent researcher. The mathematics of this note is
the author's, developed inside the author's dual-rail carrier programme
around Papers I–II; AI assistance (Anthropic Claude family) was used for
the Lean 4 mechanization, the machine replay, and the preparation of the
manuscript, with the Lean 4 kernel as the acceptance gate for the
verification layer. Remark 4.2 records a self-correction of the author's
series: an earlier internal manuscript stated the 2ⁿ count; the corrected
function count 2^(2^(n−1)) is proved here. Corrections are invited.

Licenses: Apache-2.0 (Lean artifacts and verification scripts),
CC BY 4.0 (text).
