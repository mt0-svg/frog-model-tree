# Certificate format

The certificate of Section 7 of the paper is two plain text files: the table, in version 3 (`code/certificate/table.cert`), and the data of the backward check, in version 4 (the release asset `frog-model-tree-certificate.v4.zst`, compressed with zstd). The conditions (I1) to (I5) below are named as in the comments of the Lean files. The paper states the conditions on the table as (C1) and (C2) (Section 6) and the checks on the data as (C3) to (C7) (Section 6.6).

## Lines

One record per line, tokens separated by spaces. Empty lines and lines starting with `#` are ignored. Numbers are exact: a nonnegative integer, or a rational `a/b` with decimal integers a and b (no sign, no exponent, no decimal point).

| keyword  | arguments                              | meaning                                                                                                                                                              |
| -------- | -------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `d`      | integer                                | branching number of the tree; default 4                                                                                                                              |
| `J`      | integer                                | block length, J >= 2 for a certificate                                                                                                                               |
| `T`      | integer                                | truncation: the finite part lives on F_T = {B nondecreasing, B(1) >= 0, B(J) \<= T}                                                                                  |
| `Tpend`  | integer                                | pending cap T' >= T: a move that leaves more than T' frogs waiting at the root is stopped; default T                                                                 |
| `eps`    | rational                               | tail mass, 0 \<= eps < 1                                                                                                                                             |
| `rho`    | rational                               | geometric ratio of the tail atoms, 0 < rho < 1                                                                                                                       |
| `phi`    | rational                               | phi > 1                                                                                                                                                              |
| `kappa`  | rational                               | kappa > 1                                                                                                                                                            |
| `plan`   | J integers, J integers, rational       | `plan x(1) ... x(J) y(1) ... y(J) a`: mass a of the atom y of H\* is filled from the atom x (condition (I4))                                                         |
| `label`  | integer, name                          | version 3: `label q NAME` declares a label at level q, 1 \<= q \<= J - 1; level 0 has the single label `root`, level J the single label `end`                        |
| `tr`     | integer, name, integer, name, rational | version 3: `tr q S DELTA S2 P`: from label S at level q, with probability P > 0, the increment B(q + 1) - B(q) is DELTA >= 0 and the next label is S2 at level q + 1 |
| `rounds` | integer                                | round cap of a forward computation of the root chain, not used by version 4; default 400                                                                             |
| `prune`  | rational                               | mass threshold of a forward computation of the root chain, not used by version 4; default 0                                                                          |

`d`, `J` and `T` come before the `label`, `tr` and `plan` lines. P_tab is the law of B(q) = DELTA_1 + ... + DELTA_q along the label paths from `root` to `end` (the probability of a path is the product of its P), and h(B) = (1 - eps) P_tab(B). The certificate law is

H\* = sum over the atoms B of P_tab of h(B) delta_B + eps sum\_{t > T} (1 - rho) rho^{t - T - 1} delta\_{(t, ..., t)}.

The atoms of the finite part are the support of P_tab; they need not lie in F_T.

## Conditions on the table

- (I1) sum h + eps = 1 exactly, every mass >= 0, J >= 2, eps in \[0, 1), rho in (0, 1), phi > 1, kappa > 1, and the table is well formed: every label declared once, at a level in 1 to J - 1, not named `root` or `end`; every `tr` line from a label of its level to a label of the next level, P > 0, DELTA >= 0, no repeated (q, S, DELTA, S2); the P of every (q, S) sum to 1 exactly; `root` and every target label below level J have transitions.
- (I2) phi rho < 1, kappa^J >= M, theta rho >= 1, with M = sum h(B) phi^{B(J)} + eps (1 - rho) phi^\{T+1} / (1 - phi rho) and theta = (d + 1) phi - d kappa.
- (I3) bounds the part of the output that the check stops: (I3b) is item 6 of version 4 below, and (I3a), that this part has mass at most eps, follows from (I4).
- (I4), dual form, for a measure L on F_T defined by the data (item 7 of version 4). Every plan entry has a >= 0, x in F_T, y an atom of H\*, and x \<= y componentwise. Every atom y of H\* is filled: sum_x a(x, y) >= h(y). No atom x is overdrawn: sum_y a(x, y) \<= L(x); a source that is not an atom of L has L(x) = 0. The slack is positive, so a plan computed in floating point against a slightly lowered L can pass.
- (I5) c = sum h(B) B(1) + eps (T + 1 + rho / (1 - rho)) < 1, where sum h(B) B(1) = (1 - eps) E_tab B(1), the sum over the `root` lines of P DELTA.

A checker may also decide (I4) by its own exact max flow from the atoms of H\* into L, along the edges y to x for x \<= y. (I4) holds if and only if that flow equals sum h.

## Version 4: the backward certificate of a lumped chain

A version 4 certificate checks (I3b) and (I4) of a version 3 table without a forward computation of the root chain, by Theorem 6.5 of the paper, backward in every phase. It is a version 3 table file plus a data file. The checker generates every move and every stop of every state from the table and the state itself. It reads from the data only the states, one flag per state, the values and the plan. Everything below is exact; the only roundings are the ones defined in "Rounding".

### Objects derived from the table

1. Child states, in this order: `F`, `B` (the boundary), `q:S` for q = 1, ..., J - 1 and the labels S of level q in the order of their `label` lines, `q:tail` for q = 1, ..., J - 1, `q:M` for q = 1, ..., J - 1. The names are the ones used in the data file.
2. Rows. The rows of `F`, `B`, `q:S` and `q:tail` are those of the child chain of Section 6.2 of the paper, with the tail atoms of `F` and `B` apart (they are moves of their own, below). From `F`: for every pair of lines `tr 0 root DELTA1 S1 P1` and `tr 1 S1 DELTA2 S2 P2`, the transition ((1 - eps) P1 P2, DELTA1 + DELTA2, `2:S2`). From `B`: for every line `tr 0 root DELTA1 S1 P1`, the transition ((1 - eps) P1, DELTA1, `1:S1`). From `q:S`: its `tr` lines. From `q:tail`: the transition (1, 0, `(q+1):tail`). A next state of level J is read as `B`. `q:M`, the max chain of level q: for k >= 0 let tau_q(k) be the largest, over the labels S of level q, of the sum of P over the lines `tr q S DELTA S2 P` with DELTA >= k (so tau_q(0) = 1). The row of `q:M` has the transitions (tau_q(k) - tau_q(k + 1), k, `(q+1):M`) for the k with tau_q(k) > tau_q(k + 1), with `J:M` read as `B`.
3. Lump: `q:S` to `q:M`; every other child state is fixed. The lump of a multiset is taken element by element.
4. Potentials: w(F) = kappa^J, w(B) = kappa^\{J-1}, w(`q:S`) = kappa^\{q-1} r_q(S), where r_J(end) = 1 and r_q(S) is the sum over the lines `tr q S DELTA S2 P` of P phi^DELTA r\_\{q+1}(S2), w(`q:tail`) = kappa^\{q-1}, w(`q:M`) = kappa^\{q-1} r_q(M), where r_q(M) = sum_k (tau_q(k) - tau_q(k + 1)) phi^k r\_\{q+1}(M) and r_J(M) = 1. theta = 5 phi - 4 kappa.
5. States: s = (q, sigma, p) with 1 \<= q \<= J, sigma a multiset of four child states, 1 \<= p \<= T'. The start is s_0 = (1, {F, F, F, F}, 1).
6. Compositions: C_q is the set of vectors x = (x_q, ..., x_J) of nonnegative integers with x_q + ... + x_J \<= T, in lexicographic order with x_q the most significant coordinate. |C_q| = binom(T + J - q + 1, J - q + 1), and C\_\{J+1} = {()}.

### Moves and stops of a state

Let s = (q, sigma, p), m_c the multiplicity of the child state c in sigma, and sigma[c to c'] the multiset with one c replaced by c'. A move has an exact weight omega > 0, an exit flag f in {0, 1} and a reached pair (sigma', p'):

- the exit: omega = 1/5, f = 1, (sigma, p - 1);
- for every distinct c in sigma and every transition (P, DELTA, c') of the row of c: omega = m_c P / 5, f = 0, (sigma[c to c'], p - 1 + DELTA);
- for c in {F, B} in sigma and every tail atom t with T + 1 \<= t \<= T' - p + 1: omega = m_c eps (1 - rho) rho^\{t-T-1} / 5, f = 0, (sigma[c to c_t], p - 1 + t), where c_t = `2:tail` for c = F (`B` if J = 2) and c_t = `1:tail` for c = B.

The outcome of a move, tested in this order:

- if p' > T' (only when f = 0): a stop, of weight omega phi^{p' + J - q} prod over sigma' of w;
- else if p' = 0 and q = J: absorbed;
- else the reached state is t = (q, sigma', p') if p' >= 1, or t = (q + 1, sigma', 1) if p' = 0 (the next frog starts). The target of the move is t if t is a state of the data with flag 1, and otherwise (q_t, lump(sigma'), p_t), where (q_t, p_t) are the phase and pending of t. The target must be a state of the data.

The other stops of s:

- the exit stop at budget 0 (the exit is the (T + 1)-th one): weight (1/5) theta phi^{p - 1 + J - q} prod over sigma of w;
- for every c in {F, B} in sigma, the tail atoms t >= t_0 = max(T + 1, T' - p + 2), taken together in closed form: weight (m_c / 5) eps (1 - rho) rho^{t_0 - T - 1} phi^\{t_0} / (1 - phi rho) x phi^{p - 1 + J - q} prod over sigma[c to c_t] of w.

### Rounding

For a rational y >= 0, y^- = floor(2^48 y) / 2^48 and y^+ = ceil(2^48 y) / 2^48, applied to the weight of every move separately (omega^- for V; omega^+ and (theta omega)^+ for W) and to the weight of every stop separately. An implementation may merge the moves of a state that have the same target and exit flag after rounding, since sums of rounded weights are exact. V' and W' are given on the grid 2^-40.

### Data file

Lexical rules as in "Lines" above.

| keyword        | arguments                        | meaning                                                                                                                                       |
| -------------- | -------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- |
| `version`      | `4`                              | first record                                                                                                                                  |
| `table`        | path                             | the version 3 table, relative to the data file                                                                                                |
| `table_sha256` | hex                              | sha256 of the table file                                                                                                                      |
| `state`        | K Q P H, then four names         | `state K Q P H C1 C2 C3 C4`: the state (Q, {C1, ..., C4}, P) has index K (0, 1, 2, ... in order) and flag H in {0, 1}; the names in any order |
| `V`            | K, then \|C_Q\| integers         | `V K N_1 ... N_n`: V'(K)[x] = N_i / 2^40 for the i-th composition x of C_Q                                                                    |
| `W`            | K, then T + 1 integers           | `W K N_0 ... N_T`: W'(K)[b] = N_b / 2^40, b the budget (exits still allowed before the stop by e > T)                                         |
| `plan`         | J integers, J integers, rational | as in "Lines", for (I4) with the L of item 7                                                                                                  |

No two `state` lines have the same (Q, multiset, P). Every state has exactly one `V` line and one `W` line, and s_0 is a state. The flag of a state whose multiset is its own lump does not matter.

### What a checker verifies

Items 3 to 7 correspond to the conditions (C3) to (C7) of Section 6.6 of the paper, with the weights rounded as in "Rounding".

1. The table: (I1), (I2) and (I5).
2. The data: the sha256 of the table; well-formed `state` lines (1 \<= Q \<= J, 1 \<= P \<= T', declared names, no duplicate); s_0 present; one `V` and one `W` line per state.
3. Closure: every move of every state that is neither a stop nor absorbed has its target among the states.
4. V, sub-solution. For every state s = (q, sigma, p) and every x in C_q: V'(s)[x] \<= sum over the moves mu of s of omega_mu^- v_mu(x), where v_mu(x) is
   - V'(t)[x - f e_q] if the target t is in phase q and x_q >= f (0 if x_q < f), e_q the unit vector of the coordinate x_q;
   - V'(t)[(x\_\{q+1}, ..., x_J)] if the move ends phase q < J (its target is in phase q + 1) and x_q = f, and 0 otherwise;
   - 1 if the move is absorbed (q = J) and x = (f), and 0 otherwise;
   - 0 if the move is a stop.
5. W, super-solution. For every state s and every b in {0, ..., T}: W'(s)[b] >= E(s, b) + sum over the moves mu with f = 0 that are not stops or absorbed of omega_mu^+ W'(t_mu)[b] + the sum of the rounded-up weights of the stops p' > T' and of the closed-form tails of s, where for the exit move with target t: E(s, b) = (theta / 5)^+ W'(t)[b - 1] if b >= 1 and the exit is not absorbed, 0 if b >= 1 and it is absorbed, and E(s, 0) = the rounded-up weight of the exit stop at budget 0.
6. (I3b): W'(s_0)[T] \<= eps theta^\{T+1}.
7. (I4) with L(B) := V'(s_0)[(B(1), B(2) - B(1), ..., B(J) - B(J - 1))] for B in F_T, and L(B) = 0 outside F_T: in the dual form, or by the checker's own exact max flow.

The certificate passes if and only if 1 to 7 hold. Then Phi_J(H\*) \<= H\* by Theorem 6.5 of the paper, and E X \<= c < 1 by Theorem 5.3. The roundings make the check stronger than the exact one: V' >= 0 and omega^- \<= omega give V' \<= b + K V' for the true kernel K of the redirected chain, and W' >= 0 with every stop present and rounded up gives W' >= c + K' W'. (I3a) follows from (I4); a checker may report 1 - |L| for information.

### Generator (informative)

1. Heavy pairs: the (multiset, p) of each phase whose summed occupation in the root chain without lumping, computed in floating point (`code/certificate/run_occupations.sh`), is at least HMIN; the flag of a state is 1 if its (multiset, p) is heavy.
2. R: search from s_0 along the targets.
3. V_num, W_num and Z (the expected number of steps of the scalar chain with the budget stop ignored, Z = 1 + K Z) by Gauss-Seidel from 0, phase J first, in floating point.
4. V' = max(0, floor(2^40 (V_num - eta Z))) with eta = 2^-39 (coordinatewise, Z(s) in every coordinate of s). W' = ceil(2^40 (W_num + eta' theta^b Z(s))) at (s, b), eta' at least the largest residual of W_num against the rounded-up right side of item 5, plus 2^-40 theta. The scalar Z does not work for W, whose exit carries the factor theta; theta^b Z does.
5. The plan: a floating-point flow from L into (1 + delta) h, with delta below the margin measured in floating point, rounded so that every receiver is filled exactly and no source is overdrawn.

For the certificate of the release (HMIN = 1e-7): 159786 states, 4.19e6 merged moves, 3.09e7 integers in the `V` and `W` lines (`code/certificate/out/gen.out`).

### Version 4 clarifications

These bind both the generator and every checker.

1. Rounding, no merge before it. Each move as listed under "Moves and stops" is rounded on its own: one move per (distinct child state c, `tr` line of the row of c), where for c = F a `tr` line of the row is one pair (root line, level-1 line), with weight m_c P / 5, one per tail atom t, and the exit. Two moves that reach the same target are still rounded separately; merging is allowed only after rounding. Each stop is rounded on its own in the same way.
2. d. Version 4 is written for d = 4: the factors 1/5, 5 phi - 4 kappa and the four children are fixed. A checker rejects a table with d other than 4 at item 1.
3. Item 7. If the data has `plan` lines, item 7 is decided by the plan in the dual form, so a failing plan fails item 7 even when a max flow would succeed. A checker also computes its own exact max flow and reports it. With no `plan` lines, the checker's own exact max flow decides.
4. Duplicate plan entries. Two `plan` lines with the same (x, y) are allowed; their amounts add.
5. Names. The derived names `F`, `B`, `q:tail` and `q:M` must not coincide with a table label: a table with a label named `tail`, `M`, `F` or `B`, or a name containing `:`, is rejected at item 2.
6. Slacks reported, all exact (also printed in floating point): item 4, the minimum over (s, x) of right side minus left side; item 5, the minimum over (s, b) of left side minus right side; item 6, eps theta^(T+1) - W'(s_0)[T] and the ratio W'(s_0)[T] / (eps theta^(T+1)); item 7, the minimum filling excess over receivers, the minimum undrawn mass over sources, and the leftover |L| - sum h.
7. Paths. The `table` path is relative to the directory of the data file.
