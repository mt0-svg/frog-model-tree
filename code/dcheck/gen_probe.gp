\\ The margins of the table of Proposition 15.2 of the paper: checks, in exact rationals, the inequalities of Section
\\ 14 on the 95 intervals of dcheck_m1_cert.gp and prints their smallest margins (the self-check line). It also writes
\\ them as Lean theorems under OUTDIR/Probe/, in the two forms below; the proof does not use them.
\\ FloatLib form (F*): sqrt, exp, log as Real functions, closed by FloatLib's `interval`.
\\ Rational form (R*, in ℝ by norm_num; Q*, the same in ℚ by decide +kernel): sqrt(mu) replaced by a rational s with mu <= s^2, the
\\ tilt bounds of the two binomial tails written as rational powers (exp(-1) <= 3/8 for the first).
\\ Per interval [ml, mh] with entry [J, D, a, b, a9]: k = a J, y = ceil(b k 3^(D-1)), k1 = a9 J,
\\ muD = mu_(ml+1-D)(1) = (ml + 3 - D)/3, mu1 = mu_ml(1) = (ml + 2)/3, co = 2/3 - J 3^-D,
\\ pD = 1 - ((2/5) muD + sqrt(muD)/2)/(muD - y), p1 = 1 - ((2/5) mu1 + sqrt(mu1)/2)/(mu1 - k1),
\\ t2 >= P(Bin(y, 3^(1-D)) < k) by the tilt at z = 2/3: exp(-y 3^(1-D)/3) (3/2)^(k-1), y 3^(1-D) = (3a/2) J,
\\ t3 >= P(Bin(k, 1/4) < J) by the tilt at z3 = 3/(a - 1): ((3 + z3)/4)^k z3^-(J-1), likewise t9 for k1, z9.
\\ (K1)  ((mh + J + 1)/3) ((1 - co pD)^(J+1) + t2 + t3) <= 1/50;
\\ slope (3/5)/3 <= (1/3 - 1/50)(1 - L1), L1 = 1 - S(p1) + t9, S(p) = 15/16 - (9/16)(1 - p) - (3/8)(1 - p)^2;
\\ base  ((3/5)(ml + 3) + J - 2)/3 <= (b1 + (1/3 - 1/50)(ml - m1))(1 - L1).
\\ Usage: gp -q dcheck_m1_cert.gp gen_probe.gp < /dev/null (from code/dcheck; writes out/probe/Probe/*.lean).
OUTDIR = "out/probe";
M(i) = my(f = sqrtint(sqrtint(16*10^(22 + i)))); (f + 1) \ 2;
if (M(3) != 1778279 || M(98) != 10^30 || #CERT != 95, error("interval data"));
TY = "ℝ";
q(x) = if (denominator(x) == 1, Str("(", x, " : ", TY, ")"), Str("(", numerator(x), " / ", denominator(x), " : ", TY, ")"));
squp(x) = (sqrtint(floor(x * 4^64)) + 1) / 2^64;
mkrow(t) =
{
  my(i = t + 2, c = CERT[t], J = c[1], D = c[2], a = c[3], b = c[4], a9 = c[5], ml = M(i), mh = M(i + 1));
  my(k = a*J, y = ceil(b*k*3^(D - 1)), k1 = a9*J);
  if (b*k*3^(D - 1) != y || (3*a/2)*J*3^(D - 1) != y, error("y not exact"));
  [i, J, D, a, a9, ml, mh, k, y, k1, (ml + 3 - D)/3, (ml + 2)/3, 2/3 - J/3^D, 3/(a - 1), 3/(a9 - 1), (3*a/2)*J/3]
}
rows = vector(95, t, mkrow(t));
pexpr(mu, x, form) = Str("(1 - (", q(2/5), " * ", q(mu), " + ", if(form == "F", Str("Real.sqrt ", q(mu)), q(squp(mu))), " / 2) / (", q(mu), " - ", q(x), "))");
tilt(n, z, J, form) =
{
  if (form == "F", Str("Real.exp (", q(n), " * Real.log ", q((3 + z)/4), " + ", q(J - 1), " * Real.log ", q(1/z), ")"),
    Str(q((3 + z)/4), " ^ ", n, " * ", q(1/z), " ^ ", J - 1))
}
t2expr(e, k, form) =
{
  if (form == "F", Str("Real.exp (-", q(e), " + ", q(k - 1), " * Real.log ", q(3/2), ")"),
    Str(q(3/8), " ^ ", e, " * ", q(3/2), " ^ ", k - 1))
}
k1expr(r, form) =
{
  my([i, J, D, a, a9, ml, mh, k, y, k1, muD, mu1, co, z3, z9, e2] = r);
  Str("(", q(mh + J + 1), " / 3) * ((1 - ", q(co), " * ", pexpr(muD, y, form), ") ^ ", J + 1, " + ", t2expr(e2, k, form), " + ", tilt(k, z3, J, form), ") ≤ 1 / 50")
}
l1expr(r, form) =
{
  my([i, J, D, a, a9, ml, mh, k, y, k1, muD, mu1, co, z3, z9, e2] = r, p = pexpr(mu1, k1, form));
  Str("(1 - (15 / 16 - 9 / 16 * (1 - ", p, ") - 3 / 8 * (1 - ", p, ") ^ 2) + ", tilt(k1, z9, J, form), ")")
}
slexpr(r, form) = Str(q(3/5), " / 3 ≤ (1 / 3 - 1 / 50) * (1 - ", l1expr(r, form), ")");
baexpr(r, form) =
{
  my(J = r[2], ml = r[6]);
  Str("(", q(3/5), " * ", q(ml + 3), " + ", q(J - 2), ") / 3 ≤ (", q(27290443/50), " + (1 / 3 - 1 / 50) * ", q(ml - 1778279), ") * (1 - ", l1expr(r, form), ")")
}
hdr(form) = if (form == "F", "import FloatLib\n", "import Mathlib\n");
tac(form, kind) = if (form == "F", if (kind == "K1", "interval (precision := 256)", "interval (precision := 128)"), form == "Q", "decide +kernel", "norm_num");
writefile(name, form, kind, f) =
{
  my(path = Str(OUTDIR, "/Probe/", name, ".lean"));
  system(Str("rm -f ", path));
  write(path, hdr(form), "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n");
  for (t = 1, 95, write(path, "theorem ", kind, "_", rows[t][1], " : ", f(rows[t], form), " := by\n  ", tac(form, kind), "\n"));
}
system(Str("mkdir -p ", OUTDIR, "/Probe"));
writefile("FK1", "F", "K1", k1expr); writefile("FSlope", "F", "SL", slexpr); writefile("FBase", "F", "BA", baexpr);
writefile("RK1", "R", "K1", k1expr); writefile("RSlope", "R", "SL", slexpr); writefile("RBase", "R", "BA", baexpr);
TY = "ℚ";
writefile("QK1", "Q", "K1", k1expr); writefile("QSlope", "Q", "SL", slexpr); writefile("QBase", "Q", "BA", baexpr);
TY = "ℝ";
\\ the sqrt side facts of the rational form: mu <= s^2
{
  my(path = Str(OUTDIR, "/Probe/RSqrt.lean"));
  system(Str("rm -f ", path));
  write(path, "import Mathlib\n\nset_option maxHeartbeats 0\n");
  for (t = 1, 95, my(r = rows[t]);
    write(path, "theorem SQD_", r[1], " : ", q(r[11]), " ≤ ", q(squp(r[11])), " ^ 2 := by norm_num");
    write(path, "theorem SQ1_", r[1], " : ", q(r[12]), " ≤ ", q(squp(r[12])), " ^ 2 := by norm_num"));
}
\\ self-check in exact rationals of the rational form (the same numbers the Lean files carry)
{
  my(bad = 0, worst = [0, 0, -oo], minsl = oo, minba = oo);
  for (t = 1, 95,
    my([i, J, D, a, a9, ml, mh, k, y, k1, muD, mu1, co, z3, z9, e2] = rows[t]);
    my(sD = squp(muD), s1 = squp(mu1), pD = 1 - (2/5*muD + sD/2)/(muD - y), p1 = 1 - (2/5*mu1 + s1/2)/(mu1 - k1));
    my(t2 = (3/8)^e2 * (3/2)^(k - 1), t3 = ((3 + z3)/4)^k * (1/z3)^(J - 1), t9 = ((3 + z9)/4)^k1 * (1/z9)^(J - 1));
    my(K1 = (mh + J + 1)/3 * ((1 - co*pD)^(J + 1) + t2 + t3), L1 = 1 - (15/16 - 9/16*(1 - p1) - 3/8*(1 - p1)^2) + t9);
    my(sl = (1/3 - 1/50)*(1 - L1) - 1/5, ba = (27290443/50 + (1/3 - 1/50)*(ml - 1778279))*(1 - L1) - (3/5*(ml + 3) + J - 2)/3);
    if (!(K1 <= 1/50 && sl >= 0 && ba >= 0 && sD^2 >= muD && s1^2 >= mu1 && co > 0 && pD > 0 && p1 > 0 && y < muD && k1 < mu1),
      bad++; print("FAIL interval ", i));
    minsl = min(minsl, sl); minba = min(minba, ba);
    if (K1*50 > worst[3], worst = [i, J, K1*50]));
  printf("rational form self-check: %d failing of 95; largest (K1)/eps %.6f at interval %d; smallest slope margin %.4e; smallest base margin %.6f\n", bad, worst[3], worst[1], minsl, minba);
}
