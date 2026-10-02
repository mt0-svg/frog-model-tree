\\ Writes the table of Appendix A of main.tex from the certificate file: one line per label s of
\\ level q, with B(q) and the flag of s, and for each increment delta = 0, ..., 8 the integer
\\ 2^28 p(s, delta). Checks on the way that every next label is the one the label rule gives
\\ (B(q + 1) = B(q) + delta, flag kept iff flag set and delta <= 1, end at level 3), that every
\\ probability is a multiple of 2^-28 and that every row sums to 1; stops with an error otherwise.
\\ Run, from code/gp: gp -q table_tex.gp < /dev/null > ../../paper/table.tex
f = "../certificate/table.cert";
L = externstr(Str("cat ", f));
lab(s) = if(s == "root", [0, 1], my(v = Vec(s), b = 0, k = 2); while(v[k] != "f", b = 10*b + eval(v[k]); k++); [b, eval(v[k+1])]);
rows = Map();
{
for(n = 1, #L,
  w = strsplit(L[n], " ");
  if(#w == 0 || w[1] != "tr", next);
  q = eval(w[2]); s = w[3]; dl = eval(w[4]); t = w[5]; p = eval(w[6]);
  [b, fl] = lab(s);
  want = if(q == 3, "end", Str("b", b + dl, "f", (fl == 1 && dl <= 1), "x0"));
  if(t != want, error("next label ", t, " expected ", want, " in line ", n));
  N = p * 2^28;
  if(denominator(N) != 1, error("probability not a multiple of 2^-28 in line ", n));
  key = [q, b, fl];
  r = if(mapisdefined(rows, key), mapget(rows, key), vector(9));
  if(r[dl + 1] != 0, error("repeated increment in line ", n));
  r[dl + 1] = N; mapput(rows, key, r));
}
K = vecsort(Vec(rows));
{
for(n = 1, #K,
  r = mapget(rows, K[n]);
  if(vecsum(r) != 2^28, error("row ", K[n], " does not sum to 2^28"));
  [q, b, fl] = K[n];
  print1(q, " & ", b, " & ", fl);
  for(k = 1, 9, print1(" & ", if(r[k], r[k], "")));
  print(" \\\\"));
}
print("% ", #K, " rows, ", sum(n = 1, #K, #select(x -> x != 0, mapget(rows, K[n]))), " transitions");
