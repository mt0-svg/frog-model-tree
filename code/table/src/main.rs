// The program that wrote the table of the paper (Section 7 and Appendix A), in floating point; the
// Lean kernel checks the table, not this program. J = 4, T = 8, the class of labels (q, B(q), all
// increments so far <= 1) of Section 7, eps = 1e-4, phi = 23/20, rho = 27/40, T' = 16, masses below
// 1e-12 dropped.
//
// table iterate H N OUT: N steps from the law of the file H. One step sends a law H of the class to
// the law of the class, built level by level by quantile couplings (cls::envelope), that dominates
// the normalized part on {B(J) <= T} of the output law of the root chain for
// H* = (1 - eps) H + eps (tail atoms); the root chain runs to e > T or p > T' (check::phi_joint_chain).
// Writes the iterate of step n to OUT.n.
//
// table write H H' S OUT: the law H + S (H - H') for the laws of the files H and H', its rows rounded to
// multiples of 2^-28, written to OUT.v3 (the table, format of code/certificate/FORMAT.md, version 3)
// and OUT.v2 (its atoms).

mod check;
mod cls;
mod fx;

const J: usize = 4;
const T: usize = 8;
const KIND: u8 = 1;
const EPS: f64 = 1e-4;
const PHI: f64 = 1.15;
const RHO: f64 = 0.675;
const PMAX: usize = 16;
const TINY: f64 = 1e-12;

fn load(path: &str) -> cls::CL {
    let h = cls::CL::load(path);
    assert!(h.kind == KIND && h.j == J && h.t == T);
    h
}

fn iterate(mut h: cls::CL, n: usize, out_prefix: &str) {
    for it in 0..n {
        let pt = cls::pot(&h, EPS, PHI, RHO);
        let (chain, nid) = (h.chain(), h.nid);
        let (out, _, _, _) = check::phi_joint_chain(chain, nid, J, T, EPS, PMAX, TINY, std::slice::from_ref(&pt));
        h = cls::envelope(&out, J, T, h.kind);
        let path = format!("{}.{}", out_prefix, it + 1);
        h.save(&path);
        println!("step {}: wrote {}, E B(1) = {:.4}", it + 1, path, h.mean(1));
    }
}

fn write_table(h: cls::CL, prev: cls::CL, s: f64, pre: &str) {
    let mut h = h.extrapolate(&prev, s);
    println!("extrapolated by s = {}: E B(1) = {:.6}, E B(J) = {:.6}", s, h.mean(1), h.mean(J));
    let (en, ed): (u64, u64) = (1, 10000);
    let (rho, phi, tpend, rounds, prune) = ("27/40", "23/20", 16, 400, "1/1000000000000");
    let bits = 28;
    let nr = h.rational_rows(bits);
    h = h.with_rows(&nr, bits);
    let pt = cls::pot(&h, en as f64 / ed as f64, 23.0 / 20.0, 27.0 / 40.0);
    let kd = 1_000_000_000u64;
    let kn = (pt.m.powf(1.0 / J as f64) * (1.0 + 1e-9) * kd as f64).ceil() as u64;
    let kappa = format!("{}/{}", kn, kd);
    let eps = format!("{}/{}", en, ed);
    let hdr = (eps.as_str(), rho, phi, kappa.as_str(), tpend, rounds, prune);
    let comment = format!("the table law, class kind {} J = {} T = {}, rows over 2^{}; floating-point M = {:.9}, kappa^J = {:.9}", h.kind, J, T, bits, pt.m, (kn as f64 / kd as f64).powi(J as i32));
    h.write_v3(&format!("{}.v3", pre), bits, hdr, &comment);
    h.write_v2(&format!("{}.v2", pre), bits, en, ed, hdr, &comment);
    println!("wrote {}.v3 and {}.v2 (kappa = {}, M = {:.9})", pre, pre, kappa, pt.m);
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|x| x.as_str()) {
        Some("iterate") if a.len() == 5 => iterate(load(&a[2]), a[3].parse().unwrap(), &a[4]),
        Some("write") if a.len() == 6 => write_table(load(&a[2]), load(&a[3]), a[4].parse().unwrap(), &a[5]),
        _ => {
            eprintln!("usage: table iterate H N OUT | table write H H' S OUT");
            std::process::exit(2);
        }
    }
}
