//! Does the substitution construction really produce sunflower-free
//! families? g(ab) >= g(a) * iota(b)^a, needing the inner family
//! intersecting.
use sunflower_formal::intersecting::{find_sunflower_128, max_intersecting, substitute, verify};

fn main() {
    // Outer: two_triangles, a = 2, 6 members on 6 points (sunflower-free,
    // NOT intersecting -- only the inner family needs to be).
    let tt: Vec<u32> = vec![0b000011, 0b000101, 0b000110, 0b011000, 0b101000, 0b110000];
    verify(&tt, 2, false).expect("two_triangles broken");

    for (b, wg) in [(2u32, 3u32), (3, 6)] {
        let (n, h, done) = max_intersecting(wg, b, 20_000_000_000);
        assert!(done);
        verify(&h, b, true).expect("inner family not intersecting sf");
        let out = substitute(&tt, 6, &h, wg);
        let expect = 6 * n * n;
        println!("a=2 (|G|=6, 2-uniform)  b={b} (iota={n} on {wg} pts)");
        println!("  -> {} members of {}-sets on {} points (expected {expect})",
                 out.len(), 2 * b, 6 * wg);
        assert_eq!(out.len(), expect);
        let mut sorted = out.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), out.len(), "members not distinct");
        match find_sunflower_128(&out) {
            None => println!("  -> SUNFLOWER-FREE. so g({}) >= {expect}", 2 * b),
            Some(t) => println!("  -> REFUTED: sunflower at {t:?}"),
        }
    }

    // The control: substitute a NON-intersecting inner family and the
    // construction should break.
    let (_, h3, _) = max_intersecting(6, 3, 20_000_000_000);
    let mut broken = h3.clone();
    broken.truncate(2);
    broken.push(0b111000); // {3,4,5}: disjoint from {0,1,2}
    println!("control: inner family made non-intersecting ({} members)", broken.len());
    match verify(&broken, 3, false) {
        Ok(()) => {
            let out = substitute(&tt, 6, &broken, 6);
            match find_sunflower_128(&out) {
                None => println!("  -> still sunflower-free (intersecting may not be needed?)"),
                Some(t) => println!("  -> breaks, as predicted: sunflower at {t:?}"),
            }
        }
        Err(e) => println!("  -> control family is itself bad: {e}"),
    }
}
