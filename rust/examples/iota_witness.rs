use sunflower_formal::intersecting::{doubled, max_intersecting, verify};
fn main() {
    for (b, g) in [(2u32, 4u32), (3, 6)] {
        let (n, fam, done) = max_intersecting(g, b, 20_000_000_000);
        assert!(done);
        verify(&fam, b, true).expect("not intersecting sf");
        let sets: Vec<Vec<u32>> = fam.iter()
            .map(|m| (0..16u32).filter(|x| m >> x & 1 == 1).collect()).collect();
        println!("iota({b}) = {n} on {g} points: {sets:?}");
        let d = doubled(&fam, g);
        verify(&d, b, false).expect("DOUBLING IS NOT SUNFLOWER-FREE");
        let dsets: Vec<Vec<u32>> = d.iter()
            .map(|m| (0..32u32).filter(|x| m >> x & 1 == 1).collect()).collect();
        println!("  doubled: {} members of {b}-sets on {} points, sunflower-free OK", d.len(), 2*g);
        let coq: Vec<String> = dsets.iter()
            .map(|s| format!("[{}]", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join("; ")))
            .collect();
        println!("  Coq: [{}]", coq.join("; "));
    }
}
