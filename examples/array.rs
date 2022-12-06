use bittle::Bits;

fn main() {
    let set: [u32; 4] = bittle::set![4, 63, 71];

    for bit in set.iter_bits() {
        dbg!(bit);
    }
}
