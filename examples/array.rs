use bittle::Bits;

fn main() {
    let set: [u32; 4] = bittle::set![4, 63, 71];
    assert!(set.iter_ones().eq([4, 63, 71]));

    let n = 0b10001000u8;
    dbg!(n.iter_ones().collect::<Vec<_>>());
    assert!(n.iter_ones().eq([0, 5]));

    let vec = vec![0, 1, 2, 3];
    assert!(vec.iter_ones().eq([32, 65, 96, 97]));
}
