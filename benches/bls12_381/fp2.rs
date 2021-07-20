use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

use blstrs::*;
use ff::Field;

#[bench]
fn bench_fp2_add_assign(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp2, Fp2)> = (0..SAMPLES)
        .map(|_| (Fp2::random(&mut rng), Fp2::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count].0;
        tmp += &v[count].1;
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp2_sub_assign(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp2, Fp2)> = (0..SAMPLES)
        .map(|_| (Fp2::random(&mut rng), Fp2::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count].0;
        tmp -= &v[count].1;
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp2_mul_assign(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp2, Fp2)> = (0..SAMPLES)
        .map(|_| (Fp2::random(&mut rng), Fp2::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count].0;
        tmp *= &v[count].1;
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp2_squaring(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp2> = (0..SAMPLES).map(|_| Fp2::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        tmp.square();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp2_inverse(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp2> = (0..SAMPLES).map(|_| Fp2::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let tmp = v[count].invert();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp2_sqrt(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp2> = (0..SAMPLES).map(|_| Fp2::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let tmp = v[count].sqrt();
        count = (count + 1) % SAMPLES;
        tmp
    });
}
