use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

use blstrs::*;
use ff::Field;
use group::{Curve, Group};

#[bench]
fn bench_fp12_add_assign(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp12, Fp12)> = (0..SAMPLES)
        .map(|_| (Fp12::random(&mut rng), Fp12::random(&mut rng)))
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
fn bench_fp12_sub_assign(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp12, Fp12)> = (0..SAMPLES)
        .map(|_| (Fp12::random(&mut rng), Fp12::random(&mut rng)))
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
fn bench_fp12_mul_assign(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp12, Fp12)> = (0..SAMPLES)
        .map(|_| (Fp12::random(&mut rng), Fp12::random(&mut rng)))
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
fn bench_fp12_squaring(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp12> = (0..SAMPLES).map(|_| Fp12::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        tmp.square();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp12_inverse(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp12> = (0..SAMPLES).map(|_| Fp12::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let tmp = v[count].invert();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp12_compress(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp12> = (0..SAMPLES)
        .map(|_| {
            let p = G1Projective::random(&mut rng).to_affine();
            let q = G2Projective::random(&mut rng).to_affine();
            blstrs::pairing(&p, &q)
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        let tmp = v[count].compress().unwrap();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

#[bench]
fn bench_fp12_uncompress(b: &mut ::test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<_> = (0..SAMPLES)
        .map(|_| {
            let p = G1Projective::random(&mut rng).to_affine();
            let q = G2Projective::random(&mut rng).to_affine();
            blstrs::pairing(&p, &q).compress().unwrap()
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        let tmp = v[count].uncompress().unwrap();
        count = (count + 1) % SAMPLES;
        tmp
    });
}
