mod g1 {
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use blstrs::*;
    use ff::Field;
    use group::Group;

    #[bench]
    fn bench_g1_mul_assign(b: &mut ::test::Bencher) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let v: Vec<(G1Projective, Scalar)> = (0..SAMPLES)
            .map(|_| (G1Projective::random(&mut rng), Scalar::random(&mut rng)))
            .collect();

        let mut count = 0;
        b.iter(|| {
            let mut tmp = v[count].0;
            tmp *= v[count].1;
            count = (count + 1) % SAMPLES;
            tmp
        });
    }

    #[bench]
    fn bench_g1_add_assign(b: &mut ::test::Bencher) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let v: Vec<(G1Projective, G1Projective)> = (0..SAMPLES)
            .map(|_| {
                (
                    G1Projective::random(&mut rng),
                    G1Projective::random(&mut rng),
                )
            })
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
    fn bench_g1_add_assign_mixed(b: &mut ::test::Bencher) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let v: Vec<(G1Projective, G1Affine)> = (0..SAMPLES)
            .map(|_| {
                (
                    G1Projective::random(&mut rng),
                    G1Projective::random(&mut rng).into(),
                )
            })
            .collect();

        let mut count = 0;
        b.iter(|| {
            let mut tmp = v[count].0;
            tmp += &v[count].1;
            count = (count + 1) % SAMPLES;
            tmp
        });
    }
}

mod g2 {
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use blstrs::*;
    use ff::Field;
    use group::Group;

    #[bench]
    fn bench_g2_mul_assign(b: &mut ::test::Bencher) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let v: Vec<(G2Projective, Scalar)> = (0..SAMPLES)
            .map(|_| (G2Projective::random(&mut rng), Scalar::random(&mut rng)))
            .collect();

        let mut count = 0;
        b.iter(|| {
            let mut tmp = v[count].0;
            tmp *= v[count].1;
            count = (count + 1) % SAMPLES;
            tmp
        });
    }

    #[bench]
    fn bench_g2_add_assign(b: &mut ::test::Bencher) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let v: Vec<(G2Projective, G2Projective)> = (0..SAMPLES)
            .map(|_| {
                (
                    G2Projective::random(&mut rng),
                    G2Projective::random(&mut rng),
                )
            })
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
    fn bench_g2_add_assign_mixed(b: &mut ::test::Bencher) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let v: Vec<(G2Projective, G2Affine)> = (0..SAMPLES)
            .map(|_| {
                (
                    G2Projective::random(&mut rng),
                    G2Projective::random(&mut rng).into(),
                )
            })
            .collect();

        let mut count = 0;
        b.iter(|| {
            let mut tmp = v[count].0;
            tmp += &v[count].1;
            count = (count + 1) % SAMPLES;
            tmp
        });
    }
}
