//! Utilities for provider module.
pub(in crate::provider) mod fb_msm;
pub mod msm {
  use ff::PrimeField as _;
use group::Group;
  use halo2curves::msm::best_multiexp;
  use halo2curves::CurveAffine;
  use rayon::prelude::*;
  use bitvec::{array::BitArray, order::Lsb0};

  // this argument swap is useful until Rust gets named arguments
  // and saves significant complexity in macro code
  pub fn cpu_best_msm<C: CurveAffine>(bases: &[C], scalars: &[C::Scalar]) -> C::Curve {
    let max_num_bits = scalars
          .par_iter()
          .map(|s| {
            // in practive, this is how every field of interest is implemented
            assert_eq!(std::mem::size_of::<C::Scalar>(), std::mem::size_of::<[u64; 4]>());
            let bytes = s.to_repr();
            let limbs: [u64; 4] = unsafe { std::mem::transmute_copy(&bytes) };
            
            let le_array = BitArray::<_, Lsb0>::new(limbs);
            le_array.len() - le_array.trailing_zeros()
          })
          .max()
          .unwrap();

        let map_field_elements_to_u64 = |field_elements: &[C::Scalar]| {
          field_elements
            .iter()
            .map(|field_element| {
              // in practive, this is how every field of interest is implemented
              assert_eq!(std::mem::size_of::<C::Scalar>(), std::mem::size_of::<[u64; 4]>());
              let bytes = field_element.to_repr();
              let limbs: [u64; 4] = unsafe { std::mem::transmute_copy(&bytes) };
              limbs[0]
            })
            .collect()
        };

        match max_num_bits {
          0 => <C::Curve as Group>::identity(),
          1 => {
            let scalars_u64: Vec<_> = map_field_elements_to_u64(scalars);
            msm_binary(bases, &scalars_u64)
          }
          2..=10 => {
            let scalars_u64: Vec<_> = map_field_elements_to_u64(scalars);
            msm_small(bases, &scalars_u64, max_num_bits)
          }
          11..=64 => {
            let scalars_u64: Vec<_> = map_field_elements_to_u64(scalars);
            msm_u64_wnaf(bases, &scalars_u64, max_num_bits)
          }
          _ => best_multiexp(scalars, bases),
        }

  }

  fn msm_binary<C: CurveAffine>(bases: &[C], scalars: &[u64]) -> C::Curve {
    scalars
      .iter()
      .zip(bases)
      .filter(|(&scalar, _base)| scalar != 0)
      .map(|(_scalar, base)| base)
      .fold(C::Curve::identity(), |sum, base| sum + base)
  }

  fn msm_small<C: CurveAffine>(
    bases: &[C],
    scalars: &[u64],
    max_num_bits: usize,
  ) -> C::Curve {
    let num_buckets: usize = 1 << max_num_bits;
    // Assign things to buckets based on the scalar
    let mut buckets: Vec<C::Curve> = vec![<C::Curve as Group>::identity(); num_buckets];
    scalars
      .iter()
      .zip(bases)
      .filter(|(&scalar, _base)| scalar != 0)
      .for_each(|(&scalar, base)| {
        buckets[scalar as usize] += base;
      });

    let mut result = <C::Curve as Group>::identity();
    let mut running_sum = <C::Curve as Group>::identity();
    buckets.iter().skip(1).rev().for_each(|bucket| {
      running_sum += bucket;
      result += running_sum;
    });
    result
  }

  // Adapted from the Jolt implementation, which is in turn adapted from the ark_ec implementation
  fn msm_u64_wnaf<C: CurveAffine>(
    bases: &[C],
    scalars: &[u64],
    max_num_bits: usize,
  ) -> C::Curve {
    use std::cmp::Ordering;

    let c = if bases.len() < 32 {
      3
    } else {
      // ~= ln(bases.len()) + 2
      (bases.len().ilog2() as usize * 69 / 100) + 2
    };

    let digits_count = (max_num_bits + c - 1) / c;
    let radix: u64 = 1 << c;
    let window_mask: u64 = radix - 1;

    let scalar_digits = scalars
      .into_par_iter()
      .flat_map_iter(|&scalar| {
        let mut carry = 0u64;
        (0..digits_count).into_iter().map(move |i| {
          // Construct a buffer of bits of the scalar, starting at `bit_offset`.
          let bit_offset = i * c;
          let bit_idx = bit_offset % 64;
          // Read the bits from the scalar
          let bit_buf = scalar >> bit_idx;
          // Read the actual coefficient value from the window
          let coef = carry + (bit_buf & window_mask); // coef = [0, 2^r)

          // Recenter coefficients from [0,2^c) to [-2^c/2, 2^c/2)
          carry = (coef + radix / 2) >> c;
          let mut digit = (coef as i64) - (carry << c) as i64;

          if i == digits_count - 1 {
            digit += (carry << c) as i64;
          }
          digit
        })
      })
      .collect::<Vec<_>>();
    let zero = <C::Curve as Group>::identity();

    let window_sums: Vec<_> = (0..digits_count)
      .into_par_iter()
      .map(|i| {
        let mut buckets = vec![zero; 1 << c];
        for (digits, base) in scalar_digits.chunks(digits_count).zip(bases) {
          // digits is the digits thing of the first scalar?
          let scalar = digits[i];
          match 0.cmp(&scalar) {
            Ordering::Less => buckets[(scalar - 1) as usize] += base,
            Ordering::Greater => buckets[(-scalar - 1) as usize] -= base,
            Ordering::Equal => (),
          }
        }

        let mut running_sum = <C::Curve as Group>::identity();
        let mut res = <C::Curve as Group>::identity();
        buckets.iter().rev().for_each(|b| {
          running_sum += b;
          res += &running_sum;
        });
        res
      })
      .collect();

    // We store the sum for the lowest window.
    let lowest = *window_sums.first().unwrap();

    // We're traversing windows from high to low.
    let result = lowest
      + window_sums[1..]
        .iter()
        .rev()
        .fold(zero, |mut total, sum_i| {
          total += sum_i;
          for _ in 0..c {
            total = total.double();
          }
          total
        });
    result
  }

}

pub mod iterators {
  use ff::Field;
  use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
  use rayon_scan::ScanParallelIterator;
  use std::iter::DoubleEndedIterator;
  use std::{
    borrow::Borrow,
    ops::{AddAssign, MulAssign},
  };

  pub trait DoubleEndedIteratorExt: DoubleEndedIterator {
    /// This function employs Horner's scheme and core traits to create a combination of an iterator input with the powers
    /// of a provided coefficient.
    fn rlc<T, F>(&mut self, coefficient: &F) -> T
    where
      T: Clone + for<'a> MulAssign<&'a F> + for<'r> AddAssign<&'r T>,
      Self::Item: Borrow<T>,
    {
      let mut iter = self.rev();
      let Some(fst) = iter.next() else {
        panic!("input iterator should not be empty")
      };

      iter.fold(fst.borrow().clone(), |mut acc, item| {
        acc *= coefficient;
        acc += item.borrow();
        acc
      })
    }
  }

  impl<I: DoubleEndedIterator> DoubleEndedIteratorExt for I {}

  pub trait IndexedParallelIteratorExt: IndexedParallelIterator {
    /// This function core traits to create a combination of an iterator input with the powers
    /// of a provided coefficient.
    fn rlc<T, F>(self, coefficient: &F) -> T
    where
      F: Field,
      Self::Item: Borrow<T>,
      T: Clone + for<'a> MulAssign<&'a F> + for<'r> AddAssign<&'r T> + Send + Sync,
    {
      debug_assert!(self.len() > 0);
      // generate an iterator of powers of the right length
      let v = {
        let mut v = vec![*coefficient; self.len()];
        v[0] = F::ONE;
        v
      };
      // the collect is due to Scan being unindexed
      let powers: Vec<_> = v.into_par_iter().scan(|a, b| *a * *b, F::ONE).collect();

      self
        .zip_eq(powers.into_par_iter())
        .map(|(pt, val)| {
          let mut pt = pt.borrow().clone();
          pt *= &val;
          pt
        })
        .reduce_with(|mut a, b| {
          a += &b;
          a
        })
        .unwrap()
    }
  }

  impl<I: IndexedParallelIterator> IndexedParallelIteratorExt for I {}
}

#[cfg(test)]
pub mod test_utils {
  //! Contains utilities for testing and benchmarking.
  use crate::spartan::polys::multilinear::MultilinearPolynomial;
  use crate::traits::{
    commitment::CommitmentEngineTrait, evaluation::EvaluationEngineTrait, Engine,
  };
  use ff::Field;
  use rand::rngs::StdRng;
  use rand_core::{CryptoRng, RngCore};
  use std::sync::Arc;

  /// Returns a random polynomial, a point and calculate its evaluation.
  fn random_poly_with_eval<E: Engine, R: RngCore + CryptoRng>(
    num_vars: usize,
    mut rng: &mut R,
  ) -> (
    MultilinearPolynomial<<E as Engine>::Scalar>,
    Vec<<E as Engine>::Scalar>,
    <E as Engine>::Scalar,
  ) {
    // Generate random polynomial and point.
    let poly = MultilinearPolynomial::random(num_vars, &mut rng);
    let point = (0..num_vars)
      .map(|_| <E as Engine>::Scalar::random(&mut rng))
      .collect::<Vec<_>>();

    // Calculation evaluation of point over polynomial.
    let eval = poly.evaluate(&point);

    (poly, point, eval)
  }

  /// Methods used to test the prove and verify flow of [`MultilinearPolynomial`] Commitment Schemes
  /// (PCS).
  ///
  /// Generates a random polynomial and point from a seed to test a proving/verifying flow of one
  /// of our [`EvaluationEngine`].
  pub(crate) fn prove_verify_from_num_vars<E: Engine, EE: EvaluationEngineTrait<E>>(
    num_vars: usize,
  ) {
    use rand_core::SeedableRng;

    let mut rng = rand::rngs::StdRng::seed_from_u64(num_vars as u64);

    let (poly, point, eval) = random_poly_with_eval::<E, StdRng>(num_vars, &mut rng);

    // Mock commitment key.
    let ck = E::CE::setup(b"test", 1 << num_vars);
    let ck = Arc::new(ck);
    // Commits to the provided vector using the provided generators.
    let commitment = E::CE::commit(&ck, poly.evaluations());

    prove_verify_with::<E, EE>(ck, &commitment, &poly, &point, &eval, true)
  }

  fn prove_verify_with<E: Engine, EE: EvaluationEngineTrait<E>>(
    ck: Arc<<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey>,
    commitment: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    poly: &MultilinearPolynomial<<E as Engine>::Scalar>,
    point: &[<E as Engine>::Scalar],
    eval: &<E as Engine>::Scalar,
    evaluate_bad_proof: bool,
  ) {
    use crate::traits::TranscriptEngineTrait;
    use std::ops::Add;

    // Generate Prover and verifier key for given commitment key.
    let ock = ck.clone();
    let (prover_key, verifier_key) = EE::setup(ck);

    // Generate proof.
    let mut prover_transcript = E::TE::new(b"TestEval");
    let proof = EE::prove(
      &*ock,
      &prover_key,
      &mut prover_transcript,
      commitment,
      poly.evaluations(),
      point,
      eval,
    )
    .unwrap();
    let pcp = prover_transcript.squeeze(b"c").unwrap();

    // Verify proof.
    let mut verifier_transcript = E::TE::new(b"TestEval");
    EE::verify(
      &verifier_key,
      &mut verifier_transcript,
      commitment,
      point,
      eval,
      &proof,
    )
    .unwrap();
    let pcv = verifier_transcript.squeeze(b"c").unwrap();

    // Check if the prover transcript and verifier transcript are kept in the same state.
    assert_eq!(pcp, pcv);

    if evaluate_bad_proof {
      // Generate another point to verify proof. Also produce eval.
      let altered_verifier_point = point
        .iter()
        .map(|s| s.add(<E as Engine>::Scalar::ONE))
        .collect::<Vec<_>>();
      let altered_verifier_eval =
        MultilinearPolynomial::evaluate_with(poly.evaluations(), &altered_verifier_point);

      // Verify proof, should fail.
      let mut verifier_transcript = E::TE::new(b"TestEval");
      assert!(EE::verify(
        &verifier_key,
        &mut verifier_transcript,
        commitment,
        &altered_verifier_point,
        &altered_verifier_eval,
        &proof,
      )
      .is_err());
    }
  }
}
