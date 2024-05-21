//! Generate the SRS required by the protocols.
//! 
//! Here, s_hat is the toxic waste which should be discarded securely
//! in real applications.
//! 
use serde::{Serialize, Deserialize};

use crate::utils::curve::GenRandom;
use crate::utils::curve::{G1Element, G2Element, GtElement};

use crate::utils::dirac::inner_product;
use crate::utils::to_file::FileIO;

use rayon::{ThreadPoolBuilder, prelude::*};
use crate::config::NUM_THREADS;

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct SRS {
    pub q: usize,
    pub g_hat: G1Element,
    pub h_hat: G2Element,
    pub blind_base: GtElement,
    pub g_hat_vec: Vec<G1Element>,
    pub h_hat_vec: Vec<G2Element>,
    pub g_hat_prime_vec: Vec<G1Element>,
    pub h_hat_prime_vec: Vec<G2Element>,
    pub delta: GtElement,
    pub delta_g: GtElement,
    pub delta_h: GtElement,
}

impl SRS {
    pub fn new(q: usize) -> Self {
               
        let g_hat = G1Element::rand();
        let h_hat = G2Element::rand();

        let pool = ThreadPoolBuilder::new()
        .num_threads(NUM_THREADS)
        .build()
        .unwrap();

        let g_hat_vec: Vec<G1Element> = pool.install(|| {
             (0..q)
                .into_par_iter()
                .map(|_| G1Element::rand())
                .collect()
            }
        );

        let g_hat_prime_vec: Vec<G1Element> = pool.install(|| {
            (0..q)
               .into_par_iter()
               .map(|_| G1Element::rand())
               .collect()
           }
       );

       let h_hat_vec: Vec<G2Element> = pool.install(|| {
                (0..q)
                .into_par_iter()
                .map(|_| G2Element::rand())
                .collect()
            }
        );

        let h_hat_prime_vec: Vec<G2Element> = pool.install(|| {
            (0..q)
                .into_par_iter()
                .map(|_| G2Element::rand())
                .collect()
            }
        );


        let blind_base = G1Element::rand() * G2Element::rand();

        let delta = inner_product(&g_hat_vec, &h_hat_vec);
        let delta_g = inner_product(&g_hat_vec, &h_hat_prime_vec);
        let delta_h = inner_product(&h_hat_vec, &g_hat_prime_vec);

        let srs = Self {
            q,
            g_hat,
            h_hat,
            blind_base,
            g_hat_vec,
            h_hat_vec,
            g_hat_prime_vec,
            h_hat_prime_vec,
            delta,
            delta_g,
            delta_h,
        };

        let log_q = (q as f64).log2() as usize;

        srs.to_file(format!("srs_2e{:?}.srs", log_q), true)
        .unwrap();

        srs

    }

}


impl FileIO for SRS {}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{config::Q_TEST, utils::to_file::FileIO};

    #[test]
    fn test_srs() {
        let srs = SRS::new(Q_TEST);
        let srs_read = FileIO::from_file(
            String::from(
                format!("srs_2e{:?}.srs", (Q_TEST as f64).log2() as usize) ),
                true,
        ).unwrap();
        assert_eq!(srs, srs_read);
    }
}