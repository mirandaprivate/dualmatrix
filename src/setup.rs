//! Generate the SRS required by the protocols.
//! 
//! Here, s_hat is the toxic waste which should be discarded securely
//! in real applications.
//! 
use serde::{Serialize, Deserialize};

use crate::utils::curve::GenRandom;
use crate::utils::curve::{G1Element, G2Element, GtElement};

use crate::utils::to_file::FileIO;


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
}

impl SRS {
    pub fn new(q: usize) -> Self {
               
        let g_hat = G1Element::rand();
        let h_hat = G2Element::rand();


        let g_hat_vec = (0..q)
        .map(|_| G1Element::rand()).collect();

        let g_hat_prime_vec = (0..q)
        .map(|_| G1Element::rand()).collect();

        let h_hat_vec = (0..q)
        .map(|_| G2Element::rand()).collect();

        let h_hat_prime_vec = (0..q)
        .map(|_| G2Element::rand()).collect();

        let blind_base = G1Element::rand() * G2Element::rand();

        let srs = Self {
            q,
            g_hat,
            h_hat,
            blind_base,
            g_hat_vec,
            h_hat_vec,
            g_hat_prime_vec,
            h_hat_prime_vec,
        };

        let log_q = (q as f64).log2() as usize;
        println!("---");
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
        println!("srs: {:?}", srs);
        assert_eq!(srs, srs_read);
    }
}