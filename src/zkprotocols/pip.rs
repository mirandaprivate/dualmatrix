//! Implementation of the Public Inner Product protocol
//!
//! Details of this protocol can be found in the DualMatrix paper 

use curv::arithmetic::Zero;

// 
use crate::setup::SRS;

use crate::utils::curve::{ZpElement, G1Element, G2Element, GtElement};
use crate::utils::dirac::{self, inner_product};
use crate::utils::fiat_shamir::{TranElem, TranSeq};
use crate::utils::xi;

use super::zk_trans::ZkTranSeqProver;


pub struct Pip {
    pub v_g_vec: Vec<G1Element>,
    pub v_h_vec: Vec<G2Element>,
    pub challenges_g_vec: Vec<Vec<ZpElement>>,
    pub challenges_h_vec: Vec<Vec<ZpElement>>,
}

impl Pip {
    pub fn new(
    ) -> Self {
        Self {
            v_g_vec: Vec::new(),
            v_h_vec: Vec::new(),
            challenges_g_vec: Vec::new(),
            challenges_h_vec: Vec::new(),
        }
    }
    pub fn from(
        v_g_vec_value: Vec<G1Element>, 
        v_h_vec_value: Vec<G2Element>, 
        challenges_g_vec_value: Vec<Vec<ZpElement>>,
        challenges_h_vec_value: Vec<Vec<ZpElement>>
    ) -> Self {
        Self {
            v_g_vec: v_g_vec_value,
            v_h_vec: v_h_vec_value,
            challenges_g_vec: challenges_g_vec_value,
            challenges_h_vec: challenges_h_vec_value,
        }
    }

    fn reduce_challenges(
        &self,
        challenges_1: Vec<ZpElement>,
        challenges_2: Vec<ZpElement>,
    ) -> ZpElement {
        let k_1 = challenges_1.len();
        let k_2 = challenges_2.len();
        let k = std::cmp::min(k_1, k_2);
        let vec_1: Vec<ZpElement> = challenges_1.iter().rev().take(k).cloned().collect();
        let vec_2: Vec<ZpElement> = challenges_2.iter().rev().take(k).cloned().collect();
        let mut result = ZpElement::from(1 as u64);
        for i in 0..k {
            result = result * (
                ZpElement::from(1 as u64) + vec_1[i] * vec_2[i]
            );
        }
        result
    }

    pub fn prove(&self, srs: &SRS, trans_seq: &mut ZkTranSeqProver)  {

        let len_g = self.v_g_vec.len();  
        let len_h = self.v_h_vec.len();

      
        let z = trans_seq.gen_challenge();
     
        let mut a_vec: Vec<ZpElement> = vec![ZpElement::zero(); srs.q];
        for i in 0..len_g {
            a_vec = dirac::vec_addition(
                &a_vec, 
                &dirac::vec_scalar_mul(
                    &xi::xi_from_challenges(&self.challenges_g_vec[i]),
                    z.pow(i as u64)
                )
            );
        }
         
        let mut b_vec: Vec<ZpElement> = vec![ZpElement::zero(); srs.q];
        for i in 0..len_h {
            b_vec = dirac::vec_addition(
                &b_vec, 
                &dirac::vec_scalar_mul(
                    &xi::xi_from_challenges(&self.challenges_h_vec[i]),
                    z.pow(i as u64)
                )
            );
        }

        let n = srs.q;
        let log_n = (n as u64).ilog2() as usize;

        let mut a_vec_current = a_vec.clone();
        let mut b_vec_current = b_vec.clone();
        let mut g_vec_current = srs.g_hat_vec.clone();
        let mut h_vec_current = srs.h_hat_vec.clone();
        let mut g_prime_vec_current = srs.g_hat_prime_vec.clone();
        let mut h_prime_vec_current = srs.h_hat_prime_vec.clone();
        
        let mut challenges: Vec<ZpElement> = Vec::new();
        let mut challenges_inv: Vec<ZpElement> = Vec::new();

        for j in 0..log_n {
            let current_len = n / 2usize.pow(j as u32);
            
            let a_left = 
                a_vec_current[0..current_len/2].to_vec();
            let a_right = 
                a_vec_current[current_len/2..current_len].to_vec();
            
            let b_left = 
                b_vec_current[0..current_len/2].to_vec();
            let b_right = 
                b_vec_current[current_len/2..current_len].to_vec();
            
            let g_left = 
                g_vec_current[0..current_len/2].to_vec();
            let g_right = 
                g_vec_current[current_len/2..current_len].to_vec();

            let h_left = 
                h_vec_current[0..current_len/2].to_vec();
            let h_right = 
                h_vec_current[current_len/2..current_len].to_vec();

            let g_prime_left = 
                g_prime_vec_current[0..current_len/2].to_vec();
            let g_prime_right = 
                g_prime_vec_current[current_len/2..current_len].to_vec();

            let h_prime_left = 
                h_prime_vec_current[0..current_len/2].to_vec();
            let h_prime_right = 
                h_prime_vec_current[current_len/2..current_len].to_vec();

            let l_a = 
                dirac::inner_product(&a_left, &g_right);
            let r_a = 
                dirac::inner_product(&a_right, &g_left);

            trans_seq.push_without_blinding(TranElem::G1(l_a));
            trans_seq.push_without_blinding(TranElem::G1(r_a));

            let l_b = 
                dirac::inner_product(&b_right, &h_left);
            let r_b = 
                dirac::inner_product(&b_left, &h_right);

            trans_seq.push_without_blinding(TranElem::G2(l_b));
            trans_seq.push_without_blinding(TranElem::G2(r_b));



            let l_delta = 
                dirac::inner_product(&g_right, &h_left);
            let r_delta = 
                dirac::inner_product(&g_left, &h_right);

            trans_seq.push_without_blinding(TranElem::Gt(l_delta));
            trans_seq.push_without_blinding(TranElem::Gt(r_delta));


            let l_g = 
                dirac::inner_product(&g_right, &h_prime_left);
            let r_g = 
                dirac::inner_product(&g_left, &h_prime_right);

            trans_seq.push_without_blinding(TranElem::Gt(l_g));
            trans_seq.push_without_blinding(TranElem::Gt(r_g));

            let l_h = 
            dirac::inner_product(&g_prime_right, &h_left);
            let r_h = 
                dirac::inner_product(&g_prime_left, &h_right);

            trans_seq.push_without_blinding(TranElem::Gt(l_h));
            trans_seq.push_without_blinding(TranElem::Gt(r_h));
                    
            
            let x_j = trans_seq.gen_challenge();
            let x_j_inv = x_j.inv();

            challenges.push(x_j);
            challenges_inv.push(x_j_inv);

            a_vec_current = dirac::vec_addition(
                &a_left,
                &dirac::vec_scalar_mul(
                    &a_right, x_j),
            );

            b_vec_current = dirac::vec_addition(
                &b_left,
                &dirac::vec_scalar_mul(
                    &b_right, x_j_inv),
            );

            g_vec_current = dirac::vec_addition(
                &g_left,
                &dirac::vec_scalar_mul(
                    &g_right, x_j_inv),
            );

            h_vec_current = dirac::vec_addition(
                &h_left,
                &dirac::vec_scalar_mul(
                    &h_right, x_j),
            );

            g_prime_vec_current = dirac::vec_addition(
                &g_prime_left,
                &dirac::vec_scalar_mul(
                    &g_prime_right, x_j_inv),
            );

            h_prime_vec_current = dirac::vec_addition(
                &h_prime_left,
                &dirac::vec_scalar_mul(
                    &h_prime_right, x_j),
            );

        }

        let a_reduce = a_vec_current[0];
        let b_reduce = b_vec_current[0];
        let g_reduce = g_vec_current[0];
        let h_reduce = h_vec_current[0];
        let g_prime_reduce = g_prime_vec_current[0];
        let h_prime_reduce = h_prime_vec_current[0];

        trans_seq.push_without_blinding(TranElem::Zp(a_reduce));
        trans_seq.push_without_blinding(TranElem::Zp(b_reduce));
        trans_seq.push_without_blinding(TranElem::G1(g_reduce));
        trans_seq.push_without_blinding(TranElem::G2(h_reduce));
        trans_seq.push_without_blinding(TranElem::G1(g_prime_reduce));
        trans_seq.push_without_blinding(TranElem::G2(h_prime_reduce));


    }

    pub fn verify_as_subprotocol(
        &self, srs: &SRS, trans_seq: &mut TranSeq
    ) -> bool {

        let pointer_old = trans_seq.pointer;
        

        let n = srs.q;
        let log_n = (n as u64).ilog2() as usize;

        let mut pointer = pointer_old;

        if let TranElem::Coin(z) = trans_seq.data[pointer] {
            pointer = pointer + 1;

            let len_g = self.v_g_vec.len();  
            let len_h = self.v_h_vec.len();

            let mut ag = G1Element::zero();
            for i in 0..len_g {
                ag = ag + self.v_g_vec[i] * z.pow(i as u64); 
            } 

            let mut bh = G2Element::zero();
            for i in 0..len_h {
                bh = bh + self.v_h_vec[i] * z.pow(i as u64); 
            }

            let mut l_a_vec: Vec<G1Element> = Vec::new();
            let mut r_a_vec: Vec<G1Element> = Vec::new();
            let mut l_b_vec: Vec<G2Element> = Vec::new();
            let mut r_b_vec: Vec<G2Element> = Vec::new();
            let mut l_delta_vec: Vec<GtElement> = Vec::new();
            let mut r_delta_vec: Vec<GtElement> = Vec::new();
            let mut l_g_vec: Vec<GtElement> = Vec::new();
            let mut r_g_vec: Vec<GtElement> = Vec::new();
            let mut l_h_vec: Vec<GtElement> = Vec::new();
            let mut r_h_vec: Vec<GtElement> = Vec::new();
            let mut challenges: Vec<ZpElement> = Vec::new();
            let mut challenges_inv: Vec<ZpElement> = Vec::new();

            for _ in 0..log_n {
                
                if let (
                    TranElem::G1(l_a),
                    TranElem::G1(r_a),
                    TranElem::G2(l_b),
                    TranElem::G2(r_b),
                    TranElem::Gt(l_delta),
                    TranElem::Gt(r_delta),
                    TranElem::Gt(l_g),
                    TranElem::Gt(r_g),
                    TranElem::Gt(l_h),
                    TranElem::Gt(r_h),
                    TranElem::Coin(x_j),
                ) = (
                    trans_seq.data[pointer],
                    trans_seq.data[pointer + 1],
                    trans_seq.data[pointer + 2],
                    trans_seq.data[pointer + 3],
                    trans_seq.data[pointer + 4],
                    trans_seq.data[pointer + 5],
                    trans_seq.data[pointer + 6],
                    trans_seq.data[pointer + 7],
                    trans_seq.data[pointer + 8],
                    trans_seq.data[pointer + 9],
                    trans_seq.data[pointer + 10],
                ) {
                    l_a_vec.push(l_a);
                    r_a_vec.push(r_a);
                    l_b_vec.push(l_b);
                    r_b_vec.push(r_b);
                    l_delta_vec.push(l_delta);
                    r_delta_vec.push(r_delta);
                    l_g_vec.push(l_g);
                    r_g_vec.push(r_g);
                    l_h_vec.push(l_h);
                    r_h_vec.push(r_h);
                    challenges.push(x_j);
                    challenges_inv.push(x_j.inv());

                    pointer = pointer + 11;
                }
            }

            if let (
                TranElem::Zp(a_reduce),
                TranElem::Zp(b_reduce),
                TranElem::G1(g_reduce),
                TranElem::G2(h_reduce),
                TranElem::G1(g_prime_reduce),
                TranElem::G2(h_prime_reduce),
            ) = (
                trans_seq.data[pointer],
                trans_seq.data[pointer + 1],
                trans_seq.data[pointer + 2],
                trans_seq.data[pointer + 3],
                trans_seq.data[pointer + 4],
                trans_seq.data[pointer + 5],
            ) {

                trans_seq.pointer = pointer + 6;
                
                let lhs_1 = ag 
                + inner_product(&l_a_vec, &challenges_inv)
                + inner_product(&r_a_vec, &challenges);
                let rhs_1 = a_reduce * g_reduce;
                let check_1 = lhs_1 == rhs_1;

                // println!("check_1: {:?}", check_1);

                let lhs_2 = bh
                + inner_product(&l_b_vec, &challenges_inv)
                + inner_product(&r_b_vec, &challenges);
                let rhs_2 = b_reduce * h_reduce;
                let check_2 = lhs_2 == rhs_2;

                // println!("check_2: {:?}", check_2);

                let lhs_3 = srs.delta
                + inner_product(&l_delta_vec, &challenges_inv)
                + inner_product(&r_delta_vec, &challenges);
                let rhs_3 = g_reduce * h_reduce;
                let check_3 = lhs_3 == rhs_3;

                // println!("check_3: {:?}", check_3);


                let lhs_4 = srs.delta_g
                + inner_product(&l_g_vec, &challenges_inv)
                + inner_product(&r_g_vec, &challenges);
                let rhs_4 = g_reduce * h_prime_reduce;
                let check_4 = lhs_4 == rhs_4;

                // println!("check_4: {:?}", check_4);


                let lhs_5 = srs.delta_h
                + inner_product(&l_h_vec, &challenges_inv)
                + inner_product(&r_h_vec, &challenges);
                let rhs_5 = g_prime_reduce * h_reduce;
                let check_5 = lhs_5 == rhs_5;

                // println!("check_5: {:?}", check_5);


                let mut a_reduce_prime: ZpElement = ZpElement::zero();
                for i in 0..len_g {
                    a_reduce_prime = a_reduce_prime 
                        + self.reduce_challenges(
                            self.challenges_g_vec[i].clone(), 
                            challenges.clone())
                        * z.pow(i as u64);
                }


                let mut b_reduce_prime: ZpElement = ZpElement::zero();
                for i in 0..len_h {
                    b_reduce_prime = b_reduce_prime 
                        + self.reduce_challenges(
                            self.challenges_h_vec[i].clone(), 
                            challenges_inv.clone())
                        * z.pow(i as u64);
                }

                let check_6 = a_reduce == a_reduce_prime;
                let check_7 = b_reduce == b_reduce_prime;
                
                // println!("check_6: {:?}", check_6);
                // println!("check_7: {:?}", check_7);

                if check_1 && check_2 && check_3 && check_4 && check_5 && check_6 && check_7{
                    return true;
                } else {
                    println!("!! Pip equation check failed!");
                }

            }
            
        }

        false

    }

    pub fn verify(&self, srs: &SRS, trans_seq: &mut TranSeq
    ) -> bool {


        if trans_seq.check_fiat_shamir() == false {
            println!("!! Fiat shamir check failed when verifying Pip");
            return false;
        }

        self.verify_as_subprotocol(srs, trans_seq)
    }

}


#[cfg(test)]
mod tests {
    
    use super::*;

    #[test]
    fn test_pip() {

        let srs = SRS::new(64);

        let challenges1 = (0..5).map(|_| 
            ZpElement::rand()
        ).collect::<Vec<ZpElement>>();

        let challenges2 = (0..3).map(|_| 
            ZpElement::rand()
        ).collect::<Vec<ZpElement>>();

        let challenges3 = (0..4).map(|_| 
            ZpElement::rand()
        ).collect::<Vec<ZpElement>>();

        let challenges4 = (0..5).map(|_| 
            ZpElement::rand()
        ).collect::<Vec<ZpElement>>();

        let challenge_g = 
            vec![challenges1.clone(), challenges2.clone()];
        let challenge_h = 
            vec![challenges3.clone(), challenges4.clone()];

        let vg1_test = xi::reduce_from_challenges(
            &challenges1, &srs.g_hat_vec
        );
        let vg2_test = xi::reduce_from_challenges(
            &challenges2, &srs.g_hat_vec
        );
        let vh1_test = xi::reduce_from_challenges(
            &challenges3, &srs.h_hat_vec
        );
        let vh2_test = xi::reduce_from_challenges(
            &challenges4, &srs.h_hat_vec
        );

        let vg = vec![vg1_test, vg2_test];
        let vh = vec![vh1_test, vh2_test];

        let pip_protocol = Pip::from(
            vg, vh, challenge_g, challenge_h
        );
        
        let mut trans_seq = ZkTranSeqProver::new(&srs);

        pip_protocol.prove(&srs, &mut trans_seq);
    
        let mut trans = trans_seq.publish_trans();
  
        let result = pip_protocol.verify(
            &srs, &mut trans
        );

        assert_eq!(result, true);

        println!(" * Verifications of Pip passed");

    }

    
}