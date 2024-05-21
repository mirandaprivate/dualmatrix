use crate::setup::SRS;

use crate::utils::curve::{
    ZpElement, GtElement, G1Element, G2Element, 
    ConvertToZp,
};
use crate::utils::dirac;
use crate::utils::fiat_shamir::{TranElem, TranSeq};
use crate::utils::xi;

use crate::zkprotocols::pip::Pip;

use crate::zkprotocols::zk_trans::ZkTranSeqProver;
use crate::zkprotocols::zk_scalars::{ZkSchnorr, ZkSemiMulScalar};


pub struct ZkSipG1 {
    pub c_com: GtElement,
    pub a_com: GtElement,
    pub length: usize,
    pub y: ZpElement,
}

pub struct ZkSipG2 {
    pub c_com: GtElement,
    pub a_com: GtElement,
    pub length: usize,
    pub y: ZpElement,
}

impl ZkSipG1 {
    pub fn new(
        c_com_value: GtElement,
        a_com_value: GtElement, 
        length_value: usize,
        y_value: ZpElement,
    ) -> Self {
        Self {
            c_com: c_com_value,
            a_com: a_com_value,
            length: length_value,
            y: y_value,
        }
    }

    fn get_l_vec(&self, srs: &SRS) -> Vec<ZpElement> {
        let y = self.y;
        let n = self.length;
        
        let step = y.pow(srs.q as u64);
        
        std::iter::successors(
            Some(ZpElement::from(1 as u64)), 
            |&x| Some(x * step)
        ).take(n).collect::<Vec<ZpElement>>()
    }

    fn reduce_l(&self, challenges: &Vec<ZpElement>, srs: &SRS) -> ZpElement {
        xi::phi_s(
            self.y, challenges,
            0 as usize, 
            srs.q as usize,
        )
    }

    pub fn prove<T>(
        &self, srs: &SRS, 
        zk_trans_seq: &mut ZkTranSeqProver, 
        vec_a: &Vec<T>, 
        tilde_c: ZpElement,
        tilde_a: ZpElement,
        pip: &mut Pip,
    ) where T: 'static + ConvertToZp {

        zk_trans_seq.push_without_blinding(
            TranElem::Gt(self.c_com),
        );
        zk_trans_seq.push_without_blinding(
            TranElem::Gt(self.a_com)
        );
        zk_trans_seq.push_without_blinding(
            TranElem::Size(self.length),
        );
        zk_trans_seq.push_without_blinding(
            TranElem::Zp(self.y)
        );

        let x = zk_trans_seq.gen_challenge();

        if (self.length & (self.length - 1)) != 0 {
            panic!("Length is not a power of 2 when proving IpGt");
        }

        let n = self.length;
        let log_n = (n as u64).ilog2() as usize;

        let mut vec_a_current = dirac::vec_convert_to_zp_vec(
            vec_a);
        
        let mut vec_b_current = self.get_l_vec(srs);

        let mut vec_g_current = srs.g_hat_vec[0..n].to_vec();
         
        let mut challenges: Vec<ZpElement> = Vec::new();
        let mut challenges_inv: Vec<ZpElement> = Vec::new();
        let g_0 = srs.g_hat; 

        for j in 0..log_n {
            let current_len = n / 2usize.pow(j as u32);
            
            let a_left = 
                vec_a_current[0..current_len/2].to_vec();
            let a_right = 
                vec_a_current[current_len/2..current_len].to_vec();
            
            let b_left = 
                vec_b_current[0..current_len/2].to_vec();
            let b_right = 
                vec_b_current[current_len/2..current_len].to_vec();
            
                        
            let g_left = 
                vec_g_current[0..current_len/2].to_vec();
            let g_right = 
                vec_g_current[current_len/2..current_len].to_vec();

      
            let l_tr = 
                g_0 * dirac::inner_product(&a_left, &b_right) 
                + x * dirac::inner_product(&a_left, &g_right);
            let r_tr = 
                g_0 * dirac::inner_product(&a_right, &b_left) 
                + x * dirac::inner_product(&a_right, &g_left);
                

            zk_trans_seq.push_gen_blinding(TranElem::G1(l_tr));
            zk_trans_seq.push_gen_blinding(TranElem::G1(r_tr));
            
            let x_j = zk_trans_seq.gen_challenge();
            let x_j_inv = x_j.inv();

            challenges.push(x_j);
            challenges_inv.push(x_j_inv);

            vec_a_current = dirac::vec_addition(
                &a_left,
                &dirac::vec_scalar_mul(
                    &a_right, x_j_inv),
            );

            vec_b_current = dirac::vec_addition(
                &b_left,
                &dirac::vec_scalar_mul(
                    &b_right, x_j),
            );


            vec_g_current = dirac::vec_addition(
                &g_left,
                &dirac::vec_scalar_mul(
                    &g_right, x_j),
            );

        }

        let a_reduce = vec_a_current[0];
        let b_reduce = vec_b_current[0];
        let g_reduce = vec_g_current[0];

        let a_g = a_reduce * g_reduce;

        let (a_reduce_blind, a_reduce_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_reduce));
        zk_trans_seq.push_without_blinding(TranElem::G1(g_reduce));

        pip.challenges_g_vec.push(challenges.clone());
        pip.v_g_vec.push(g_reduce);


        // ///////////////////////////////////////////////////////////
        // Add zk from now on
        // //////////////////////////////////////////////////////////
        let (a_g_blind, a_g_tilde) = 
            zk_trans_seq.push_gen_blinding(TranElem::G1(a_g));

        let length = zk_trans_seq.blind_seq.len();

        
        let rhs_tilde = x * a_g_tilde + b_reduce * a_reduce_tilde; 
           

        let mut current_index = length - 2 - 2 * log_n;
        let mut lhs_tilde = tilde_c + x * tilde_a;
        for j in 0..log_n {
            let l_tilde = zk_trans_seq.blind_seq[current_index];
            let r_tilde = zk_trans_seq.blind_seq[current_index+1];
            let x_j = challenges[j];
            let x_j_inv = challenges_inv[j];
            lhs_tilde = lhs_tilde +  l_tilde * x_j + r_tilde * x_j_inv;
            
            current_index += 2; 
        }

        let eq_tilde = lhs_tilde - rhs_tilde;
        let blind_base = srs.blind_base;
        let eq_tilde_com = eq_tilde * blind_base;

        let zk_semi_mul_1 = ZkSemiMulScalar::new(
            a_g_blind,
            a_reduce_blind,
            g_reduce,
        );

        let zk_schnorr = ZkSchnorr::new(
            eq_tilde_com,
            blind_base,
        );

        zk_semi_mul_1.prove(
            srs,
            zk_trans_seq.get_mut_trans_seq(),
            a_reduce,
            a_g_tilde,
            a_reduce_tilde,
        );

        zk_schnorr.prove(
            zk_trans_seq.get_mut_trans_seq(), 
            eq_tilde,
        )

    }

    pub fn verify_as_subprotocol(
        &self, srs: &SRS, trans_seq: &mut TranSeq, pip: &mut Pip,
    ) -> bool {

        let pointer_old = trans_seq.pointer;
        
        if (
            TranElem::Gt(self.c_com),
            TranElem::Gt(self.a_com),
            TranElem::Size(self.length),
            TranElem::Zp(self.y),
        ) != (
            trans_seq.data[pointer_old],
            trans_seq.data[pointer_old + 1],
            trans_seq.data[pointer_old + 2],
            trans_seq.data[pointer_old + 3],
        ) {
            println!("{:?}", self.c_com);
            println!("{:?}", trans_seq.data[pointer_old]);
            println!("!! Invalid public input when verifying Sip");
            return false;
        } 


        let x: ZpElement;
        if let TranElem::Coin(x_value) 
            = trans_seq.data[pointer_old + 4] {
                x = x_value;
            }
        else {
            return false;
        }

        let n = self.length;
        let log_n = (n as u64).ilog2() as usize;

        trans_seq.pointer = pointer_old + 3 * log_n + 8;

        let mut current_pointer = pointer_old + 5;
        let mut lhs: GtElement = self.c_com.clone() + x * self.a_com.clone();
        
        let mut challenges: Vec<ZpElement> = Vec::new();
        let mut challenges_inv: Vec<ZpElement> = Vec::new();

        for _ in 0..log_n {

            if let (
                TranElem::Gt(l_tr),
                TranElem::Gt(r_tr),
                TranElem::Coin(x_j),
            ) = (
                trans_seq.data[current_pointer],
                trans_seq.data[current_pointer + 1],
                trans_seq.data[current_pointer + 2],
            ) {
                let x_j_inv = x_j.inv();
                lhs = lhs + l_tr * x_j + r_tr * x_j_inv;
                challenges.push(x_j);
                challenges_inv.push(x_j_inv);

            } else {
                println!("!! Invalid transcript when verifying Sip");
                return false;
            }

            current_pointer += 3;
        }

        if let (
            TranElem::Gt(a_reduce_blind),
            TranElem::G1(g_reduce),
            TranElem::Gt(a_g_blind),
        ) = (
            trans_seq.data[current_pointer],
            trans_seq.data[current_pointer+1],
            trans_seq.data[current_pointer+2],
        ) {
            trans_seq.pointer = current_pointer + 3;

            let b_reduce = self.reduce_l(&challenges, srs);

            let rhs = 
                x * a_g_blind + b_reduce * a_reduce_blind;
            
            let eq_com = lhs - rhs;
            
            pip.challenges_g_vec.push(challenges.clone());
            pip.v_g_vec.push(g_reduce);
            

            // ///////////////////////////////////////////////////////////
            // Add zk from now on
            // /////////////////////////////////////////////////////////////
            let blind_base = srs.blind_base;

            let zk_semi_mul_1 = ZkSemiMulScalar::new(
                a_g_blind,
                a_reduce_blind,
                g_reduce,
            );
    
        
            let zk_schnorr = ZkSchnorr::new(
                eq_com,
                blind_base,
            );
    
            let check1 = zk_semi_mul_1.verify_as_subprotocol::<G1Element, ZpElement>(
                srs,
                trans_seq,
            );

    
            let check2 = zk_schnorr.verify_as_subprotocol(trans_seq);

            return check1 && check2;

        } else {
            println!("!! Type check failed in Sip");
            return false;
        }
        
    }

    pub fn verify(&self, srs: &SRS, trans_seq: &mut TranSeq, pip: &mut Pip
    ) -> bool {

        if trans_seq.check_fiat_shamir() == false {
            println!("!! Fiat shamir check failed when verifying Sip");
            return false;
        }

        return self.verify_as_subprotocol(srs, trans_seq, pip);
    }

}


impl ZkSipG2 {
    pub fn new(
        c_com_value: GtElement,
        a_com_value: GtElement, 
        length_value: usize,
        y_value: ZpElement,
    ) -> Self {
        Self {
            c_com: c_com_value,
            a_com: a_com_value,
            length: length_value,
            y: y_value,
        }
    }

    fn get_r_vec(&self) -> Vec<ZpElement> {
        let y = self.y;
        let n = self.length;
        
        std::iter::successors(
            Some(ZpElement::from(1 as u64)),
            |&x| Some(y * x),
        ).take(n).collect::<Vec<ZpElement>>()
    }

    fn reduce_r(&self, challenges: &Vec<ZpElement>) -> ZpElement {
        xi::phi_s(
            self.y, challenges,
            0 as usize, 
            1 as usize,
        )
    }

    pub fn prove<T>(
        &self, srs: &SRS, 
        zk_trans_seq: &mut ZkTranSeqProver, 
        vec_a: &Vec<T>, 
        tilde_c: ZpElement,
        tilde_a: ZpElement,
        pip: &mut Pip,
    ) where T: 'static + ConvertToZp {

        zk_trans_seq.push_without_blinding(
            TranElem::Gt(self.c_com),
        );
        zk_trans_seq.push_without_blinding(
            TranElem::Gt(self.a_com)
        );
        zk_trans_seq.push_without_blinding(
            TranElem::Size(self.length),
        );
        zk_trans_seq.push_without_blinding(
            TranElem::Zp(self.y)
        );

        let x = zk_trans_seq.gen_challenge();

        if (self.length & (self.length - 1)) != 0 {
            panic!("Length is not a power of 2 when proving IpGt");
        }

        let n = self.length;
        let log_n = (n as u64).ilog2() as usize;

        let mut vec_a_current = dirac::vec_convert_to_zp_vec(
            vec_a);
        
        let mut vec_b_current = self.get_r_vec();

        let mut vec_h_current = srs.h_hat_vec[0..n].to_vec();
         
        let mut challenges: Vec<ZpElement> = Vec::new();
        let mut challenges_inv: Vec<ZpElement> = Vec::new();
        let h_0 = srs.h_hat; 

        for j in 0..log_n {
            let current_len = n / 2usize.pow(j as u32);
            
            let a_left = 
                vec_a_current[0..current_len/2].to_vec();
            let a_right = 
                vec_a_current[current_len/2..current_len].to_vec();
            
            let b_left = 
                vec_b_current[0..current_len/2].to_vec();
            let b_right = 
                vec_b_current[current_len/2..current_len].to_vec();
            
                        
            let h_left = 
                vec_h_current[0..current_len/2].to_vec();
            let h_right = 
                vec_h_current[current_len/2..current_len].to_vec();

      
            let l_tr = 
                h_0 * dirac::inner_product(&a_left, &b_right) 
                + x * dirac::inner_product(&a_left, &h_right);
            let r_tr = 
                h_0 * dirac::inner_product(&a_right, &b_left) 
                + x * dirac::inner_product(&a_right, &h_left);
                

            zk_trans_seq.push_gen_blinding(TranElem::G2(l_tr));
            zk_trans_seq.push_gen_blinding(TranElem::G2(r_tr));
            
            let x_j = zk_trans_seq.gen_challenge();
            let x_j_inv = x_j.inv();

            challenges.push(x_j);
            challenges_inv.push(x_j_inv);

            vec_a_current = dirac::vec_addition(
                &a_left,
                &dirac::vec_scalar_mul(
                    &a_right, x_j_inv),
            );

            vec_b_current = dirac::vec_addition(
                &b_left,
                &dirac::vec_scalar_mul(
                    &b_right, x_j),
            );


            vec_h_current = dirac::vec_addition(
                &h_left,
                &dirac::vec_scalar_mul(
                    &h_right, x_j),
            );

        }

        let a_reduce = vec_a_current[0];
        let b_reduce = vec_b_current[0];
        let h_reduce = vec_h_current[0];

        let a_h = a_reduce * h_reduce;

        let (a_reduce_blind, a_reduce_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_reduce));
        zk_trans_seq.push_without_blinding(TranElem::G2(h_reduce));

        pip.challenges_h_vec.push(challenges.clone());
        pip.v_h_vec.push(h_reduce);


        // ///////////////////////////////////////////////////////////
        // Add zk from now on
        // //////////////////////////////////////////////////////////
        let (a_h_blind, a_h_tilde) = 
            zk_trans_seq.push_gen_blinding(TranElem::G2(a_h));

        let length = zk_trans_seq.blind_seq.len();

        
        let rhs_tilde = x * a_h_tilde + b_reduce * a_reduce_tilde; 
           

        let mut current_index = length - 2 - 2 * log_n;
        let mut lhs_tilde = tilde_c + x * tilde_a;
        for j in 0..log_n {
            let l_tilde = zk_trans_seq.blind_seq[current_index];
            let r_tilde = zk_trans_seq.blind_seq[current_index+1];
            let x_j = challenges[j];
            let x_j_inv = challenges_inv[j];
            lhs_tilde = lhs_tilde +  l_tilde * x_j + r_tilde * x_j_inv;
            
            current_index += 2; 
        }

        let eq_tilde = lhs_tilde - rhs_tilde;
        let blind_base = srs.blind_base;
        let eq_tilde_com = eq_tilde * blind_base;

        let zk_semi_mul_1 = ZkSemiMulScalar::new(
            a_h_blind,
            a_reduce_blind,
            h_reduce,
        );

        let zk_schnorr = ZkSchnorr::new(
            eq_tilde_com,
            blind_base,
        );

        zk_semi_mul_1.prove(
            srs,
            zk_trans_seq.get_mut_trans_seq(),
            a_reduce,
            a_h_tilde,
            a_reduce_tilde,
        );

        zk_schnorr.prove(
            zk_trans_seq.get_mut_trans_seq(), 
            eq_tilde,
        )

    }

    pub fn verify_as_subprotocol(
        &self, srs: &SRS, trans_seq: &mut TranSeq, pip: &mut Pip,
    ) -> bool {

        let pointer_old = trans_seq.pointer;
        
        if (
            TranElem::Gt(self.c_com),
            TranElem::Gt(self.a_com),
            TranElem::Size(self.length),
            TranElem::Zp(self.y),
        ) != (
            trans_seq.data[pointer_old],
            trans_seq.data[pointer_old + 1],
            trans_seq.data[pointer_old + 2],
            trans_seq.data[pointer_old + 3],
        ) {
            println!("{:?}", self.c_com);
            println!("{:?}", trans_seq.data[pointer_old]);
            println!("!! Invalid public input when verifying Sip");
            return false;
        } 


        let x: ZpElement;
        if let TranElem::Coin(x_value) 
            = trans_seq.data[pointer_old + 4] {
                x = x_value;
            }
        else {
            return false;
        }

        let n = self.length;
        let log_n = (n as u64).ilog2() as usize;

        let mut current_pointer = pointer_old + 5;
        let mut lhs: GtElement = self.c_com.clone() + x * self.a_com.clone();
        
        let mut challenges: Vec<ZpElement> = Vec::new();
        let mut challenges_inv: Vec<ZpElement> = Vec::new();

        for _ in 0..log_n {

            if let (
                TranElem::Gt(l_tr),
                TranElem::Gt(r_tr),
                TranElem::Coin(x_j),
            ) = (
                trans_seq.data[current_pointer],
                trans_seq.data[current_pointer + 1],
                trans_seq.data[current_pointer + 2],
            ) {
                let x_j_inv = x_j.inv();
                lhs = lhs + l_tr * x_j + r_tr * x_j_inv;
                challenges.push(x_j);
                challenges_inv.push(x_j_inv);

            } else {
                println!("!! Invalid transcript when verifying Sip");
                return false;
            }

            current_pointer += 3;
        }

        if let (
            TranElem::Gt(a_reduce_blind),
            TranElem::G2(h_reduce),
            TranElem::Gt(a_h_blind),
        ) = (
            trans_seq.data[current_pointer],
            trans_seq.data[current_pointer+1],
            trans_seq.data[current_pointer+2],
        ) {
            trans_seq.pointer = current_pointer + 3;

            let b_reduce = self.reduce_r(&challenges);

            let rhs = 
                x * a_h_blind + b_reduce * a_reduce_blind;
            
            let eq_com = lhs - rhs;
            
            pip.challenges_h_vec.push(challenges.clone());
            pip.v_h_vec.push(h_reduce);
            

            // ///////////////////////////////////////////////////////////
            // Add zk from now on
            // /////////////////////////////////////////////////////////////
            let blind_base = srs.blind_base;

            let zk_semi_mul_1 = ZkSemiMulScalar::new(
                a_h_blind,
                a_reduce_blind,
                h_reduce,
            );
    
        
            let zk_schnorr = ZkSchnorr::new(
                eq_com,
                blind_base,
            );
    
            let check1 = zk_semi_mul_1.verify_as_subprotocol::<G2Element, ZpElement>(
                srs,
                trans_seq,
            );


            let check2 = zk_schnorr.verify_as_subprotocol(trans_seq);

            return check1 && check2;

        } else {
            println!("!! Type check failed in Sip");
            return false;
        }
        
    }

    pub fn verify(&self, srs: &SRS, trans_seq: &mut TranSeq, pip: &mut Pip
    ) -> bool {

        if trans_seq.check_fiat_shamir() == false {
            println!("!! Fiat shamir check failed when verifying Sip");
            return false;
        }

        return self.verify_as_subprotocol(srs, trans_seq, pip);
    }

}


#[cfg(test)]
mod tests {
    
    use super::*;
    use rand::Rng;

    #[test]
    fn test_sip() {

        let srs = SRS::new(64);

        let n = 32 as usize;
        let a_vec = (0..n).map(|_| 
            rand::thread_rng().gen_range(0..2i64.pow(26))
        ).collect::<Vec<i64>>();

        let y = ZpElement::rand();
        let step = y;

        let a_com = srs.g_hat * dirac::inner_product(
            &a_vec, &srs.h_hat_vec
        );

        let b_vec =  std::iter::successors(
            Some(ZpElement::from(1 as u64)),
            |&x| Some(step * x),
        ).take(n).collect::<Vec<ZpElement>>();

        let c = dirac::inner_product(&a_vec, &b_vec);

        let blind_base = srs.blind_base;

        let c_tilde = ZpElement::rand();
        let a_tilde = ZpElement::rand();

        let c_com =
            c * srs.g_hat * srs.h_hat + c_tilde * blind_base;
        let a_com = 
            a_com + a_tilde * blind_base;

        let sip = ZkSipG2::new(
            c_com, a_com, n, y,
        );

        let mut trans_seq_prover = ZkTranSeqProver::new(&srs);
        let mut pip = Pip::new();   

        sip.prove::<i64>(
            &srs, 
            &mut trans_seq_prover, 
            &a_vec, 
            c_tilde,
            a_tilde,
            &mut pip,
        );

        pip.prove(&srs, &mut trans_seq_prover);

        let mut trans = trans_seq_prover.publish_trans();
        let mut pip_v = Pip::new();
        let result = sip.verify(&srs, &mut trans, &mut pip_v);

        let result_pip = pip_v.verify(&srs, &mut trans);

        assert_eq!(result, true);
        assert_eq!(result_pip, true);
        assert_eq!(trans.data.len(), trans.pointer);

        println!(" * Verification of Sip passed");

    }

    
}
