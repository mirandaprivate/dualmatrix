//! Implementation of the Scalar Projection protocol
//!
//! Details of this protocol can be found in the DualMatrix paper 
//!
//! To prove that holding a secret matrix \bm{a} 
//! and two Zp elements c_tilde and a_tilde such that
//! 
//! C_a = < \vec{G}, \bm{a}, \vec{H} > + a_tilde * blind_base,
//! C_c = (l^T \bm{a} r) e(\hat{G}, \hat{H}) + c_tilde * blind_base,
// 

use std::time::Instant;


use crate::mat::Mat;
use crate::setup::SRS;

use crate::utils::curve::{
    ZpElement, GtElement, G1Element, 
    ConvertToZp,
};
use crate::utils::dirac::{self, BraKetZp};
use crate::utils::fiat_shamir::{TranElem, TranSeq};
use crate::utils::xi;

use crate::zkprotocols::pip::Pip;

use crate::zkprotocols::zk_trans::ZkTranSeqProver;
use crate::zkprotocols::zk_scalars::{ZkSchnorr, ZkSemiMulScalar};



/// Interface when l_vec and r_vec are arbitrary public vectors
pub struct ZkProj {
    pub c_com: GtElement,
    pub a_com: GtElement,
    pub shape: (usize, usize),
    pub l_vec: Vec<ZpElement>,
    pub r_vec: Vec<ZpElement>,
}

/// Interface when y_l and y_r are vectors generated from a random y
/// In this case, the number of field operations can be optimized
pub struct ZkProjPoly {
    pub c_com: GtElement,
    pub a_com: GtElement,
    pub shape: (usize, usize),
    pub y: ZpElement, 
    pub yp: ZpElement,
    pub z: ZpElement,
    pub q: usize,
}



impl ZkProj {
    pub fn new(
        c_com_value: GtElement, 
        a_com_value: GtElement,  
        shape_value: (usize, usize),
        l_vec: &Vec<ZpElement>,
        r_vec: &Vec<ZpElement>,
    ) -> Self {
        Self {
            c_com: c_com_value,
            a_com: a_com_value,
            shape: shape_value,
            l_vec: l_vec.clone(),
            r_vec: r_vec.clone(),
        }
    }

}

pub trait ZkProjProtocol:ZkProjInterface {

    fn prove<T>(
        &self, srs: &SRS, 
        zk_trans_seq: &mut ZkTranSeqProver, 
        mat_a: (&Vec<Mat<T>>, ZpElement), 
        a_cache: &Vec<G1Element>,
        c_tilde: ZpElement,
        a_tilde: ZpElement,
        pip: &mut Pip,
    ) where 
        T: 'static + ConvertToZp,
        Mat<T>: 'static + BraKetZp, 
    {

        zk_trans_seq.push_without_blinding(TranElem::Gt(self.get_c_com()));
        zk_trans_seq.push_without_blinding(TranElem::Gt(self.get_a_com()));
        zk_trans_seq.push_without_blinding(TranElem::Size(self.get_shape().0));
        zk_trans_seq.push_without_blinding(TranElem::Size(self.get_shape().1));

        let x = zk_trans_seq.gen_challenge();

        let m = self.get_shape().0;
        let n = self.get_shape().1;

        let log_m = (m as u64).ilog2() as usize;
        let log_n = (n as u64).ilog2() as usize;

        let u_0 = srs.g_hat * srs.h_hat;
        let l_vec = self.get_l_vec();
        let r_vec = self.get_r_vec();

        let mut capital_a_current = a_cache[0..n].to_vec();
        let mut h_vec_current = srs.h_hat_vec[0..n].to_vec();
        let mut r_current = r_vec[0..n].to_vec();
        
        let mut challenges_n: Vec<ZpElement> = Vec::new();
        let mut challenges_inv_n: Vec<ZpElement> = Vec::new();

        let mut la= vec![ZpElement::from(0 as u64); m];
        for i in 0 .. mat_a.0.len() {
            let mat = mat_a.0[i].clone();
            let la_current = 
                dirac::vec_scalar_mul(
                    & mat.bra_zp(&l_vec), 
                    mat_a.1.pow(i as u64),
                );
            la = dirac::vec_addition(
                &la, 
                &la_current
            );
        }        

        let mut v_current = dirac::vec_convert_to_zp_vec(
            &la);

        for j in 0..log_n {

            // println!("Within proj proving iteration");


            let current_len = n / 2usize.pow(j as u32);
            
            let v_left = 
                v_current[0..current_len/2].into();
            let v_right = 
                v_current[current_len/2..current_len].into();

            let capital_a_left = 
                capital_a_current[0..current_len/2].into();
            let capital_a_right = 
                capital_a_current[current_len/2..current_len].into();
            
            let r_left = 
                r_current[0..current_len/2].into();
            let r_right = 
                r_current[current_len/2..current_len].into();
            

            let h_left = 
                h_vec_current[0..current_len/2].into();
            let h_right = 
                h_vec_current[current_len/2..current_len].into();

            let l_tr = 
                x * dirac::inner_product(&capital_a_left, &h_right)
                + dirac::inner_product(&v_left, &r_right) * u_0;
            let r_tr = 
                x * dirac::inner_product(&capital_a_right, &h_left)
                + dirac::inner_product(&v_right, &r_left) * u_0;

            zk_trans_seq.push_gen_blinding(TranElem::Gt(l_tr));
            zk_trans_seq.push_gen_blinding(TranElem::Gt(r_tr));
            
            let x_j = zk_trans_seq.gen_challenge();
            let x_j_inv = x_j.inv();

            challenges_n.push(x_j);
            challenges_inv_n.push(x_j_inv);

            v_current = dirac::vec_addition(
                &v_left,
                &dirac::vec_scalar_mul(
                    &v_right, x_j_inv),
            );

            capital_a_current = dirac::vec_addition(
                &capital_a_left,
                &dirac::vec_scalar_mul(
                    &capital_a_right, x_j_inv),
            );

            h_vec_current = dirac::vec_addition(
                &h_left,
                &dirac::vec_scalar_mul(
                    &h_right, x_j),
            );

            r_current = dirac::vec_addition(
                &r_left,
                &dirac::vec_scalar_mul(
                    &r_right, x_j),
            );

        }


        let timer = Instant::now();

        let xi_n_inv = xi::xi_from_challenges(&challenges_inv_n);
        
        let mut a_xi_inv = vec![ZpElement::from(0 as u64); xi_n_inv.len()];
        for i in 0 .. mat_a.0.len() {
            let mat = mat_a.0[i].clone();
            let mat_xi_inv = 
                dirac::vec_scalar_mul(
                    & mat.ket_zp(&xi_n_inv), 
                    mat_a.1.pow(i as u64),
                );
            a_xi_inv = dirac::vec_addition(
                &a_xi_inv, 
                &mat_xi_inv
            );
        }        

        println!(" * Time for ket_zp: {:?}", timer.elapsed());

        let h_reduce = h_vec_current[0];
        let r_reduce = r_current[0];

        let mut a_current = dirac::vec_convert_to_zp_vec(
            &a_xi_inv);
        let mut g_vec_current = srs.g_hat_vec[0..m].to_vec();
        let mut l_current = l_vec[0..m].to_vec();
        
        let mut challenges_m: Vec<ZpElement> = Vec::new();
        let mut challenges_inv_m: Vec<ZpElement> = Vec::new();
        

        for j in 0..log_m {

            // println!("Within scalar_proj proving iteration");


            let current_len = m / 2usize.pow(j as u32);
            
            let a_left = 
                a_current[0..current_len/2].into();
            let a_right = 
                a_current[current_len/2..current_len].into();
            
            let l_left = 
                l_current[0..current_len/2].into();
            let l_right = 
                l_current[current_len/2..current_len].into();
            

            let g_left = 
                g_vec_current[0..current_len/2].into();
            let g_right = 
                g_vec_current[current_len/2..current_len].into();

            let l_tr = 
                x * h_reduce * dirac::inner_product(&a_left, &g_right)
                + r_reduce 
                * dirac::inner_product(&a_left, &l_right) * u_0;
            let r_tr = 
                x * h_reduce * dirac::inner_product(&a_right, &g_left)
                + r_reduce 
                * dirac::inner_product(&a_right, &l_left) * u_0;

            zk_trans_seq.push_gen_blinding(TranElem::Gt(l_tr));
            zk_trans_seq.push_gen_blinding(TranElem::Gt(r_tr));
            
            let x_j = zk_trans_seq.gen_challenge();
            let x_j_inv = x_j.inv();

            challenges_m.push(x_j);
            challenges_inv_m.push(x_j_inv);

            a_current = dirac::vec_addition(
                &a_left,
                &dirac::vec_scalar_mul(
                    &a_right, x_j_inv),
            );

            g_vec_current = dirac::vec_addition(
                &g_left,
                &dirac::vec_scalar_mul(
                    &g_right, x_j),
            );

            l_current = dirac::vec_addition(
                &l_left,
                &dirac::vec_scalar_mul(
                    &l_right, x_j),
            );

        }

        let a_reduce = a_current[0];
        let g_reduce = g_vec_current[0];


        zk_trans_seq.push_without_blinding(TranElem::G1(g_reduce));
        zk_trans_seq.push_without_blinding(TranElem::G2(h_reduce));

        pip.challenges_g_vec.push(challenges_m.clone());
        pip.v_g_vec.push(g_reduce);
        pip.challenges_h_vec.push(challenges_n.clone());
        pip.v_h_vec.push(h_reduce);

        // /////////////////////////////////////////////////////////////
        // Add Zero-Knowledge from now on
        // /////////////////////////////////////////////////////////////
        

        let xi_l = self.reduce_l(&challenges_m);
        let xi_r = self.reduce_r(&challenges_n);

        let (a_reduce_blind, a_reduce_tilde) = 
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_reduce));
        
            
        let base_rhs =  
            xi_l * xi_r * srs.g_hat * srs.h_hat
            + x * g_reduce * h_reduce;
        
        let rhs_com = 
            base_rhs * a_reduce;

        let (rhs_blind, rhs_tilde) = 
            zk_trans_seq.push_gen_blinding( 
            TranElem::Gt(rhs_com)
            );
        
        let mut lhs_tilde = c_tilde + x * a_tilde;

        let length = zk_trans_seq.blind_seq.len();
        let mut current_index = length - 2 - 2 * log_n - 2 * log_m;

        // assert_eq!(current_index, 0);

        for j in 0..log_n {
            let l_tilde = zk_trans_seq.blind_seq[current_index];
            let r_tilde = zk_trans_seq.blind_seq[current_index+1];
            let x_j = challenges_n[j];
            let x_j_inv = challenges_inv_n[j];
            lhs_tilde = lhs_tilde + l_tilde * x_j + r_tilde * x_j_inv;
            current_index +=2;
        }  

        for j in 0..log_m {
            let l_tilde = zk_trans_seq.blind_seq[current_index];
            let r_tilde = zk_trans_seq.blind_seq[current_index+1];
            let x_j = challenges_m[j];
            let x_j_inv = challenges_inv_m[j];
            lhs_tilde = lhs_tilde + l_tilde * x_j + r_tilde * x_j_inv;
            current_index +=2;
        }  

        let eq_tilde = lhs_tilde - rhs_tilde;
        let blind_base = srs.blind_base;
        let eq_tilde_com = eq_tilde * blind_base;

        let zk_semi_mul = ZkSemiMulScalar::new(
            rhs_blind,
            a_reduce_blind,
            base_rhs,
        );

        let zk_schnorr = ZkSchnorr::new(
            eq_tilde_com,
            blind_base,
        );


        zk_semi_mul.prove(
            srs, zk_trans_seq.get_mut_trans_seq(), 
            a_reduce, rhs_tilde, a_reduce_tilde
        );
        zk_schnorr.prove(
            zk_trans_seq.get_mut_trans_seq(), 
            eq_tilde,
        );

    }

    fn verify_as_subprotocol(
        &self, srs: &SRS, trans_seq: &mut TranSeq, pip: &mut Pip
    ) -> bool {

        let pointer_old = trans_seq.pointer;
        
        if (
            TranElem::Gt(self.get_c_com()),
            TranElem::Gt(self.get_a_com()),
            TranElem::Size(self.get_shape().0),
            TranElem::Size(self.get_shape().1)
        ) != (
            trans_seq.data[pointer_old],
            trans_seq.data[pointer_old + 1],
            trans_seq.data[pointer_old + 2], 
            trans_seq.data[pointer_old + 3],
        ) {
            println!("!! Invalid public input when verifying Proj");
            return false;
        } 

        let x: ZpElement;
        
        if let TranElem::Coin(x_read) = 
            trans_seq.data[pointer_old + 4] 
        {
            x = x_read;
        } else {
            println!("!! Invalid transcript when verifying Proj");
            return false;
        }

        let m = self.get_shape().0;
        let n = self.get_shape().1;
        if m & (m - 1) != 0 || n & (n - 1) != 0 {
            panic!("Invalid shape when verifying Proj");
        }
        let log_m = (m as u64).ilog2() as usize;
        let log_n = (n as u64).ilog2() as usize;

        let mut current_pointer = pointer_old + 5;
        let mut lhs: GtElement = 
            self.get_c_com().clone() + x * self.get_a_com().clone();
        
        let mut challenges_n: Vec<ZpElement> = Vec::new();
        let mut challenges_inv_n: Vec<ZpElement> = Vec::new();

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
                challenges_n.push(x_j);
                challenges_inv_n.push(x_j_inv);

            } else {
                println!("!! Invalid transcript when verifying Proj");
                return false;
            }

            current_pointer += 3;
        }

        let mut challenges_m: Vec<ZpElement> = Vec::new();
        let mut challenges_inv_m: Vec<ZpElement> = Vec::new();

        for _ in 0..log_m {

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
                challenges_m.push(x_j);
                challenges_inv_m.push(x_j_inv);

            } else {
                println!("!! Invalid transcript when verifying Proj");
                return false;
            }

            current_pointer += 3;
        }


        let xi_l = self.reduce_l(&challenges_m);
        let xi_r = self.reduce_r(&challenges_n);

        if let (
            TranElem::G1(g_reduce),
            TranElem::G2(h_reduce),
            TranElem::Gt(a_reduce_blind),
            TranElem::Gt(rhs_blind),
        ) = (
            trans_seq.data[current_pointer],
            trans_seq.data[current_pointer+1],
            trans_seq.data[current_pointer+2],
            trans_seq.data[current_pointer+3],

        ) {

            trans_seq.pointer = current_pointer + 4;

            let eq_tilde_com = lhs - rhs_blind;
            
            let rhs_base = xi_l * xi_r * srs.g_hat * srs.h_hat
                + x * g_reduce * h_reduce;
            let blind_base = srs.blind_base;

            let zk_semi_mul = ZkSemiMulScalar::new(
                rhs_blind,
                a_reduce_blind,
                rhs_base,
            );
    
            let zk_schnorr = ZkSchnorr::new(
                eq_tilde_com,
                blind_base,
            );


            let check1 = zk_semi_mul.verify_as_subprotocol::<GtElement, ZpElement>(
                srs, trans_seq
            );
            let check2 = zk_schnorr.verify_as_subprotocol(trans_seq);

            pip.challenges_g_vec.push(challenges_m.clone());
            pip.v_g_vec.push(g_reduce);
            pip.challenges_h_vec.push(challenges_n.clone());
            pip.v_h_vec.push(h_reduce);

            // println!(" check 1 {:?}", check1);
            // println!(" check 2 {:?}", check2);
            // println!(" check 3 {:?}", check3);
            // println!(" check 4 {:?}", check4);
            return check1 && check2;

        } else {
            println!("!! Invalid transcript when verifying Proj");
            return false;
        }

    }

    fn verify(&self, srs: &SRS, trans_seq: &mut TranSeq, pip: &mut Pip
    ) -> bool {

        if trans_seq.check_fiat_shamir() == false {
            println!("!! Fiat shamir check failed when verifying Proj");
            return false;
        }

        self.verify_as_subprotocol(srs, trans_seq, pip)
    }

}



pub trait ZkProjInterface {
    fn get_c_com(&self) -> GtElement;
    fn get_a_com(&self) -> GtElement;
    fn get_shape(&self) -> (usize, usize);
    fn reduce_l(&self, challenges: &Vec<ZpElement>) -> ZpElement;
    fn reduce_r(&self, challenges: &Vec<ZpElement>) -> ZpElement;
    fn get_l_vec(&self) -> Vec<ZpElement>;
    fn get_r_vec(&self) -> Vec<ZpElement>;
}

impl ZkProjInterface for ZkProj {
    fn reduce_l(&self, challenges: &Vec<ZpElement>) -> ZpElement {
        xi::reduce_from_challenges(challenges, &self.get_l_vec())
    }

    fn reduce_r(&self, challenges: &Vec<ZpElement>) -> ZpElement {
        xi::reduce_from_challenges(challenges, &self.get_r_vec())
    }

    fn get_l_vec(&self) -> Vec<ZpElement> {
        self.l_vec.clone()
    }

    fn get_r_vec(&self) -> Vec<ZpElement> {
        self.r_vec.clone()
    }

    fn get_c_com(&self) -> GtElement {
        self.c_com
    }

    fn get_a_com(&self) -> GtElement {
        self.a_com
    }

    fn get_shape(&self) -> (usize, usize) {
        self.shape
    }

}

impl ZkProjInterface for ZkProjPoly {
    fn reduce_l(&self, challenges: &Vec<ZpElement>) -> ZpElement {
        
        let part_1 = xi::phi_s(
            self.y, 
            challenges,
            0 as usize, 
            self.q as usize,
        );

        let part_2 = xi::phi_s(
            self.yp, 
            challenges,
            0 as usize, 
            self.q as usize,
        );

        let result = part_1 + part_2 * self.z;

        result
    }

    fn reduce_r(&self, challenges: &Vec<ZpElement>) -> ZpElement {
        
        let part_1 = xi::phi_s(
            self.y, challenges,
            0 as usize, 
            1 as usize,
        );

        let part_2 = xi::phi_s(
            self.yp, challenges,
            0 as usize, 
            1 as usize,
        );

        let result = part_1 + part_2 * self.z * self.z;

        result
    }

    fn get_l_vec(&self) -> Vec<ZpElement> {
        let m = self.get_shape().0;
        let step = self.y.pow(self.q as u64);
        let stepp = self.yp.pow(self.q as u64);
        let z = self.z;

        let part_1 = std::iter::successors(
            Some(ZpElement::from(1 as u64)), 
            |&x| Some(x * step)
        ).take(m).collect::<Vec<ZpElement>>();

        let part_2 = std::iter::successors(
            Some(ZpElement::from(1 as u64)), 
            |&x| Some(x * stepp )
        ).take(m).collect::<Vec<ZpElement>>();

        dirac::vec_addition(&part_1,
            &dirac::vec_scalar_mul(&part_2, z) 
            )
    }

    fn get_r_vec(&self) -> Vec<ZpElement> {
        let y = self.y;
        let yp = self.yp;
        let n = self.get_shape().1;
        let z = self.z;
        
        let part_1 = std::iter::successors(
            Some(ZpElement::from(1 as u64)),
            |&x| Some(y * x),
        ).take(n).collect::<Vec<ZpElement>>();


        let part_2 = std::iter::successors(
            Some(ZpElement::from(1 as u64)),
            |&x| Some(yp * x),
        ).take(n).collect::<Vec<ZpElement>>();


        dirac::vec_addition(&part_1,
            &dirac::vec_scalar_mul(&part_2, z * z) 
            )
    }

    fn get_c_com(&self) -> GtElement {
        self.c_com
    }

    fn get_a_com(&self) -> GtElement {
        self.a_com
    }

    fn get_shape(&self) -> (usize, usize) {
        self.shape
    }

}


impl ZkProjPoly {
    pub fn new(
        c_com_value: GtElement, 
        a_com_value: GtElement,  
        shape_value: (usize, usize),
        y_value: ZpElement,
        yp_value: ZpElement,  
        z_value: ZpElement,
        q_value: usize,
    ) -> Self {
        Self {
            c_com: c_com_value,
            a_com: a_com_value,
            shape: shape_value,
            y: y_value,
            yp: yp_value,
            z: z_value,
            q: q_value,
        }
    }
}

impl ZkProjProtocol for ZkProj {}
impl ZkProjProtocol for ZkProjPoly {}


#[cfg(test)]
mod tests {
    
    use super::*;

    use rand::Rng;

    use crate::commit_mat::CommitMat;


    #[test]
    fn test_proj() {

        let srs = SRS::new(64);

        let m = 16 as usize;
        let n = 32 as usize;

        let a_data = (0..m).into_iter()
            .zip((0..n).into_iter())
            .map(|(i, j)| 
                (i, j, rand::thread_rng().gen::<u32>() as i64 )
            ).collect::<Vec<(usize, usize, i64)>>();

        
        let a = Mat::new_from_data_vec(
            "a_test", 
            (m, n), 
            a_data
        );

        let (a_com, a_cache_cm) 
            = a.commit_col_major(
                &srs.g_hat_vec, &srs.h_hat_vec
            );
    

        let l_vec = (0..m).map(|_| 
            ZpElement::rand()
        ).collect::<Vec<ZpElement>>();

        let r_vec = (0..n).map(|_| 
            ZpElement::rand()
        ).collect::<Vec<ZpElement>>();

        let c = a.braket_zp(&l_vec, &r_vec);

        let c_com = c * srs.g_hat * srs.h_hat;

        let a_tilde = ZpElement::rand();
        let c_tilde = ZpElement::rand();

        let c_blind = c_com + c_tilde * srs.blind_base;
        let a_blind = a_com + a_tilde * srs.blind_base;

        let proj_protocol = ZkProj::new(
            c_blind,
            a_blind, 
            (m, n), 
            &l_vec, 
            &r_vec,
        );

        let mut pip = Pip::new();

        let mut zk_trans_seq = ZkTranSeqProver::new(&srs);

        let mat_vec = (&vec![a], ZpElement::from(1 as u64));

        proj_protocol.prove::<i64>(
            &srs, 
            &mut zk_trans_seq, 
            mat_vec,
            &a_cache_cm,
            c_tilde,
            a_tilde,
            &mut pip,
        );

        pip.prove(&srs, &mut zk_trans_seq);

        let mut pip_v = Pip::new();
        let mut trans_seq = zk_trans_seq.publish_trans();

        let result = proj_protocol.verify_as_subprotocol(
            &srs, &mut trans_seq, &mut pip_v
        );

        let result2 = pip_v.verify(
            &srs, &mut trans_seq
        );
        

        assert_eq!(result && result2, true);

        println!(" * Verification of Proj passed");


    }

    
}
