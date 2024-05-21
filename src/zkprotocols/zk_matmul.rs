//! Zero-Knowledge implementation of the zkMatMul protocol
//!
//! Details of this protocol can be found in the DualMatrix paper 
//!
//! To prove that holding three secret matrix \bm{c}, \bm{a}, \bm{b}
//! and three secret Zp elements c_tilde, a_tilde, b_tilde such that 
//! 
//! \bm{c} = \bm{a} \bm{b},
//! C_c = < \vec{G}, \bm{c}, \vec{H} > + c_tilde * blind_base, 
//! C_a = < \vec{G}, \bm{a}, \vec{H} > + a_tilde * blind_base,
//! C_b = < \vec{G}, \bm{b}, \vec{H} > + b_tilde * blind_base,
//! 
use crate::mat::{Mat,ToZpMat};
use crate::setup::SRS;

use crate::utils::curve::{
    ZpElement, GtElement, G1Element,
    ConvertToZp,
};
use crate::utils::dirac::{self, vec_scalar_mul, BraKetZp};
use crate::utils::fiat_shamir::{TranElem, TranSeq};

use crate::zkprotocols::zk_proj::{ZkProjPoly, ZkProjProtocol};
use crate::zkprotocols::zk_ip_gt::ZkIpGt;
use crate::zkprotocols::zk_sip::{ZkSipG1,ZkSipG2};
use crate::zkprotocols::pip::Pip;

use crate::zkprotocols::zk_trans::ZkTranSeqProver;




/// Interface for the matMul protocol
pub struct ZkMatMul {
    pub c_blind: GtElement,
    pub a_blind: GtElement,
    pub b_blind: GtElement,
    pub m: usize,
    pub n: usize,
    pub l: usize,
}


impl ZkMatMul {
    pub fn new(
        c_com_value: GtElement, 
        a_com_value: GtElement, 
        b_com_value: GtElement,  
        m_value: usize,
        n_value: usize,
        l_value: usize,
    ) -> Self {
        Self {
            c_blind: c_com_value,
            a_blind: a_com_value,
            b_blind: b_com_value,
            m: m_value,
            n: n_value,
            l: l_value,
         }
    }

    pub fn prove<T, U, V>(
        &self, srs: &SRS, 
        zk_trans_seq: &mut ZkTranSeqProver, 
        mat_c: Mat<T>, 
        mat_a: Mat<U>, 
        mat_b: Mat<V>,
        cache_c: &Vec<G1Element>,
        cache_a: &Vec<G1Element>,
        cache_b: &Vec<G1Element>,
        c_tilde: ZpElement,
        a_tilde: ZpElement,
        b_tilde: ZpElement,
    ) where 
        T: 'static + ConvertToZp,
        Mat<T>: 'static + BraKetZp + ToZpMat, 
        U: 'static + ConvertToZp,
        Mat<T>: 'static + BraKetZp + ToZpMat, 
        V: 'static + ConvertToZp,
        Mat<T>: 'static + BraKetZp + ToZpMat, 
    {
        
        zk_trans_seq.push_without_blinding(TranElem::Gt(self.c_blind));
        zk_trans_seq.push_without_blinding(TranElem::Gt(self.a_blind));
        zk_trans_seq.push_without_blinding(TranElem::Gt(self.b_blind));

        zk_trans_seq.push_without_blinding(TranElem::Size(self.m));
        zk_trans_seq.push_without_blinding(TranElem::Size(self.n));
        zk_trans_seq.push_without_blinding(TranElem::Size(self.l));
      
        let y = zk_trans_seq.gen_challenge();

        let m = self.m;
        let n = self.n;
        let l = self.l;


        if m & (m - 1) != 0 || n & (n - 1) != 0 || l & (l - 1) != 0
            || m != mat_c.shape.0 || m != mat_a.shape.0
            || n != mat_c.shape.1 || n != mat_b.shape.1
            || l != mat_a.shape.1 || l != mat_b.shape.0 
        {
            panic!("Invalid shape when proving MatMul");
        }

        let mat_a_zp = mat_a.to_zp_mat();
        std::mem::drop(mat_a);
        let mat_b_zp = mat_b.to_zp_mat();
        std::mem::drop(mat_b);
        let mat_c_zp = mat_c.to_zp_mat();
        std::mem::drop(mat_c);

        let q = srs.q;
        let max_m = std::cmp::max(m, l);
        let max_n = std::cmp::max(n, l);
        
        let step = y.pow(q as u64);

        let y_l = std::iter::successors(
                Some(ZpElement::from(1 as u64)), 
                |&x| Some(x * step)
            ).take(max_m).collect::<Vec<ZpElement>>();
        let y_r = std::iter::successors(
                Some(ZpElement::from(1 as u64)),
                |&x| Some(x * y)
           ).take(max_n).collect::<Vec<ZpElement>>();


        let a_y = mat_a_zp.bra_zp(&y_l);
        let b_y = mat_b_zp.bra_zp(&y_l);
        let c_y = mat_c_zp.bra_zp(&y_l);

        let b_yr = mat_b_zp.ket_zp(&y_r);

        let a_yy = dirac::inner_product(&a_y, &y_r);
        let b_yy = dirac::inner_product(&b_y, &y_r);
        let c_yy = dirac::inner_product(&c_y, &y_r);

        let g_0 = srs.g_hat;
        let h_0 = srs.h_hat;
        
        let a_y_com = g_0 * dirac::inner_product(
            &a_y,
            &srs.h_hat_vec[0..l].to_vec(), 
        );
        let b_yr_com = h_0 * dirac::inner_product(
            &b_yr,
            &srs.g_hat_vec[0..l].to_vec(), 
        );


        let (ay_blind, ay_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Gt(a_y_com));
        let (byr_blind, byr_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Gt(b_yr_com));

        let (cyy_blind, cyy_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(c_yy));
        let (ayy_blind, ayy_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_yy));
        let (byy_blind, byy_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(b_yy));

        let yp = zk_trans_seq.gen_challenge();

        let stepp = yp.pow(q as u64);

        let yp_l = std::iter::successors(
                Some(ZpElement::from(1 as u64)), 
                |&x| Some(x * stepp)
            ).take(max_m).collect::<Vec<ZpElement>>();
        let yp_r = std::iter::successors(
                Some(ZpElement::from(1 as u64)),
                |&x| Some(x * yp)
           ).take(max_n).collect::<Vec<ZpElement>>();
        
        let a_yp = mat_a_zp.bra_zp(&yp_l);
        let b_yp = mat_b_zp.bra_zp(&yp_l);
        let c_yp = mat_c_zp.bra_zp(&yp_l);
        
        let a_yyp = dirac::inner_product(&a_y, &yp_r);
        let b_yyp = dirac::inner_product(&b_y, &yp_r);
        let c_yyp = dirac::inner_product(&c_y, &yp_r);
           
        let a_ypy = dirac::inner_product(&a_yp, &y_r);
        let b_ypy = dirac::inner_product(&b_yp, &y_r);
        let c_ypy = dirac::inner_product(&c_yp, &y_r);

        let a_ypyp = dirac::inner_product(&a_yp, &yp_r);
        let b_ypyp = dirac::inner_product(&b_yp, &yp_r);
        let c_ypyp = dirac::inner_product(&c_yp, &yp_r);

        let (cyyp_blind, cyyp_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(c_yyp));
        let (ayyp_blind, ayyp_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_yyp));
        let (byyp_blind, byyp_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(b_yyp));
        
        let (cypy_blind, cypy_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(c_ypy));
        let (aypy_blind, aypy_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_ypy));
        let (bypy_blind, bypy_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(b_ypy));

        let (cypyp_blind, cypyp_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(c_ypyp));
        let (aypyp_blind, aypyp_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(a_ypyp));
        let (bypyp_blind, bypyp_tilde) =
            zk_trans_seq.push_gen_blinding(TranElem::Zp(b_ypyp));

        let z = zk_trans_seq.gen_challenge();

        let c_gt = cyy_blind + z * cypy_blind 
            +  z.pow(2) * cyyp_blind  + z.pow(3) * cypyp_blind
            + z.pow(4) * ayy_blind + z.pow(5) * aypy_blind
            + z.pow(6) * ayyp_blind + z.pow(7) * aypyp_blind
            + z.pow(8) * byy_blind + z.pow(9) * bypy_blind
            + z.pow(10) * byyp_blind + z.pow(11) * bypyp_blind;

        let c_gt_tilde = cyy_tilde + z * cypy_tilde 
        +  z.pow(2) * cyyp_tilde  + z.pow(3) * cypyp_tilde
        + z.pow(4) * ayy_tilde + z.pow(5) * aypy_tilde
        + z.pow(6) * ayyp_tilde + z.pow(7) * aypyp_tilde
        + z.pow(8) * byy_tilde + z.pow(9) * bypy_tilde
        + z.pow(10) * byyp_tilde + z.pow(11) * bypyp_tilde;

        let c_abc = self.c_blind 
            + self.a_blind * z.pow(4) + self.b_blind * z.pow(8);
        let c_abc_tilde = c_tilde 
            + a_tilde * z.pow(4) + b_tilde * z.pow(8);

        
        let cache_abc = dirac::vec_addition(
            &cache_c,
            &dirac::vec_addition(
                &vec_scalar_mul(&cache_a, z.pow(4)),
                &vec_scalar_mul(&cache_b, z.pow(8)),
            )
        );


        let ip1 = ZkProjPoly::new(
            c_gt, 
            c_abc,
            (max_m,max_n), 
            y,
            yp,
            z, 
            srs.q,
        );

        let ip2 = ZkSipG2::new(
            ayyp_blind, 
            ay_blind,
            l, 
            yp,
        );

        let ip3 = ZkSipG1::new(
            bypy_blind, 
            byr_blind,
            l, 
            yp,
        );

        let ip4 = ZkIpGt::new(
            cyy_blind, 
            ay_blind,  
            byr_blind,
            l, 
        );

        let mut pip = Pip::new();


        ip1.prove::<ZpElement>(
            srs, zk_trans_seq,
            (&vec![mat_c_zp, mat_a_zp, mat_b_zp], z.pow(4)), 
            &cache_abc,
            c_gt_tilde,
            c_abc_tilde,
            &mut pip, 
        );

        ip2.prove::<ZpElement>(
            srs, zk_trans_seq,
            &a_y,
            ayyp_tilde,
            ay_tilde,
            &mut pip,
        );

        ip3.prove::<ZpElement>(
            srs, zk_trans_seq,
            &b_yr,
            bypy_tilde,
            byr_tilde,
            &mut pip,
        );

        ip4.prove::<ZpElement>(
            srs, zk_trans_seq, 
            &a_y, 
            &b_yr,
            cyy_tilde, 
            ay_tilde, 
            byr_tilde,
            &mut pip,
        );

        pip.prove(srs, zk_trans_seq);

     
    }

    pub fn verify_as_subprotocol(
        &self, srs: &SRS, trans_seq: &mut TranSeq
    ) -> bool {

        let pointer_old = trans_seq.pointer;
        
        if (
            TranElem::Gt(self.c_blind),
            TranElem::Gt(self.a_blind),
            TranElem::Gt(self.b_blind),
            TranElem::Size(self.m),
            TranElem::Size(self.n),
            TranElem::Size(self.l),
        ) != (
            trans_seq.data[pointer_old],
            trans_seq.data[pointer_old + 1],
            trans_seq.data[pointer_old + 2], 
            trans_seq.data[pointer_old + 3],
            trans_seq.data[pointer_old + 4],
            trans_seq.data[pointer_old + 5],
        ) {
            println!("!! Invalid public input when verifying MatMul");
            return false;
        } 


        let m = self.m;
        let n = self.n;
        let l = self.l;
        if m & (m - 1) != 0 || n & (n - 1) != 0 || l & (l - 1) != 0 {
            panic!("Invalid shape when verifying MatMul");
        }

        let max_m = std::cmp::max(m, l);
        let max_n = std::cmp::max(n, l);

        if let (
            TranElem::Coin(y),
            TranElem::Gt(ay_blind),
            TranElem::Gt(byr_blind),
            TranElem::Gt(cyy_blind),
            TranElem::Gt(ayy_blind),
            TranElem::Gt(byy_blind),
            TranElem::Coin(yp),
            TranElem::Gt(cyyp_blind),
            TranElem::Gt(ayyp_blind),
            TranElem::Gt(byyp_blind),
            TranElem::Gt(cypy_blind),
            TranElem::Gt(aypy_blind),
            TranElem::Gt(bypy_blind),
            TranElem::Gt(cypyp_blind),
            TranElem::Gt(aypyp_blind),
            TranElem::Gt(bypyp_blind),
            TranElem::Coin(z),
        ) = (
            trans_seq.data[pointer_old + 6],
            trans_seq.data[pointer_old + 7],
            trans_seq.data[pointer_old + 8],
            trans_seq.data[pointer_old + 9],
            trans_seq.data[pointer_old + 10],
            trans_seq.data[pointer_old + 11],
            trans_seq.data[pointer_old + 12], 
            trans_seq.data[pointer_old + 13],
            trans_seq.data[pointer_old + 14],
            trans_seq.data[pointer_old + 15],
            trans_seq.data[pointer_old + 16],
            trans_seq.data[pointer_old + 17],
            trans_seq.data[pointer_old + 18],
            trans_seq.data[pointer_old + 19],
            trans_seq.data[pointer_old + 20],
            trans_seq.data[pointer_old + 21],
            trans_seq.data[pointer_old + 22],
        ) {
            trans_seq.pointer = pointer_old + 23;

            let c_gt = cyy_blind + z * cypy_blind 
            +  z.pow(2) * cyyp_blind  + z.pow(3) * cypyp_blind
            + z.pow(4) * ayy_blind + z.pow(5) * aypy_blind
            + z.pow(6) * ayyp_blind + z.pow(7) * aypyp_blind
            + z.pow(8) * byy_blind + z.pow(9) * bypy_blind
            + z.pow(10) * byyp_blind + z.pow(11) * bypyp_blind;

            let c_abc = self.c_blind 
                + self.a_blind * z.pow(4) + self.b_blind * z.pow(8);

            
            let ip1 = ZkProjPoly::new(
                c_gt, 
                c_abc,
                (max_m,max_n), 
                y,
                yp,
                z, 
                srs.q,
            );

            let ip2 = ZkSipG2::new(
                ayyp_blind, 
                ay_blind,
                l, 
                yp,
            );

            let ip3 = ZkSipG1::new(
                bypy_blind, 
                byr_blind,
                l, 
                yp,
            );

            let ip4 = ZkIpGt::new(
                cyy_blind, 
                ay_blind,  
                byr_blind,
                l, 
            );

            let mut pip = Pip::new();

            let check1 = ip1.verify_as_subprotocol(srs, trans_seq, &mut pip);
            // println!(" * IP1 check: {}", check1);
            let check2 = ip2.verify_as_subprotocol(srs, trans_seq, &mut pip);
            // println!(" * IP2 check: {}", check2);
            let check3 = ip3.verify_as_subprotocol(srs, trans_seq, &mut pip);
            // println!(" * IP3 check: {}", check3);
            let check4 = ip4.verify_as_subprotocol(srs, trans_seq, &mut pip);
            // println!(" * IP4 check: {}", check4);

            let check5 = pip.verify(srs, trans_seq);
            // println!(" * Pip check: {}", check5);

            return check1 && check2 && check3 && check4 && check5;

        } else {
            println!("!! Invalid Transcript type when verifying MatMul");
            return false;
        } 

        
    }

    pub fn verify(&self, srs: &SRS, trans_seq: &mut TranSeq
    ) -> bool {

        if trans_seq.check_fiat_shamir() == false {
            println!("!! Fiat shamir check failed when verifying LeftProj");
            return false;
        }

        self.verify_as_subprotocol(srs, trans_seq)
    }

}


#[cfg(test)]
mod tests {
    
    use super::*;
    use crate::commit_mat::CommitMat;

    use crate::utils::curve::ZpElement;
    use crate::utils::test_data;
   
    #[test]
    fn test_matmul() {

        let srs = SRS::new(64);

        let (c, a, b) = 
            test_data::gen_test_matrices_not_square();

        let (c_com, c_cache_cm) =
            c.commit_col_major(
                &srs.g_hat_vec, &srs.h_hat_vec
            );

        let (a_com, a_cache_cm) = 
            a.commit_col_major(
                &srs.g_hat_vec, &srs.h_hat_vec
            );
        
        let (b_com, b_cache_cm) = 
            b.commit_col_major(
                &srs.g_hat_vec, &srs.h_hat_vec
            );
        
        let c_tilde = ZpElement::rand();
        let a_tilde = ZpElement::rand();
        let b_tilde = ZpElement::rand();

        let blind_base = srs.blind_base;

        let matmul_protocol = ZkMatMul::new(
            c_com + c_tilde * blind_base,
            a_com + a_tilde * blind_base,
            b_com + b_tilde * blind_base, 
            c.shape.0,
            c.shape.1,
            a.shape.1,
        );


        let mut zk_trans_seq = ZkTranSeqProver::new(&srs);

        matmul_protocol.prove::<i128, i64, i64>(
            &srs,
            &mut zk_trans_seq,
            c, a, b,
            &c_cache_cm, &a_cache_cm, &b_cache_cm, 
            c_tilde, a_tilde, b_tilde,
        );

        let mut trans_seq = zk_trans_seq.publish_trans();

        let result = matmul_protocol.verify(
            &srs, &mut trans_seq
        );

        assert_eq!(trans_seq.data.len(), trans_seq.pointer);

        assert_eq!(result, true);

        println!(" * Verification of MatMul passed");

    }

    
}
