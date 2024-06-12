//! Utility functions for the braket operation
//! 
//! Parallelized whenever possible
//! 

use std::sync::Arc;

use rayon::{ThreadPoolBuilder, prelude::*};


use crate::utils::curve::{
    Zero, ZpElement, G1Element, G2Element, GtElement,
};

use crate::utils::dirac;
use crate::mat::Mat;

use crate::config::NUM_THREADS;

use super::curve::Double;

pub fn fix_base_double(g_vec: &Vec<G1Element>, bit_length: usize) 
-> Vec<Vec<G1Element>>  {
    
    let mut g_double_vec: Vec<G1Element> = g_vec.clone();
    let mut g_double_mat: Vec<Vec<G1Element>> = Vec::new();
    
    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    for _ in 0..bit_length{

        g_double_mat.push(g_double_vec.clone());

        g_double_vec = pool.install(|| {
            g_double_vec.par_iter().map(|v| {
                v.double()
            }).collect()
        });
    }

    g_double_mat
}

pub fn first_tier(witness_mat: &Vec<Vec<i64>>, g_double_mat: &Vec<Vec<G1Element>>)
-> Vec<G1Element> {
    
    let bit_length = g_double_mat.len();
    let mat_m = witness_mat[0].len();

    let mut g_cache: Vec<G1Element> = vec![G1Element::zero(); mat_m];
    
    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    let abs_sign_mat: Vec<Vec<(u64, bool)>> = pool.install(|| {
        witness_mat.par_iter().map(|col| {
            col.iter().map(|&x| (x.abs() as u64, x < 0) ).collect()
        }).collect()
    });

    // println!("witness_mat: {:?}", witness_mat);

    // println!("abs_sign_mat: {:?}", abs_sign_mat);


    for j_bit in 0..bit_length{
        // println!("j_bit: {:?}", j_bit);

        let g_double_vec = &g_double_mat[j_bit];
        let g_double_vec_arc = Arc::new(g_double_vec);

        let g_cache_current = pool.install(|| {
            abs_sign_mat.par_iter()
            .map(|col| {
                
                let g_double_vec_clone = Arc::clone(&g_double_vec_arc);
                let mut g_com_col = G1Element::zero();
                
                col.iter().enumerate().for_each(|(i, &(val, sign))| {
                    // println!("i:{:?}, val: {:?}, sign: {:?}", i, val, sign);
                    // if sign {count_neg += 1;}
                    if (val >> j_bit) & 1 == 1 {
                        if sign {
                            g_com_col = g_com_col - g_double_vec_clone[i];
                        } else {
                            g_com_col += g_double_vec_clone[i];
                        }
                    }
                });
                g_com_col
            }).collect()
        });

        g_cache = dirac::vec_addition(&g_cache, &g_cache_current);
    }

    g_cache

}

pub fn second_tier(g_cache: &Vec<G1Element>, h_vec: &Vec<G2Element>) 
-> GtElement {
    dirac::inner_product(&g_cache, &h_vec)
}


/// Convert a dense col major matrix to a sparse matrix in Zp
/// 
pub fn dense_to_sprs_cm_i64(id: &str, dense: &Vec<Vec<i64>>
) -> Mat<i64> {
    // let mut sprs = Mat::new(
    //     id,
    //     (dense.len(), dense[0].len())
    // );

    // for i in 0..dense.len() {
    //     for j in 0..dense[0].len() {
    //         if dense[i][j] != 0 {
    //             sprs.push(j, i, dense[i][j]);
    //         }
    //     }
    // }

    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    let data_vec: Vec<(usize, usize, i64)> = pool.install(|| {
        dense.par_iter().enumerate().flat_map(|(j, col)| {
            col.iter().enumerate().filter_map(|(i, val)| {
                Some((i,j, *val))
            }).collect::<Vec<(usize, usize, i64)>>()
        }).collect()
    });

    let sprs = Mat::new_from_data_vec(
        id, (dense.len(), dense[0].len()), data_vec);

    sprs
}


pub fn dense_to_sprs_cm_zp(id: &str, dense: &Vec<Vec<ZpElement>>
) -> Mat<ZpElement> {
    // let mut sprs = Mat::new(
    //     id,
    //     (dense.len(), dense[0].len())
    // );

    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    let data_vec: Vec<(usize, usize, ZpElement)> = pool.install(|| {
        dense.par_iter().enumerate().flat_map(|(j, col)| {
            col.iter().enumerate().filter_map(|(i, val)| {
                Some((i,j, *val))
            }).collect::<Vec<(usize, usize, ZpElement)>>()
        }).collect()
    });

    let sprs = Mat::new_from_data_vec(
        id, (dense.len(), dense[0].len()), data_vec);

    // for i in 0..dense.len() {
    //     for j in 0..dense[0].len() {
    //         if dense[i][j] != ZpElement::zero() {
    //             sprs.push(j, i, dense[i][j]);
    //         }
    //     }
    // }

    sprs
}

pub fn dense_i64_to_scalar(a: &Vec<Vec<i64>>)
-> Vec<Vec<ZpElement>> {


    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    let b = pool.install(|| {
        a.par_iter().map(|row| {
            row.iter().map(|a_ij| {
                ZpElement::from(*a_ij)
            }).collect::<Vec<ZpElement>>()
        }).collect::<Vec<Vec<ZpElement>>>()
    });

    b
}

pub fn dense_mat_scalar_addition_zp(a: &mut Vec<Vec<ZpElement>>, b: &Vec<Vec<ZpElement>>, z: ZpElement)
{

    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    // pool.install(|| {
    //     c.par_iter_mut().enumerate().for_each(|(i, row)| {
    //         row.iter_mut().enumerate().for_each(|(j, c_ij)| {
    //             *c_ij = *c_ij + z * b[i][j];
    //         });
    //     });
    // });

    pool.install(|| {
        a.par_iter_mut().zip(b.par_iter()).for_each(|(c_row, b_row)| {
            c_row.iter_mut().zip(b_row.iter()).for_each(|(c_ij, b_ij)| {
                *c_ij = *c_ij + z * *b_ij;
            });
        });
    });

}


#[cfg(test)]
mod tests {

    use dirac::BraKet;

    use super::*;

    use crate::setup::SRS;


    use crate::experiment_data;

    use crate::config::SQRT_MATRIX_DIM_TEST;

    #[test]
    fn test_16bit() {
        let sqrt_dim = SQRT_MATRIX_DIM_TEST;
        let log_dim = (sqrt_dim as u64).ilog2() as usize;

        let a_i64 = experiment_data::gen_mat_rand_dense_i64(sqrt_dim, 10);

        // println!("a_i64: {:?}", a_i64.len());

        let a_sparse = dense_to_sprs_cm_i64(
            &format!("a_dense_i64_2e{:?}", log_dim), &a_i64);

        let srs = SRS::new(sqrt_dim);

        println!("srs: {:?}", srs.g_hat_vec.len());

        let a_cache_cm_nopt 
        = a_sparse.bra(&srs.g_hat_vec);

        let base_double 
            = fix_base_double(&srs.g_hat_vec, 10);

        assert_eq!(base_double[8][2] * 2 as u64, base_double[9][2]);

        println!("base_double: {:?}", base_double.len());

        let a_cache = first_tier(
            &a_i64, &base_double);

        assert_eq!(a_cache[1], dirac::inner_product(
            &srs.g_hat_vec, &a_i64[1]));

        assert_eq!(a_cache, a_cache_cm_nopt);

        let a_com = second_tier(&a_cache, &srs.h_hat_vec);
        let a_com_nopt = dirac::inner_product(&a_cache_cm_nopt, &srs.h_hat_vec);
        assert_eq!(a_com, a_com_nopt);
    
    }
}