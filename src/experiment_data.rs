//! Matrices for experiments.
//! 
//! We pack sqrt(n) random dense matrices of size sqrt(n) * sqrt(n) to generate
//! a n * n sparse matrix with n^{1.5} non-zero elements (52bits for each element).
//! 
//! The multiplication of two such sparse matrices will generate a sparse matrix
//! with n^{1.5} non-zero elements (each element be a i128 number).
//! 
//! We constrain the number to be 52 bits because this is the length of 
//! the mantissa for double-precision floating-point numbers
//! according to the IEEE 754 standard.
//! 

#![allow(dead_code)]
use std::time::Instant;

use curv::arithmetic::Zero;
use rand::Rng;

use rayon::prelude::*;
use rayon::ThreadPoolBuilder;

use crate::mat::Mat;

use crate::utils::curve::ZpElement;

use crate::config::NUM_THREADS;


/// Generate a random dense i64 matrix
/// 
pub fn gen_mat_rand_dense_i64(dim: usize, max_bit: u32) -> Vec<Vec<i64>>{
    (0..dim).map(|_| {
        (0..dim).map(|_| {
            rand::thread_rng()
            .gen_range(-2i64.pow(max_bit)+1..2i64.pow(max_bit)) as i64
        }).collect::<Vec<i64>>()  
    }).collect::<Vec<Vec<i64>>>()
}

/// Generate a random diagonal i64 matrix
/// 
pub fn gen_mat_rand_diag_i64(dim: usize, max_bit: u32) -> Vec<i64>{
    (0..dim).map(|_| {
        rand::thread_rng()
        .gen_range(-2i64.pow(max_bit)..2i64.pow(max_bit)) as i64
    }).collect::<Vec<i64>>()  
}

/// Pack n n*n dense matrix to a (n^2) * (n^2) sparse matrix (each element is i64)
pub fn pack_dense_to_sprs_i64(
    dense_vec: &Vec<Vec<Vec<i64>>>
) -> Vec<(usize, usize, i64)> {

    let sqrt_n = dense_vec.len();
    let mut sprs = Vec::new();

    for i in 0..sqrt_n {
        for k in 0..sqrt_n {
            for j in 0..sqrt_n {
                sprs.push((i*sqrt_n + k, j * sqrt_n +k, dense_vec[k][i][j]));
            }
        }
    }

    sprs
}

/// Pack n n*n dense matrix to a (n^2) * (n^2) sparse matrix (each element is i128)
pub fn pack_dense_to_sprs_i128(
    dense_vec: &Vec<Vec<Vec<i128>>>
) -> Vec<(usize, usize, i128)> {

    let sqrt_n = dense_vec.len();
    let mut sprs = Vec::new();

    for i in 0..sqrt_n {
        for k in 0..sqrt_n {
            for j in 0..sqrt_n {
                sprs.push((i*sqrt_n + k, j * sqrt_n +k, dense_vec[k][i][j]));
            }
        }
    }

    sprs
}


/// Compute the multiplication of two i64 sparse matrices packed by the dense matrices
pub fn mat_mul_pack_i64_to_i128(
    a_mat_vec: &Vec<Vec<Vec<i64>>>,
    b_mat_vec: &Vec<Vec<Vec<i64>>>,
) -> Vec<Vec<Vec<i128>>> {
    let sqrt_n = a_mat_vec.len();
    let mut result = Vec::new();

    let pool = ThreadPoolBuilder::new()
    .num_threads(NUM_THREADS)
    .build()
    .unwrap();

    let timer = Instant::now();

    for l in 0..sqrt_n {
        let mut result_l = 
            vec![vec![0 as i128; sqrt_n]; sqrt_n];

        pool.install(|| {
            result_l.par_iter_mut().enumerate().for_each(
                |(i, row)| {
                for j in 0..sqrt_n {
                    for k in 0..sqrt_n {
                        row[j] += a_mat_vec[l][i][k] as i128 * b_mat_vec[l][k][j] as i128;
                    }
                }
                }
            );
        });

        result.push(result_l);
    }

    println!(" *** Compute sparse matrix mulitplication time: {:?}", timer.elapsed());
    
    result
}

/// Generate the sparse matrices used for experiments
pub fn gen_matrices_sparse(sqrt_dim: usize) 
-> (Mat<i128>, Mat<i64>, Mat<i64>) {

    let dim = sqrt_dim * sqrt_dim;
    let log_dim = (dim as u64).ilog2() as usize;

    let a_mat_vec = (0..sqrt_dim).map(|_| {
        gen_mat_rand_dense_i64(sqrt_dim, 52)
    }).collect::<Vec<Vec<Vec<i64>>>>();

    let b_mat_vec = (0..sqrt_dim).map(|_| {
        gen_mat_rand_dense_i64(sqrt_dim, 52)
    }).collect::<Vec<Vec<Vec<i64>>>>();

    let c_mat_vec = mat_mul_pack_i64_to_i128(
        &a_mat_vec, &b_mat_vec
    );

    let a = Mat::new_from_data_vec(
        &format!("a_sprs_i64_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        pack_dense_to_sprs_i64(&a_mat_vec)
    );

    let b = Mat::new_from_data_vec(
        &format!("b_sprs_i64_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        pack_dense_to_sprs_i64(&b_mat_vec)
    );

    let c = Mat::new_from_data_vec(
        &format!("c_sprs_i128_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        pack_dense_to_sprs_i128(&c_mat_vec)
    );

    (c, a, b)

}

/// Compute the multiplication of two i64 dense matrices
/// 
fn mat_mul_dense_i64_to_zp(a: &Vec<Vec<i64>>, b: &Vec<Vec<i64>>) 
    -> Vec<Vec<ZpElement>> {
    let a_rows = a.len();
    let a_cols = a[0].len();
    let b_cols = b[0].len();

    let mut result = 
        vec![vec![ZpElement::zero(); b_cols]; a_rows];

    let pool = ThreadPoolBuilder::new()
        .num_threads(NUM_THREADS)
        .build()
        .unwrap();

    pool.install(|| {
        result.par_iter_mut().enumerate().for_each(
            |(i, row)| {
            for j in 0..b_cols {
                for k in 0..a_cols {
                    row[j] += ZpElement::from(a[i][k]) * ZpElement::from(b[k][j]);
                }
            }
            }
        );
    });

    result
}

/// Compute the multiplication of two i64 dense matrices
/// 
fn mat_mul_dense_i64_to_i64(a: &Vec<Vec<i64>>, b: &Vec<Vec<i64>>
) -> Vec<Vec<i64>> {
    let a_rows = a.len();
    let a_cols = a[0].len();
    let b_cols = b[0].len();

    let mut result = 
        vec![vec![0 as i64; b_cols]; a_rows];

    let pool = ThreadPoolBuilder::new()
        .num_threads(NUM_THREADS)
        .build()
        .unwrap();

    pool.install(|| {
        result.par_iter_mut().enumerate().for_each(
            |(i, row)| {
            for j in 0..b_cols {
                for k in 0..a_cols {
                    row[j] += a[i][k] * b[k][j];
                }
            }
        });
    });

    result
}


/// Compute the multiplication of two i64 dense matrices
/// 
/// The result is a i128 dense matrix
/// 
pub fn mat_mul_dense_i64_to_i128(a: &Vec<Vec<i64>>, b: &Vec<Vec<i64>>
) -> Vec<Vec<i128>> {
    let a_rows = a.len();
    let a_cols = a[0].len();
    let b_cols = b[0].len();

    let mut result = 
        vec![vec![0 as i128; b_cols]; a_rows];

    let pool = ThreadPoolBuilder::new()
        .num_threads(NUM_THREADS)
        .build()
        .unwrap();

    let timer = Instant::now();

    pool.install(|| {
        result.par_iter_mut().enumerate().for_each(
            |(i, row)| {
            for j in 0..b_cols {
                for k in 0..a_cols {
                    row[j] += (a[i][k] as i128) * (b[k][j] as i128);
                }
            }
        });
    });

    println!(" *** Compute dense matrix mulitplication time: {:?}", timer.elapsed());

    result
}

/// Compute the multiplication of two Zp dense matrices
/// 
fn mat_mul_dense_zp_to_zp(a: &Vec<Vec<ZpElement>>, b: &Vec<Vec<ZpElement>>
) -> Vec<Vec<ZpElement>> {
    let a_rows = a.len();
    let a_cols = a[0].len();
    let b_cols = b[0].len();

    let mut result = 
        vec![vec![ZpElement::zero(); b_cols]; a_rows];

    for i in 0..a_rows {
        for j in 0..b_cols {
            for k in 0..a_cols {
                result[i][j] += 
                    a[i][k] * b[k][j];
            }
        }
    }

    result
}

/// Compute the multiplication of two diagonal matrices
/// 
fn mat_mul_diag_i64_to_zp(a: &Vec<i64>, b: &Vec<i64>) -> Vec<ZpElement> {
    
    a.iter().zip(b.iter()).map(|(left, right)| {
        ZpElement::from(*left) *  ZpElement::from(*right)
    }).collect()
}

/// Compute the multiplication of two diagonal matrices
/// 
fn mat_mul_diag_i64_to_i64(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
    
    a.iter().zip(b.iter()).map(|(left, right)| {
        left * right
    }).collect()
}

/// Compute the kronecker product between a diagonal matrix and a dense matrix
/// 
pub fn diag_kronecker_dense_from_i64_to_zp(a: &Vec<i64>, b: &Vec<Vec<i64>>
) -> Vec<(usize, usize, ZpElement)> {
    
    let sqrt_dim = a.len();

    let pool = ThreadPoolBuilder::new()
        .num_threads(8)
        .build()
        .unwrap();

    pool.install(|| {
        (0..sqrt_dim).into_par_iter().flat_map(|left_ij|{
            (0..sqrt_dim).flat_map( |right_i|{
                (0..sqrt_dim).map( move |right_j|{
                    (
                        left_ij * sqrt_dim + right_i,
                        left_ij * sqrt_dim + right_j,
                        ZpElement::from(a[left_ij]) * ZpElement::from(
                            b[right_i][right_j]
                        ) 
                    )
                })
            }).collect::<Vec<(usize, usize, ZpElement)>>()
        }).collect::<Vec<(usize, usize, ZpElement)>>()
    })
    
}


/// Compute the kronecker product between a diagonal matrix and a dense matrix
/// 
pub fn diag_kronecker_dense_from_i64_to_i64(a: &Vec<i64>, b: &Vec<Vec<i64>>
) -> Vec<(usize, usize, i64)> {
    
    let sqrt_dim = a.len();

    let pool = ThreadPoolBuilder::new()
        .num_threads(8)
        .build()
        .unwrap();

    pool.install(|| {
        (0..sqrt_dim).into_par_iter().flat_map(|left_ij|{
            (0..sqrt_dim).flat_map( |right_i|{
                (0..sqrt_dim).map( move |right_j|{
                    (
                        left_ij * sqrt_dim + right_i,
                        left_ij * sqrt_dim + right_j,
                        a[left_ij] * b[right_i][right_j] 
                    )
                })
            }).collect::<Vec<(usize, usize, i64)>>()
        }).collect::<Vec<(usize, usize, i64)>>()
    })
}

/// Compute the kronecker product between a diagonal matrix and a dense matrix
/// 
pub fn diag_kronecker_dense_from_i64_to_i128(a: &Vec<i64>, b: &Vec<Vec<i64>>
) -> Vec<(usize, usize, i128)> {
    
    let sqrt_dim = a.len();

    let pool = ThreadPoolBuilder::new()
        .num_threads(8)
        .build()
        .unwrap();

    pool.install(|| {
        (0..sqrt_dim).into_par_iter().flat_map(|left_ij|{
            (0..sqrt_dim).flat_map( |right_i|{
                (0..sqrt_dim).map( move |right_j|{
                    (
                        left_ij * sqrt_dim + right_i,
                        left_ij * sqrt_dim + right_j,
                        (a[left_ij] as i128) * (
                            b[right_i][right_j] as i128
                        ) 
                    )
                })
            }).collect::<Vec<(usize, usize, i128)>>()
        }).collect::<Vec<(usize, usize, i128)>>()
    })
}



/// Generate the sparse matrices from kronecker product of a diagonal matrix 
/// and a dense matrix (each of size sqrt_dim * sqrt_dim)
/// 
/// The dimension of the resulting matrix is:
///     (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim)
/// 
/// The elements of the matrices are i128, i64, i64 respectively.
/// 
pub fn gen_matrices_sparse_from_kronecker(sqrt_dim: usize) 
    -> (Mat<i128>, Mat<i64>, Mat<i64>) {
    
    let dim = sqrt_dim * sqrt_dim;
    let log_dim = (dim as u64).ilog2() as usize;


    let a_left = gen_mat_rand_diag_i64(
        sqrt_dim,26
    );
    let a_right = gen_mat_rand_dense_i64(
        sqrt_dim, 26
    );

    let b_left = gen_mat_rand_diag_i64(
        sqrt_dim, 26
    );
    let b_right = gen_mat_rand_dense_i64(
        sqrt_dim, 26
    );

    let c_left = mat_mul_diag_i64_to_i64(
        &a_left, &b_left
    );
    let c_right = mat_mul_dense_i64_to_i64(
        &a_right, &b_right
    );

    let a = Mat::new_from_data_vec(
        &format!("a_sprs_i64_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        diag_kronecker_dense_from_i64_to_i64(&a_left, &a_right)
    );

    let b = Mat::new_from_data_vec(
        &format!("b_sprs_i64_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        diag_kronecker_dense_from_i64_to_i64(&b_left, &b_right)
    );

    let c = Mat::new_from_data_vec(
        &format!("c_sprs_i128_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        diag_kronecker_dense_from_i64_to_i128(&c_left, &c_right)
    );

    (c, a, b)
}

/// Convert the i128 sparse matrix to Zp sparse matrix
/// 
pub fn sprs_i128_to_zp(sprs: &Mat<i128>) -> Mat<ZpElement> {
   
    let data_zp = sprs.data
        .iter()
        .map(|&(row, col, val)|{
            (row, col, ZpElement::from(val))
        }).collect::<Vec<(usize, usize, ZpElement)>>();
    
    Mat::new_from_data_vec(
        &format!("{}_zp", sprs.id),
        sprs.shape,
        data_zp,
    )
}

/// Convert the i64 sparse matrix to Zp sparse matrix
/// 
pub fn sprs_i64_to_zp(sprs: &Mat<i64>) -> Mat<ZpElement> {
   
    let data_zp = sprs.data.iter()
        .map(|&(row, col, val)|{
            (row, col, ZpElement::from(val))
       }).collect::<Vec<(usize, usize, ZpElement)>>();
    
    Mat::new_from_data_vec(
        &format!("{}_zp", sprs.id),
        sprs.shape,
        data_zp,
    )
}

/// Generate the sparse matrices in Zp.
/// 
/// 
#[cfg(test)]
pub fn gen_matrices_sparse_zp_from_kronecker(sqrt_dim: usize
) -> (Mat<ZpElement>, Mat<ZpElement>, Mat<ZpElement>) {
    
    let dim = sqrt_dim * sqrt_dim;
    let log_dim = (dim as u64).ilog2() as usize;


    let a_left = gen_mat_rand_diag_i64(sqrt_dim,26);
    let a_right = gen_mat_rand_dense_i64(sqrt_dim, 26);

    let b_left = gen_mat_rand_diag_i64(sqrt_dim, 26);
    let b_right = gen_mat_rand_dense_i64(sqrt_dim, 26);

    let c_left = mat_mul_diag_i64_to_i64(&a_left, &b_left);
    let c_right = mat_mul_dense_i64_to_i64(&a_right, &b_right);

    let a = Mat::new_from_data_vec(
        &format!("a_sprs_zp_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        diag_kronecker_dense_from_i64_to_zp(&a_left, &a_right)
    );

    let b = Mat::new_from_data_vec(
        &format!("b_sprs_zp_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        diag_kronecker_dense_from_i64_to_zp(&b_left, &b_right)
    );

    let c = Mat::new_from_data_vec(
        &format!("c_sprs_zp_2e{:?}", log_dim),
        (sqrt_dim * sqrt_dim, sqrt_dim * sqrt_dim), 
        diag_kronecker_dense_from_i64_to_zp(&c_left, &c_right)
    );

    (c, a, b)
}

/// Convert a sparse matrix to a dense matrix in Zp
/// 
fn sprs_to_dense_zp(sprs: &Mat<ZpElement>) -> Vec<Vec<ZpElement>> {
    let mut dense = 
        vec![vec![ZpElement::zero(); sprs.shape.1]; sprs.shape.0];

    for &(row, col, ref val) in &sprs.data {
        dense[row][col] = *val;
    }

    dense
}

/// Convert a sparse matrix to a dense matrix in Zp
/// 
fn sprs_to_dense_from_i64_to_zp(sprs: &Mat<i64>) -> Vec<Vec<ZpElement>> {
    let mut dense = 
        vec![vec![ZpElement::zero(); sprs.shape.1]; sprs.shape.0];

    for &(row, col, ref val) in &sprs.data {
        dense[row][col] = ZpElement::from(*val);
    }

    dense
}

/// Convert a sparse matrix to a dense matrix in Zp
/// 
fn sprs_to_dense_from_i128_to_zp(sprs: &Mat<i128>) -> Vec<Vec<ZpElement>> {
    let mut dense = 
        vec![vec![ZpElement::zero(); sprs.shape.1]; sprs.shape.0];

    for &(row, col, ref val) in &sprs.data {
        dense[row][col] = ZpElement::from(*val);
    }

    dense
}

/// Convert a dense matrix to a sparse matrix in Zp
/// 
fn dense_to_sprs_zp(id: &str, dense: &Vec<Vec<ZpElement>>
) -> Mat<ZpElement> {
    let mut sprs = Mat::new(
        id,
        (dense.len(), dense[0].len())
    );

    for i in 0..dense.len() {
        for j in 0..dense[0].len() {
            if dense[i][j] != ZpElement::zero() {
                sprs.push(i, j, dense[i][j]);
            }
        }
    }

    sprs
}

/// Convert a dense matrix to a sparse matrix in Zp
/// 
pub fn dense_to_sprs_from_i64_to_zp(id: &str, dense: &Vec<Vec<i64>>
) -> Mat<ZpElement> {
    let mut sprs = Mat::new(
        id,
        (dense.len(), dense[0].len())
    );

    for i in 0..dense.len() {
        for j in 0..dense[0].len() {
            if dense[i][j] != 0 {
                sprs.push(i, j, ZpElement::from(dense[i][j]));
            }
        }
    }

    sprs
}

/// Convert a dense matrix to a sparse matrix in i64
/// 
pub fn dense_to_sprs_from_i64_to_i64(id: &str, dense: &Vec<Vec<i64>>
) -> Mat<i64> {
    let mut sprs = Mat::new(
        id,
        (dense.len(), dense[0].len())
    );

    for i in 0..dense.len() {
        for j in 0..dense[0].len() {
            if dense[i][j] != 0 {
                sprs.push(i, j, dense[i][j]);
            }
        }
    }

    sprs
}

/// Convert a dense matrix to a sparse matrix in i128
/// 
fn dense_to_sprs_from_i128_to_i128(id: &str, dense: &Vec<Vec<i128>>
) -> Mat<i128> {
    let mut sprs = Mat::new(
        id,
        (dense.len(), dense[0].len())
    );

    for i in 0..dense.len() {
        for j in 0..dense[0].len() {
            if dense[i][j] != 0 {
                sprs.push(i, j, dense[i][j] as i128);
            }
        }
    }

    sprs
}

/// Generate the random dense matrices for experiments.
/// 
/// The elements of the matrices are i128, i64, i64 respectively.
/// 
pub fn gen_matrices_dense(dim: usize
) -> (Mat<i128>, Mat<i64>, Mat<i64>) {
    
    let log_dim = (dim as u64).ilog2() as usize;

    let a_u64 = gen_mat_rand_dense_i64(dim, 52);

    let b_u64 = gen_mat_rand_dense_i64(dim, 52);

    let c_zp = mat_mul_dense_i64_to_i128(&a_u64, &b_u64);

    let a = dense_to_sprs_from_i64_to_i64(
        &format!("a_dense_i64_2e{:?}", log_dim), &a_u64);

    let b = dense_to_sprs_from_i64_to_i64(
        &format!("b_dense_i64_2e{:?}", log_dim), &b_u64);

    let c = dense_to_sprs_from_i128_to_i128(
        &format!("c_dense_i128_2e{:?}", log_dim), &c_zp);


    (c, a, b)
}

pub fn gen_matrix_dense_16bit_i64(dim: usize) -> Mat<i64> {
    let log_dim = (dim as u64).ilog2() as usize;
    let a_i64 = gen_mat_rand_dense_i64(dim, 16);

  
    let sparse = dense_to_sprs_from_i64_to_i64(
        &format!("a_dense_i64_2e{:?}", log_dim), &a_i64);
    
    sparse
}

pub fn gen_matrix_dense_1_zp(dim: usize) -> Mat<ZpElement> {
    let log_dim = (dim as u64).ilog2() as usize;
    let a_i64 = gen_mat_rand_dense_i64(dim, 16);

  
    let sparse = dense_to_sprs_from_i64_to_zp(
        &format!("a_dense_i64_2e{:?}", log_dim), &a_i64);
    
    sparse
}


pub fn gen_vec_1(dim: usize) -> Vec<ZpElement> {
    std::iter::successors(
        Some(ZpElement::from(1 as u64)), 
        |&x| Some(x)
    ).take(dim).collect::<Vec<ZpElement>>()
}

#[cfg(test)]
mod tests{

    use super::*;

    use crate::utils::to_file::FileIO;
    use crate::config::SQRT_MATRIX_DIM_TEST;


    #[test]
    fn test_experiment_data(){
        let (_c, _a, _b) = 
            gen_matrices_sparse_zp_from_kronecker(SQRT_MATRIX_DIM_TEST);

        let (_c_d, _a_d, _b_d) = 
            gen_matrices_dense(SQRT_MATRIX_DIM_TEST);

        let a_d_dense = sprs_to_dense_from_i64_to_zp(
            &_a_d
        );
        let b_d_dense = sprs_to_dense_from_i64_to_zp(
            &_b_d
        );
        let c_d_dense = sprs_to_dense_from_i128_to_zp(
            &_c_d
        );

        assert_eq!(mat_mul_dense_zp_to_zp(&a_d_dense, &b_d_dense), c_d_dense);


        let (_c, _a, _b) = 
            gen_matrices_sparse(SQRT_MATRIX_DIM_TEST);


        let a_d_dense = sprs_to_dense_from_i64_to_zp(
            &_a_d
        );
        let b_d_dense = sprs_to_dense_from_i64_to_zp(
            &_b_d
        );
        let c_d_dense = sprs_to_dense_from_i128_to_zp(
            &_c_d
        );

        assert_eq!(mat_mul_dense_zp_to_zp(&a_d_dense, &b_d_dense), c_d_dense);

        let log_dim = (SQRT_MATRIX_DIM_TEST as u64).ilog2() as usize;

        _a_d.to_file(format!("{}.dat", _a_d.id), false)
            .unwrap();
        _b_d.to_file(format!("{}.dat", _b_d.id), false)
            .unwrap();
        _c_d.to_file(format!("{}.dat", _c_d.id), false)
            .unwrap();

        let a_read: Mat<i64> = Mat::<i64>::from_file(
            format!("a_dense_i64_2e{:?}.dat", log_dim), false
            ).unwrap();
        let b_read = Mat::<i64>::from_file(
            format!("b_dense_i64_2e{:?}.dat", log_dim), false
            ).unwrap();
        let c_read = Mat::<i128>::from_file(
            format!("c_dense_i128_2e{:?}.dat", log_dim), false
            ).unwrap();
        
        let a_read_dense = sprs_to_dense_from_i64_to_zp(
            &a_read);
        let b_read_dense = sprs_to_dense_from_i64_to_zp(
            &b_read);
        let c_read_dense = sprs_to_dense_from_i128_to_zp(
            &c_read);

        assert_eq!(
            mat_mul_dense_zp_to_zp(&a_read_dense, &b_read_dense), c_read_dense
        );
    
        // let a_dense = sprs_to_dense_zp(&_a);
        // let b_dense = sprs_to_dense_zp(&_b);
        // let c_dense = sprs_to_dense_zp(&_c);

        // assert_eq!(mat_mul_dense_zp_to_zp(&a_dense, &b_dense), c_dense);
    }
}