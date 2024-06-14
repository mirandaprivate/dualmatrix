//! # Main
//! 
//! Run experiments for the dualMatrix protocol.
//! 
//! The experiment parameters are configured in config.rs
//! 
//! Use the following command to run the experiment:
//! ''' cargo bench'''
//! 
//! 
#![allow(dead_code)]
use std::time::Instant;

use std::fs::OpenOptions;
use std::fs::File;
use std::io::Write;

use curv::arithmetic::Zero;
use dualmatrix::commit_mat::CommitMat;
use dualmatrix::mat::Mat;
use dualmatrix::setup::SRS;

use dualmatrix::utils::curve::ZpElement;
use dualmatrix::utils::curve::GtElement;
use dualmatrix::utils::dirac::BraKetZp;
use dualmatrix::utils::dirac;
use dualmatrix::utils::fiat_shamir::TranSeq;
use dualmatrix::utils::to_file::FileIO;
use dualmatrix::utils::opt_16bit;


use dualmatrix::zkprotocols::zk_matmul::ZkMatMul;
use dualmatrix::zkprotocols::zk_proj::{ZkProj,ZkProjProtocol};
use dualmatrix::zkprotocols::pip::Pip;

use dualmatrix::experiment_data;
use dualmatrix::config::{Q, LOG_DIM, SQRT_MATRIX_DIM};

use dualmatrix::zkprotocols::zk_trans::ZkTranSeqProver;
use rayon::iter::IntoParallelIterator;
use rayon::prelude::*;

fn main(){
    let mut log_file = OpenOptions::new()
        .create(true)
        .write(true)
        .append(true)
        .open(format!("log/log_2e{:?}", LOG_DIM)).unwrap();

    // experiment_srs_gen(&mut log_file);
    // experiment_gen_matrices(&mut log_file);
    // experiment_commit_matrices(&mut log_file);
    // experiment_matmul(&mut log_file);
    experiment(&mut log_file);
    // experiment_dense(&mut log_file);
    // experiment_proj(&mut log_file);
}


fn experiment(log_file: &mut File) {

    for t in 2..(LOG_DIM/2+1) {

        let log_dim = 2*t;
        let sqrt_dim = 2usize.pow(t as u32);
        let matrix_dim = 2usize.pow(log_dim as u32);
        let q: usize = 2usize.pow(log_dim as u32);

        println!(" ** Experiment for dualMatrix, Matrix Dim 2e{:?} times 2e{:?}; Number of non-zero elements: 2e{:?} ** ",
            log_dim,
            log_dim,
            log_dim / 2 * 3,
        );

        let srs_timer = Instant::now();

        let srs = SRS::new(q);

        let srs_duration = srs_timer.elapsed();

        println!(" ** SRS generation time: {:?}", srs_duration);
        writeln!(log_file, " ** SRS generation time: {:?}", srs_duration)
        .unwrap();

        let mat_timer = Instant::now();

        let (c, a, b) = 
            experiment_data::gen_matrices_sparse(sqrt_dim);

        let mat_duration = mat_timer.elapsed();

        println!(" ** Matrix generation time: {:?}", mat_duration);
        writeln!(log_file, " ** Matrix generation time: {:?}", mat_duration)
        .unwrap();

        // let commit_a_timer = Instant::now();

        let a_tilde = ZpElement::rand();
        let (a_com, a_cache) = 
            a.commit_cm(&srs);
        let a_blind = a_com + a_tilde * srs.blind_base;

        // let commit_a_duration = commit_a_timer.elapsed();

        // println!(" ** Commit matrix a time: {:?}", commit_a_duration);
        // writeln!(log_file, " ** Commit matrix a time: {:?}", commit_a_duration).unwrap();
        
        // let commit_b_timer = Instant::now();

        let b_tilde = ZpElement::rand();
        let (b_com, b_cache) = b.commit_cm(&srs);
        let b_blind = b_com + b_tilde * srs.blind_base;

        // let commit_b_duration = commit_b_timer.elapsed();

        // println!(" ** Commit matrix b time: {:?}", commit_b_duration);
        // writeln!(log_file, " ** Commit matrix b time: {:?}", commit_b_duration).unwrap();

        // let commit_c_timer = Instant::now();

        let c_tilde = ZpElement::rand();
        let (c_com, c_cache) = c.commit_cm(&srs);
        let c_blind = c_com + c_tilde * srs.blind_base;

        // let commit_c_duration = commit_c_timer.elapsed();

        // println!(" ** Commit matrix c time: {:?}", commit_c_duration);
        // writeln!(log_file, " ** Commit matrix c time: {:?}", commit_c_duration).unwrap();

        let commit_cab: Vec<GtElement> = [c_blind, a_blind, b_blind].to_vec();

        let timer_prove = Instant::now();
        
        let matmul_protocol = ZkMatMul::new(
            commit_cab[0],
            commit_cab[1],
            commit_cab[2], 
            matrix_dim,
            matrix_dim,
            matrix_dim,
        );
        
        let mut zk_trans = ZkTranSeqProver::new(&srs);

        matmul_protocol.prove::<i128, i64, i64>(
            &srs,
            &mut zk_trans,
            c, a, b,
            &c_cache, &a_cache, &b_cache, 
            c_tilde, a_tilde, b_tilde,
        );

        let trans = zk_trans.publish_trans();

        println!(" ** Prover time of zkMatMul: {:?}", timer_prove.elapsed());
        writeln!(log_file, " ** Prover time of zkMatMul: {:?}", 
            timer_prove.elapsed()
        ).unwrap();

        trans.save_to_file(
            format!("tr_2e{:?}", log_dim)
        ).unwrap();

        let mut trans_read = TranSeq::read_from_file(
            format!("tr_2e{:?}", log_dim)
        );

        let result = matmul_protocol.verify(&srs, &mut trans_read);

        println!(" * Verification of zkMatMul result: {:?}", result);


        let mut verify_time: f64 = 0.;
        let repeat = 100;
        
        for _ in 0..repeat {
            let mut trans_read = TranSeq::read_from_file(
                format!("tr_2e{:?}", log_dim)
            );

            let timer_verify = Instant::now();
            matmul_protocol.verify(&srs, &mut trans_read);
            verify_time += timer_verify.elapsed().as_secs_f64()/repeat as f64;
        }

        verify_time = verify_time * 1000.;

        println!(" ** Verifier time of zkMatMul : {:?}ms", verify_time);
        writeln!(log_file, " ** Verifier time of zkMatMul : {:?}ms", 
            verify_time)
        .unwrap();

    }

}

fn experiment_dense(log_file: &mut File) {

    println!(" ** Experiment for dualMatrix, Matrix Dim 2e{:?} times 2e{:?}; Number of non-zero elements: 2e{:?} ** ",
    LOG_DIM/2,
    LOG_DIM/2,
    LOG_DIM,
    );

    let srs_timer = Instant::now();

    let srs = SRS::new(2usize.pow(LOG_DIM as u32/2));

    let srs_duration = srs_timer.elapsed();

    println!(" ** SRS generation time: {:?}", srs_duration);
    writeln!(log_file, " ** SRS generation time: {:?}", srs_duration).unwrap();

    let mat_timer = Instant::now();

    let (c, a, b) = 
        experiment_data::gen_matrices_dense(SQRT_MATRIX_DIM);
    
    c.to_file(c.id.to_string(), false).unwrap();
    a.to_file(a.id.to_string(), false).unwrap();
    b.to_file(b.id.to_string(), false).unwrap();

    let mat_duration = mat_timer.elapsed();

    println!(" ** Matrix generation time: {:?}", mat_duration);
    writeln!(log_file, " ** Matrix generation time: {:?}", mat_duration).unwrap();

    // let commit_a_timer = Instant::now();

    let a_tilde = ZpElement::rand();
    let (a_com, a_cache) = 
        a.commit_cm(&srs);
    let a_blind = a_com + a_tilde * srs.blind_base;

    // let commit_a_duration = commit_a_timer.elapsed();

    // println!(" ** Commit matrix a time: {:?}", commit_a_duration);
    // writeln!(log_file, " ** Commit matrix a time: {:?}", commit_a_duration).unwrap();
    
    // let commit_b_timer = Instant::now();

    let b_tilde = ZpElement::rand();
    let (b_com, b_cache) = b.commit_cm(&srs);
    let b_blind = b_com + b_tilde * srs.blind_base;

    // let commit_b_duration = commit_b_timer.elapsed();

    // println!(" ** Commit matrix b time: {:?}", commit_b_duration);
    // writeln!(log_file, " ** Commit matrix b time: {:?}", commit_b_duration).unwrap();

    // let commit_c_timer = Instant::now();

    let c_tilde = ZpElement::rand();
    let (c_com, c_cache) = c.commit_cm(&srs);
    let c_blind = c_com + c_tilde * srs.blind_base;

    // let commit_c_duration = commit_c_timer.elapsed();

    // println!(" ** Commit matrix c time: {:?}", commit_c_duration);
    // writeln!(log_file, " ** Commit matrix c time: {:?}", commit_c_duration).unwrap();

    let commit_cab: Vec<GtElement> = [c_blind, a_blind, b_blind].to_vec();

    let timer_prove = Instant::now();
    
    let matmul_protocol = ZkMatMul::new(
        commit_cab[0],
        commit_cab[1],
        commit_cab[2], 
        SQRT_MATRIX_DIM,
        SQRT_MATRIX_DIM,
        SQRT_MATRIX_DIM,
    );
    
    let mut zk_trans = ZkTranSeqProver::new(&srs);

    matmul_protocol.prove::<i128, i64, i64>(
        &srs,
        &mut zk_trans,
        c, a, b,
        &c_cache, &a_cache, &b_cache, 
        c_tilde, a_tilde, b_tilde,
    );

    let trans = zk_trans.publish_trans();

    println!(" ** Prover time of zkMatMul: {:?}", timer_prove.elapsed());
    writeln!(log_file, " ** Prover time of zkMatMul: {:?}", 
        timer_prove.elapsed()
    ).unwrap();

    trans.save_to_file(
        format!("tr_2e{:?}", LOG_DIM/2)
    ).unwrap();

    let mut trans_read = TranSeq::read_from_file(
        format!("tr_2e{:?}", LOG_DIM/2)
    );

    let timer_verify = Instant::now();

    let mut verify_time: f64 = 0.;
    let repeat = 100;
        
    for _ in 0..repeat {
        let mut trans_read = TranSeq::read_from_file(
            format!("tr_2e{:?}", LOG_DIM/2)
        );

        let timer_verify = Instant::now();
        matmul_protocol.verify(&srs, &mut trans_read);
        verify_time += timer_verify.elapsed().as_secs_f64()/repeat as f64;
    }

    verify_time = verify_time * 1000.;

    let result = matmul_protocol.verify(&srs, &mut trans_read);

    println!(" * Verification of zkMatMul result: {:?}", result);

    println!(" ** Verifier time of zkMatMul : {:?}ms", verify_time);
    writeln!(log_file, " ** Verifier time of zkMatMul : {:?}ms", 
        timer_verify.elapsed())
    .unwrap();

}


fn experiment_proj(log_file: &mut File) {

    let log_dim = 30 as u32;
    let sqrt_dim = 2usize.pow(log_dim as u32/2);
    let count_mat = 70 * 2usize.pow(30 - log_dim as u32) as u32 * 2;
    // let count_mat = 3;
     println!(" ** Experiment for proj for {:?} 16-bit matrix,
        Matrix Dim 2e{:?} times 2e{:?}; 
        Number of non-zero elements: 2e{:?};
        Number of matrices: {:?}; Mantissa matrices: {:?}; Exponent matrices: {:?} ,
        The projections are batch verified",
    count_mat,
    log_dim/2,
    log_dim/2,
    log_dim,
    count_mat,
    count_mat/2,
    count_mat/2,
    );

    let srs_timer = Instant::now();


    let srs = SRS::new(sqrt_dim);

    let srs_duration = srs_timer.elapsed();

    println!(" ** SRS generation time: {:?}", srs_duration);
    writeln!(log_file, " ** SRS generation time: {:?}", srs_duration).unwrap();
    

    // For our mock parameters, we assume the 70 matrices are identical
    // Otherwise it will exceed our memory limit
    let a_i16 = experiment_data::gen_mat_rand_dense_i64(
        sqrt_dim, 7);

    let a = opt_16bit::dense_to_sprs_cm_i64(
        &format!("a_dense_i64_2e{:?}", log_dim), &a_i16);

    // let a = gen_matrix_dense_16bit_i64(sqrt_dim);
    

    let commit_timer = Instant::now();

    // let double_timer = Instant::now();
    let double_mat = opt_16bit::fix_base_double(
        &srs.g_hat_vec, 7);
    // let double_duration = double_timer.elapsed();

    let a_cache_cm = opt_16bit::first_tier(
        &a_i16, &double_mat);
    let a_com = opt_16bit::second_tier(
        &a_cache_cm, &srs.h_hat_vec);

    let a_tilde = ZpElement::rand();
    let a_blind = a_com + a_tilde * srs.blind_base;

    for _ in 1..count_mat{
    
        let a_cache_cm = opt_16bit::first_tier(
            &a_i16, &double_mat);
        let a_com = opt_16bit::second_tier(
            &a_cache_cm, &srs.h_hat_vec);

        let a_tilde = ZpElement::rand();
        let _ = a_com + a_tilde * srs.blind_base;
    }

    let commit_duration = commit_timer.elapsed();
    println!(" ** comitment time for {:?} matrices: {:?}",
        count_mat, commit_duration );

    let l_vec = (0..sqrt_dim).map(|_| 
        ZpElement::rand()
    ).collect::<Vec<ZpElement>>();

    let r_vec = (0..sqrt_dim).map(|_| 
        ZpElement::rand()
    ).collect::<Vec<ZpElement>>();

    let c = a.braket_zp(&l_vec, &r_vec);

    let c_com = c * srs.g_hat * srs.h_hat;

    let c_tilde = ZpElement::rand();

    let c_blind = c_com + c_tilde * srs.blind_base;
    
    // let timer_marginal = Instant::now();
    
    // simulate the complexity of bra_zp on large matrices
        
    // let _ =a.bra_zp(&l_vec);

    // count the additional cost of during the proj
    // for _ in 0..7{
    //     inner_product(&l_vec, &r_vec);
    // }

    // let verifier_marginal = Instant::now();

    // let duration_marginal = timer_marginal.elapsed().as_secs_f64();
    // let verifier_marginal = verifier_marginal.elapsed().as_secs_f64();
    // println!(" ** Prover Marginal time: {:?}ms", duration_marginal*1000.);
    // println!(" ** Verifier Marginal time: {:?}ms", verifier_marginal*1000.);

    let proj_timer = Instant::now();

    // Sum the commitment of 70 matrices
    // No need to sum the witness matrices because compute N Zp scalar mutliplications
    // is slower than compute i64 to Zp projections of N matrices
    // It is better to compute 70 projections within the proj protocol
    // and then use these projections to compute the transcript

    let y = ZpElement::rand();

     // sum commitment of 70 matrices
    let a_com_g = a_cache_cm.clone();
    let mut a_com_g_cum = a_cache_cm.clone();
    let mut y_exp = y.clone();
    for _ in 1..count_mat{
        a_com_g_cum = dirac::vec_addition_scalar_mul(
            &a_com_g_cum, 
            &a_com_g,y_exp);
        y_exp = y_exp * y;
    }

    let mut a_tilde_cum = a_tilde.clone();
    let mut y_exp = y.clone();
    for _ in 1..count_mat{
        a_tilde_cum = a_tilde_cum + a_tilde * y_exp;
        y_exp = y_exp * y;
    }

    let mut c_tilde_cum = c_tilde.clone();
    let mut y_exp = y.clone();
    for _ in 1..count_mat{
        c_tilde_cum = c_tilde_cum + c_tilde * y_exp;
        y_exp = y_exp * y;
    }

    // println!("Start convert a");

    let a_zp = opt_16bit::dense_i64_to_scalar(&a_i16);
    let mut a_cum = a_zp.clone();
    let mut y_exp = y.clone();

    // println!("Start summing up a");
    for _ in 1..count_mat{
        opt_16bit::dense_mat_scalar_addition_zp(
            &mut a_cum, &a_zp, y_exp);
        y_exp = y_exp * y;
    }

    // println!("Start convert a_cum");
    let a_cum_zp = opt_16bit::dense_to_sprs_cm_zp(
        "a_cum_zp", &a_cum);

    let verifier_time_cum_c = Instant::now();
    

    // let mut a_com_cum = a_blind.clone();
    // let mut y_exp = y.clone();
    // for _ in 1..count_mat{
    //     a_com_cum = a_com_cum + a_blind * y_exp;
    //     y_exp = y_exp * y;
    // }


    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(64)
        .build()
        .unwrap();

    let a_com_cum = pool.install(||
        (0..count_mat).into_par_iter().map(
        |i| a_blind.clone() * y.pow(i as u64)
    ).reduce(|| GtElement::zero(), |a, b| a + b)
    );

    // assert_eq!(a_com_cum, a_com_cum_new);

    // let mut c_com_cum = c_blind.clone();
    // let mut y_exp = y.clone();
    // for _ in 1..count_mat{
    //     c_com_cum = c_com_cum + c_blind * y_exp;
    //     y_exp = y_exp * y;
    // }


    let c_com_cum = 
    pool.install(||
        (0..count_mat).into_par_iter().map(
        |i| c_blind.clone() * y.pow(i as u64)
    ).reduce(|| GtElement::zero(), |a, b| a + b)
    );

    let sum_y = (y_exp - ZpElement::from(1 as u64)) 
        * (y - ZpElement::from(1 as u64)).inv();

    assert_eq!(sum_y * c_tilde, c_tilde_cum);


    let verifer_time_cum_c_duration 
        = verifier_time_cum_c.elapsed().as_secs_f64() * 1000.0;

    // // The additional time for the projections of 70 matrices
    // let mut la_cum = a.bra_zp(&l_vec);
    // let mut y_exp = y.clone();
    // for _ in 1..count_mat {
    //     let current_la =  a.bra_zp(&l_vec);
    //     la_cum = vec_addition(
    //         &la_cum, &vec_scalar_mul(&current_la, y_exp));
    //     y_exp = y_exp * y;
    // }

 

    let proj_protocol = ZkProj::new(
        c_com_cum,
        a_com_cum, 
        (sqrt_dim, sqrt_dim), 
        &l_vec, 
        &r_vec,
    );

    let mut pip = Pip::new();

    let mut zk_trans_seq = ZkTranSeqProver::new(&srs);

    let mat_vec = (&vec![a_cum_zp], ZpElement::from(1 as u64));


    proj_protocol.prove::<ZpElement>(
        &srs, 
        &mut zk_trans_seq, 
        mat_vec,
        &a_com_g_cum,
        c_tilde_cum,
        a_tilde_cum,
        &mut pip,
    );

    pip.prove(&srs, &mut zk_trans_seq);

    let proj_duration = proj_timer.elapsed();
    println!(" ** Proj Prover time: {:?}", proj_duration);
    writeln!(log_file, " ** Proj Prover time: {:?}", proj_duration).unwrap();


    let mut verify_time: f64 = 0.;
    let repeat = 100;
        
    for _ in 0..repeat {
        let timer_verify = Instant::now();
        
        let mut pip_v = Pip::new();
        let mut trans_seq = zk_trans_seq.publish_trans();
    
        let _ = proj_protocol.verify_as_subprotocol(
            &srs, &mut trans_seq, &mut pip_v
        );
    
        let _ = pip_v.verify(
            &srs, &mut trans_seq
        );
    
        verify_time += timer_verify.elapsed().as_secs_f64()/repeat as f64;
    }

    verify_time = verify_time * 1000.;
    verify_time = verify_time + verifer_time_cum_c_duration;


    println!(" ** Verifier time of proj : {:?}ms", verify_time);


    let mut pip_v = Pip::new();
    let mut trans_seq = zk_trans_seq.publish_trans();

    trans_seq.save_to_file(
        format!("tr_2e{:?}", LOG_DIM/2)
    ).unwrap();


    let result = proj_protocol.verify_as_subprotocol(
        &srs, &mut trans_seq, &mut pip_v
    );

    let result2 = pip_v.verify(
        &srs, &mut trans_seq
    );
    

    assert_eq!(result && result2, true);

    println!(" * Verification of Proj passed");
  
   
}


fn experiment_srs_gen(log_file: &mut File){
    let srs_timer = Instant::now();

    let srs = SRS::new(Q);

    let srs_duration = srs_timer.elapsed();

    println!(" ** SRS generation time: {:?}", srs_duration);
    writeln!(log_file, " ** SRS generation time: {:?}", srs_duration).unwrap();
    

    srs.to_file(
        format!("srs_2e{:?}.srs", LOG_DIM),
        true,
    ).unwrap();

}

fn experiment_gen_matrices(log_file: &mut File){
    let mat_timer = Instant::now();

    let (c, a, b) = 
        experiment_data::gen_matrices_sparse_from_kronecker(SQRT_MATRIX_DIM);

    let mat_duration = mat_timer.elapsed();

    println!(" ** Matrix generation time: {:?}", mat_duration);
    writeln!(log_file, " ** Matrix generation time: {:?}", mat_duration).unwrap();

    c.to_file(format!("{}.dat", c.id), false).unwrap();
    a.to_file(format!("{}.dat", a.id), false).unwrap();
    b.to_file(format!("{}.dat", b.id), false).unwrap();

}


fn experiment_commit_matrices(log_file: &mut File){

    let srs = SRS::from_file(format!(
        "srs_2e{:?}.srs", LOG_DIM), true
    ).unwrap();

    let timer_read = Instant::now();

    let a_read: Mat<i64> = Mat::<i64>::from_file(
        format!("a_sprs_i64_2e{:?}.dat", LOG_DIM), false
        ).unwrap();

    println!(" ** Read matrix a time: {:?}", timer_read.elapsed());
    
    let commit_a_timer = Instant::now();

    let (a_commit,_) = a_read.commit_rm(&srs);

    let commit_a_duration = commit_a_timer.elapsed();

    println!(" ** Commit matrix a time: {:?}", commit_a_duration);
    writeln!(log_file, " ** Commit matrix a time: {:?}", commit_a_duration).unwrap();

    let b_read: Mat<i64> = Mat::<i64>::from_file(
        format!("b_sprs_i64_2e{:?}.dat", LOG_DIM), false
        ).unwrap();
    
    let commit_b_timer = Instant::now();

    let (b_commit,_) = b_read.commit_cm(&srs);

    let commit_b_duration = commit_b_timer.elapsed();

    println!(" ** Commit matrix b time: {:?}", commit_b_duration);
    writeln!(log_file, " ** Commit matrix b time: {:?}", commit_b_duration).unwrap();

    let c_read: Mat<i128> = Mat::<i128>::from_file(
        format!("c_sprs_i128_2e{:?}.dat", LOG_DIM), false
        ).unwrap();
    
    let commit_c_timer = Instant::now();

    let (c_commit,_) = c_read.commit_cm(&srs);

    let commit_c_duration = commit_c_timer.elapsed();

    println!(" ** Commit matrix c time: {:?}", commit_c_duration);
    writeln!(log_file, " ** Commit matrix c time: {:?}", commit_c_duration).unwrap();

    let commit_cab = [c_commit, a_commit, b_commit].to_vec();

    commit_cab.to_file(
        format!("commit_cab_sprs_2e{:?}.com", LOG_DIM), 
        true).unwrap()


}

