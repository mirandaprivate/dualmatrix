//! This file contains all the parameters used in the experiment. 
//!
pub const NUM_THREADS: usize = 64;

pub const LOG_DIM: usize = 20;

pub const Q: usize = 2usize.pow(LOG_DIM as u32);

pub const SQRT_MATRIX_DIM: usize = 2usize.pow(LOG_DIM as u32/2);
pub const MATRIX_DIM: usize = SQRT_MATRIX_DIM * SQRT_MATRIX_DIM;

pub const DATA_DIR_PUBLIC: &str = "data/public/";
pub const DATA_DIR_PRIVATE: &str = "data/private/";

/// The following parameters are used for testing

pub const LOG_DIM_TEST: usize = 6;
pub const Q_TEST: usize = 2usize.pow(LOG_DIM_TEST as u32);

pub const SQRT_MATRIX_DIM_TEST: usize = 2usize.pow(3);
pub const MATRIX_DIM_TEST: usize = SQRT_MATRIX_DIM_TEST * SQRT_MATRIX_DIM_TEST;
