//! Define the struct of the witness matrices.
//! 
//! The witness matrices are represented as sparse matrices.
//!  

use core::convert::From;
use std::sync::Arc;

use rayon::{ThreadPoolBuilder, prelude::*};
use serde::{Serialize, Deserialize};

use crate::utils::to_file::FileIO;

use crate::utils::curve::{
    Zero, ZpElement, ConvertToZp,
};

use crate::config::NUM_THREADS;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Mat<T> 
{
    pub id: String,
    pub shape: (usize, usize),
    pub data: Vec<(usize, usize, T)>,
}


impl<T> Mat<T> {
    pub fn new(
        id: &str, 
        shape: (usize, usize)) -> Self {
        let id = String::from(id);
        let data: Vec<(usize, usize, T)> = Vec::new();
        Self {id, shape, data}
    }

    pub fn new_from_data_vec(
        id: &str, 
        shape: (usize, usize),
        data: Vec<(usize, usize, T)>) -> Self {
        let id = String::from(id);
        Self {id, shape, data}
    }


    pub fn push(&mut self, row: usize, col: usize, val: T) {
        self.data.push((row, col, val));
    }    
}

pub trait ToZpMat {
    fn to_zp_mat(&self) -> Mat<ZpElement>;
}

impl<T: ConvertToZp> ToZpMat for Mat<T> {
    fn to_zp_mat(&self) -> Mat<ZpElement> {
        let pool = ThreadPoolBuilder::new()
        .num_threads(NUM_THREADS)
        .build()
        .unwrap();

        let shape = self.shape;
        let id = self.id.clone() + "zp";
        let data_len = self.data.len();

        // Initialize a vector for the converted data
        let mut converted_data = 
            vec![(0, 0, ZpElement::zero()); data_len];
        let arc_data = Arc::new(self.data.clone());

        pool.install(|| {
            converted_data.par_iter_mut().enumerate().for_each(
                |(idx, elem)| {
                let (i, j, val) = &arc_data[idx];
                *elem = (*i, *j, val.to_zp());
            });
        });

        let mut mat = Mat::new(&id, shape);
        mat.data = converted_data;
        
        mat
    }
}

impl<T: Serialize + for<'de> Deserialize<'de> > FileIO for Mat<T> {}

impl<T: PartialEq + Clone> PartialEq for Mat<T> {

    fn eq(&self, other: &Self) -> bool {
        if self.shape != other.shape {
            return false;
        }

        let mut self_data = self.data.clone();
        let mut other_data = other.data.clone();

        self_data.sort_by(
            |a, b| 
            a.0.cmp(&b.0)
        );
        self_data.sort_by(
            |a, b|
            a.1.cmp(&b.1)
        );

        other_data.sort_by(
            |a, b|
            a.0.cmp(&b.0)
        );
        other_data.sort_by(
            |a, b|
            a.1.cmp(&b.1)
        );

        self_data == other_data
    }
}

impl<T: PartialEq + Clone> Eq for Mat<T> {}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;
    use crate::utils::curve::GtElement;

    #[test]
    fn test_mat() {
        let mut mat_1:Mat<GtElement>  = Mat::new("test_mat", (2, 2));
        assert_eq!(mat_1.id, "test_mat");
        assert_eq!(mat_1.shape, (2, 2));

        mat_1.push(1, 1, GtElement::from(3 as i64));
        mat_1.push(1, 2, GtElement::from(1 as i64));

        assert_eq!(mat_1.data[1], (1, 2, GtElement::from(1 as i64)));

        let mut mat_2:Mat<GtElement>  = Mat::new(
            "test_mat_2", (2, 2)
        );
        mat_2.push(1, 2, GtElement::from(1 as i64));
        mat_2.push(1, 1, GtElement::from(3 as i64));
        
        assert_eq!(mat_1, mat_2);

        mat_1.to_file("mat_test.dat".to_string(), true)
        .unwrap();
        let mat_1_read: Mat<GtElement> = Mat::from_file(
                "mat_test.dat".to_string(), true
            ).unwrap();
        assert_eq!(mat_1, mat_1_read);

        let vec_1: Vec<GtElement> = 
            vec![GtElement::from(1 as i64), GtElement::from(2 as i64)];
        vec_1.to_file(
            "vec_test.dat".to_string(), false
        ).unwrap();
        let vec_1_read: Vec<GtElement> = Vec::from_file(
             "vec_test.dat".to_string(), false
        ).unwrap();
        assert_eq!(vec_1, vec_1_read);
    }
}