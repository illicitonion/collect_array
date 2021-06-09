//! Allows for collecting an Iterator into an exactly sized array.
//!
//! # Example
//!
//! ```
//! use collect_array::CollectArrayResult;
//!
//! let v = vec![0, 1, 2];
//! let result: CollectArrayResult<_, 3> = v.into_iter().collect();
//! assert_eq!(CollectArrayResult::Ok([0, 1, 2]), result);
//! ```

#![cfg_attr(not(test), no_std)]

use core::{
    mem::{self, forget, MaybeUninit},
    ptr,
};

/// The result of collecting an Iterator into an exactly-sized array, or having failed to.
///
/// More than N elements may be consumed from the Iterator - if this is undesirable, consider
/// calling [`Iterator#take`] before collecting.
pub enum CollectArrayResult<T, const N: usize> {
    /// Returned if the Iterator contained exactly N elements.
    Ok([T; N]),
    /// Returned if the Iterator contained more than N elements.
    /// The underlying Iterator may not be exhausted, and remaining values may not be accessible.
    TooManyElements {
        /// The N values which were read.
        values: [T; N],
        /// The next value after the Nth.
        next_value: T,
    },
    /// Returned if the Iterator contained fewer than N elements.
    ///
    /// # Safety
    ///
    /// Only the first `init_count` elements will be init, the remaining elements must not be read.
    NotEnoughElements {
        /// The consumed values, only `init_count` of which will be init.
        values: [MaybeUninit<T>; N],
        /// How many elements in `values` are init.
        init_count: usize,
    },
}

impl<T, const N: usize> CollectArrayResult<T, N> {
    /// Returns the contained [`Ok`](Self::Ok) value, consuming the self value.
    pub fn unwrap(mut self) -> [T; N] {
        let a = match &mut self {
            Self::Ok(a) => unsafe { ptr::read(a) },
            Self::TooManyElements { .. } => {
                panic!("called `CollectArrayResult::unwrap` with too many elements")
            }
            Self::NotEnoughElements { .. } => {
                panic!("called `CollectArrayResult::unwrap` without enough elements")
            }
        };

        mem::forget(self);

        a
    }
}

impl<T, const N: usize> PartialEq<CollectArrayResult<T, N>> for CollectArrayResult<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &CollectArrayResult<T, N>) -> bool {
        match (self, other) {
            (Self::Ok(lhs), Self::Ok(rhs)) => lhs == rhs,
            (Self::TooManyElements { .. }, Self::TooManyElements { .. }) => false,
            (
                Self::NotEnoughElements {
                    values: lhs,
                    init_count: lhs_count,
                },
                Self::NotEnoughElements {
                    values: rhs,
                    init_count: rhs_count,
                },
            ) if lhs_count == rhs_count => {
                for i in 0..*lhs_count {
                    if let Some(lhs) = lhs.get(i) {
                        if let Some(rhs) = rhs.get(i) {
                            unsafe {
                                if *lhs.as_ptr() != *rhs.as_ptr() {
                                    return false;
                                }
                            }
                        }
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl<T, const N: usize> core::fmt::Debug for CollectArrayResult<T, N>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Ok(arr) => arr.fmt(f),
            Self::TooManyElements { values, next_value: next } => write!(
                f,
                "CollectArrayResult::TooManyElements{{ values: {:?}, next: {:?} (possibly others...) }}",
                values, next,
            ),
            Self::NotEnoughElements { values, init_count } => {
                write!(
                    f,
                    "CollectArrayResult::NotEnoughElements{{ got: {:?}, expected: {:?}, values: [",
                    init_count, N
                )?;
                let mut i = 0;
                while i < *init_count {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", unsafe { &*values.get(i).unwrap().as_ptr() })?;
                    i += 1;
                }
                write!(f, "] }}")?;
                Ok(())
            }
        }
    }
}

impl<T, const N: usize> core::iter::FromIterator<T> for CollectArrayResult<T, N> {
    fn from_iter<It: IntoIterator<Item = T>>(it: It) -> Self {
        struct PanicDropper<'a, T> {
            init: &'a mut [MaybeUninit<T>],
        }

        impl<'a, T> Drop for PanicDropper<'a, T> {
            fn drop(&mut self) {
                let init_slice = ptr::slice_from_raw_parts_mut(
                    self.init.as_mut_ptr() as *mut T,
                    self.init.len(),
                );
                unsafe { ptr::drop_in_place(init_slice) }
            }
        }

        // TODO: Use MaybeUninit::uninit_array or [MaybeUninit::<T>::uninit(); N] when either stabilises.
        let mut values: [MaybeUninit<T>; N] =
            unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() };

        let mut added = 0_usize;

        let mut iter = it.into_iter();

        while added < N {
            let (init, uninit) = values.split_at_mut(added);

            let panic_dropper = PanicDropper { init };
            let next = iter.next();
            forget(panic_dropper);

            if let Some(value) = next {
                uninit[0] = MaybeUninit::new(value);
                added += 1;
            } else {
                break;
            }
        }

        if added == N {
            // TODO: Use MaybeUninit::array_assume_init when it stabilises (https://github.com/rust-lang/rust/issues/80908).
            let values = unsafe { (&values as *const _ as *const [T; N]).read() };
            if let Some(next_value) = iter.next() {
                CollectArrayResult::TooManyElements { values, next_value }
            } else {
                CollectArrayResult::Ok(values)
            }
        } else {
            CollectArrayResult::NotEnoughElements {
                values,
                init_count: added,
            }
        }
    }
}

impl<T, const N: usize> Drop for CollectArrayResult<T, N> {
    fn drop(&mut self) {
        match self {
            Self::NotEnoughElements { values, init_count } => {
                let init_slice =
                    ptr::slice_from_raw_parts_mut(values.as_mut_ptr() as *mut T, *init_count);
                unsafe { ptr::drop_in_place(init_slice) }
            }
            Self::Ok(_) => {
                // Automatically handled
            }
            Self::TooManyElements {
                values: _,
                next_value: _,
            } => {
                // Automatically handled
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::CollectArrayResult;
    use core::mem::MaybeUninit;
    use core::sync::atomic::{AtomicUsize, Ordering};
    use std::{panic, sync::Arc};

    #[test]
    fn ok() {
        let input = vec![0_i32, 1_i32, 2_i32];

        let output = input.into_iter().collect::<CollectArrayResult<_, 3>>();
        assert_eq!(output, CollectArrayResult::Ok([0, 1, 2]));
    }

    #[test]
    fn want_more() {
        let input = vec![0_i32, 1_i32, 2_i32];

        let output = input.into_iter().collect::<CollectArrayResult<_, 4>>();
        assert_eq!(
            output,
            CollectArrayResult::NotEnoughElements {
                values: [
                    MaybeUninit::new(0),
                    MaybeUninit::new(1),
                    MaybeUninit::new(2),
                    MaybeUninit::uninit()
                ],
                init_count: 3
            }
        );
    }

    #[test]
    fn want_fewer() {
        let input = vec![0_i32, 1_i32, 2_i32];

        let output = input.into_iter().collect::<CollectArrayResult<_, 2>>();
        let want_arr = [0_i32, 1_i32];
        let want_next = 2_i32;
        if let CollectArrayResult::TooManyElements {
            values,
            next_value: next,
        } = output
        {
            assert_eq!(values, want_arr);
            assert_eq!(next, want_next);
        } else {
            let want: CollectArrayResult<_, 2> = CollectArrayResult::TooManyElements {
                values: want_arr,
                next_value: want_next,
            };
            panic!(
                "Saw wrong elements; expected {:?} but saw {:?}",
                want, output
            );
        }
    }

    #[test]
    fn debug() {
        assert_eq!(
            "[0, 1, 2]",
            format!("{:?}", CollectArrayResult::Ok([0, 1, 2]))
        );

        let not_enough: CollectArrayResult<_, 4> = vec![0, 1, 2].into_iter().collect();
        assert_eq!(
            "CollectArrayResult::NotEnoughElements{ got: 3, expected: 4, values: [0, 1, 2] }",
            format!("{:?}", not_enough)
        );

        assert_eq!(
            "CollectArrayResult::TooManyElements{ values: [0, 1], next: 2 (possibly others...) }",
            format!(
                "{:?}",
                CollectArrayResult::TooManyElements {
                    values: [0, 1],
                    next_value: 2
                }
            )
        );
    }

    struct DropCounter(Arc<AtomicUsize>);

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn drop_ok() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let ok: CollectArrayResult<_, 3> = vec![
            DropCounter(drop_count.clone()),
            DropCounter(drop_count.clone()),
            DropCounter(drop_count.clone()),
        ]
        .into_iter()
        .collect();
        drop(ok);

        assert_eq!(3, Arc::try_unwrap(drop_count).unwrap().into_inner());
    }

    #[test]
    fn drop_too_many() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let ok: CollectArrayResult<_, 1> = vec![
            DropCounter(drop_count.clone()),
            DropCounter(drop_count.clone()),
            DropCounter(drop_count.clone()),
        ]
        .into_iter()
        .collect();
        drop(ok);

        assert_eq!(3, Arc::try_unwrap(drop_count).unwrap().into_inner());
    }

    #[test]
    fn drop_not_enough() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let ok: CollectArrayResult<_, 3> =
            vec![DropCounter(drop_count.clone())].into_iter().collect();
        drop(ok);

        assert_eq!(1, Arc::try_unwrap(drop_count).unwrap().into_inner());
    }

    #[test]
    fn drop_panic_during_collection() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let result = panic::catch_unwind(|| {
            let mut first = true;
            std::iter::from_fn(|| {
                if first {
                    first = false;
                    Some(DropCounter(drop_count.clone()))
                } else {
                    panic!("Panic'd on construction")
                }
            })
            .collect::<CollectArrayResult<_, 2>>()
        });

        assert!(result.is_err());

        assert_eq!(1, drop_count.load(Ordering::SeqCst));
    }

    #[test]
    fn drop_panic_too_many() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let result = panic::catch_unwind(|| {
            let mut first = true;
            std::iter::from_fn(|| {
                if first {
                    first = false;
                    Some(DropCounter(drop_count.clone()))
                } else {
                    panic!("Panic'd on construction")
                }
            })
            .collect::<CollectArrayResult<_, 1>>()
        });

        assert!(result.is_err());

        assert_eq!(1, drop_count.load(Ordering::SeqCst));
    }

    #[test]
    fn unwrap_ok() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let ok = vec![
            DropCounter(drop_count.clone()),
            DropCounter(drop_count.clone()),
            DropCounter(drop_count.clone()),
        ]
        .into_iter()
        .collect::<CollectArrayResult<_, 3>>()
        .unwrap();
        drop(ok);

        assert_eq!(3, Arc::try_unwrap(drop_count).unwrap().into_inner());
    }

    #[test]
    fn unwrap_too_many() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let ok = panic::catch_unwind(|| {
            vec![
                DropCounter(drop_count.clone()),
                DropCounter(drop_count.clone()),
                DropCounter(drop_count.clone()),
            ]
            .into_iter()
            .collect::<CollectArrayResult<_, 1>>()
            .unwrap()
        });

        assert!(ok.is_err());

        assert_eq!(3, Arc::try_unwrap(drop_count).unwrap().into_inner());
    }

    #[test]
    fn unwrap_not_enough() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        let ok = panic::catch_unwind(|| {
            vec![DropCounter(drop_count.clone())]
                .into_iter()
                .collect::<CollectArrayResult<_, 3>>()
                .unwrap()
        });

        assert!(ok.is_err());

        assert_eq!(1, Arc::try_unwrap(drop_count).unwrap().into_inner());
    }
}
