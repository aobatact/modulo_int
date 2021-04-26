use core::fmt::Debug;
use num_traits::{
    ops::overflowing::{OverflowingAdd, OverflowingMul},
    Bounded, Inv, Num, One, Zero,
};
use std::{fmt::Display, ops::*};
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct ModInt<T, B>
where
    T: Rem<T, Output = T>,
    B: Into<T>,
{
    value: T,
    bound: B,
}

impl<T, B> ModInt<T, B>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    B: Into<T> + Clone,
{
    pub fn new(value: T) -> Self
    where
        B: Default,
    {
        Self::new_with_bound(value, B::default())
    }

    pub fn new_with_bound(value: T, bound: B) -> Self {
        let t_bound = bound.clone().into();
        debug_assert!(t_bound > T::zero());
        let v = value.clone() % t_bound.clone();
        Self {
            value: if v < T::zero() { t_bound + v } else { v },
            bound,
        }
    }

    pub unsafe fn new_unchecked(value: T, bound: B) -> Self {
        Self { value, bound }
    }

    pub fn bound(&self) -> &B {
        &self.bound
    }

    pub fn bound_val(&self) -> T {
        self.bound.clone().into()
    }

    pub fn value(&self) -> &T {
        &self.value
    }
}

impl<T, B> Display for ModInt<T, B>
where
    T: Rem<T, Output = T> + Display,
    B: Into<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, B> From<T> for ModInt<T, B>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    B: Into<T> + Clone + Default,
{
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T, B> From<(T, B)> for ModInt<T, B>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    B: Into<T> + Clone + Default,
{
    fn from(value: (T, B)) -> Self {
        Self::new_with_bound(value.0, value.1)
    }
}

impl<T, B> Add<ModInt<T, B>> for ModInt<T, B>
where
    T: Bounded + Clone + OverflowingAdd + PartialOrd + Rem<Output = T> + Zero,
    B: Clone + Debug + Into<T> + PartialEq<B>,
{
    type Output = ModInt<T, B>;
    fn add(self, rhs: ModInt<T, B>) -> Self::Output {
        debug_assert_eq!(self.bound, rhs.bound);
        let (v, o) = self.value.overflowing_add(&rhs.value);
        let value = if o {
            let b = self.bound_val();
            T::max_value() % b.clone() + v % b
        } else {
            v
        };
        ModInt::new_with_bound(value, self.bound)
    }
}

impl<T, B> Sub<ModInt<T, B>> for ModInt<T, B>
where
    T: Rem<Output = T> + Clone + PartialOrd<T> + Zero + Bounded + OverflowingAdd + Sub<Output = T>,
    B: Into<T> + PartialEq<B> + Clone + Debug,
{
    type Output = ModInt<T, B>;
    fn sub(self, rhs: ModInt<T, B>) -> Self::Output {
        debug_assert_eq!(self.bound, rhs.bound);
        self + (-rhs)
    }
}

impl<T, B> Mul<ModInt<T, B>> for ModInt<T, B>
where
    T: Rem<Output = T> + Clone + PartialOrd<T> + Zero + Bounded + OverflowingMul,
    B: Into<T> + PartialEq<B> + Clone + Debug,
{
    type Output = ModInt<T, B>;
    fn mul(self, rhs: ModInt<T, B>) -> Self::Output {
        debug_assert_eq!(self.bound, rhs.bound);
        let (v, o) = self.value.overflowing_mul(&rhs.value);
        let value = if o {
            let b = self.bound_val();
            T::max_value() % b.clone() + v % b
        } else {
            v
        };
        ModInt::new_with_bound(value, self.bound)
    }
}

impl<T, B> Neg for ModInt<T, B>
where
    T: PartialOrd<T> + Clone + Rem<Output = T> + Sub<Output = T> + Zero,
    B: Into<T> + Clone,
{
    type Output = Self;
    fn neg(self) -> Self {
        unsafe { Self::new_unchecked(self.bound_val() - self.value, self.bound) }
    }
}

impl<T, B> Zero for ModInt<T, B>
where
    T: Bounded + Clone + OverflowingAdd + PartialOrd + Rem<Output = T> + Zero,
    B: Clone + Debug + Into<T> + PartialEq<B> + Default,
{
    fn zero() -> Self {
        ModInt::new(T::zero())
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
}

impl<T, B> One for ModInt<T, B>
where
    T: Bounded
        + Clone
        + OverflowingAdd
        + OverflowingMul
        + PartialOrd
        + Rem<Output = T>
        + Zero
        + One,
    B: Clone + Debug + Into<T> + PartialEq<B> + Default,
{
    fn one() -> Self {
        ModInt::new(T::one())
    }

    fn is_one(&self) -> bool {
        self.value.is_one()
    }
}

impl<T, B> Inv for ModInt<T, B>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug,
    B: Into<T> + Clone,
{
    type Output = Self;
    fn inv(self) -> Self {
        let b = self.bound_val();

        let (rs, rr) = if T::zero() == T::min_value() {
            //unsigned
            let mut s = (T::zero(), T::one(), false, false);
            let mut r = (b.clone(), self.value.clone(), false, false);

            while !r.0.is_zero() {
                let q = r.1.clone() / r.0.clone();
                let q_s = r.2 ^ r.3;
                let f = |mut r: (T, T, bool, bool)| {
                    core::mem::swap(&mut r.0, &mut r.1);
                    core::mem::swap(&mut r.2, &mut r.3);
                    let m = q.clone() * r.1.clone();
                    let rr = if (q_s ^ r.3) ^ r.2 {
                        (r.0 + m, r.2)
                    } else {
                        if r.0 > m {
                            (r.0 - m, r.2)
                        } else {
                            (m - r.0, !r.2)
                        }
                    };
                    r.0 = rr.0;
                    r.2 = rr.1;
                    r
                };
                r = f(r);
                s = f(s);
            }
            (
                if s.3 { b.clone() - s.1 } else { s.1 },
                if r.3 {
                    b.clone() - r.1.clone()
                } else {
                    r.1.clone()
                },
            )
        } else {
            // signed
            let mut s = (T::zero(), T::one());
            let mut r = (b.clone(), self.value.clone());

            while !r.0.is_zero() {
                let q = r.1.clone() / r.0.clone();
                let f = |mut r: (T, T)| {
                    core::mem::swap(&mut r.0, &mut r.1);
                    let m = q.clone() * r.1.clone();
                    r.0 = r.0 - m;
                    r
                };
                r = f(r);
                s = f(s);
            }
            (
                s.1,
                if r.1 < T::zero() {
                    b.clone() - r.1.clone()
                } else {
                    r.1.clone()
                },
            )
        };

        assert!(
            rr == T::one(),
            "Cannot Inverse {:?} for mod {:?}",
            self.value,
            b
        );
        Self::new_with_bound(rs, self.bound)
    }
}

impl<T, B> Div for ModInt<T, B>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug + Bounded + OverflowingMul,
    B: Into<T> + PartialEq<B> + Clone + Debug,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * (rhs.inv())
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use const_generic_wrap::*;

    #[test]
    fn add() {
        let c17 = WrapU32::<17>;
        let l = ModInt::new_with_bound(11, c17);
        assert_eq!(11, *l.value());
        let r = 35.into();
        let lr = l + r;
        assert_eq!(12, *lr.value());
        let r = 36.into();
        let lr = l + r;
        assert_eq!(13, *lr.value());
    }

    #[test]
    fn sub() {
        let c17 = WrapU32::<17>;
        let l = ModInt::new_with_bound(11, c17);
        assert_eq!(11, *l.value());
        let r = 35.into();
        let lr = l - r;
        assert_eq!(10, *lr.value());
        let r = 36.into();
        let lr = l - r;
        assert_eq!(9, *lr.value());
    }

    #[test]
    fn mul() {
        let c17 = WrapU32::<17>;
        let l = ModInt::new_with_bound(11, c17);
        assert_eq!(11, *l.value());
        let r = 35.into();
        let lr = l * r;
        assert_eq!(11, *lr.value());
        let r = 36.into();
        let lr = l * r;
        assert_eq!(5, *lr.value());
    }

    #[test]
    fn inv_u() {
        let c17 = WrapU32::<17>;
        for i in 1..17 {
            let l = ModInt::new_with_bound(i, c17);
            assert_eq!(i, *l.value());
            assert_eq!(1, *(l * l.inv()).value());
        }
    }

    #[test]
    fn inv_i() {
        let c17 = WrapI32::<17>;
        for i in 1..17 {
            let l = ModInt::new_with_bound(i, c17);
            assert_eq!(i, *l.value());
            assert_eq!(1, *(l * l.inv()).value());
        }
    }
}
