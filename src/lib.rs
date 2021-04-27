use const_generic_wrap::ConstWrap;
use core::fmt::Debug;
use num_traits::{
    ops::overflowing::{OverflowingAdd, OverflowingMul},
    Bounded, Inv, Num, One, Pow, ToPrimitive, Zero,
};
use std::{fmt::Display, ops::*};
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct ModInt<T, M>
where
    T: Rem<T, Output = T>,
    M: Into<T>,
{
    value: T,
    modulo: M,
}

impl<T, M> ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    M: Into<T> + Clone,
{
    pub fn new(value: T) -> Self
    where
        M: ConstWrap<BaseType = T>,
    {
        Self::new_with_modulo(value, M::default())
    }

    pub fn new_with_modulo(value: T, modulo: M) -> Self {
        let t_modulo = modulo.clone().into();
        debug_assert!(t_modulo > T::zero());
        let v = value.clone() % t_modulo.clone();
        Self {
            value: if v < T::zero() { t_modulo + v } else { v },
            modulo,
        }
    }
}

impl<T, M> ModInt<T, M>
where
    T: Rem<Output = T>,
    M: Into<T>,
{
    pub unsafe fn new_unchecked(value: T, modulo: M) -> Self {
        Self { value, modulo }
    }

    pub fn modulo(&self) -> &M {
        &self.modulo
    }

    pub fn modulo_val(&self) -> T
    where
        M: Clone,
    {
        self.modulo.clone().into()
    }

    pub fn value(&self) -> &T {
        &self.value
    }
}

impl<T, M> ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug,
    M: Into<T> + Clone,
{
    pub fn checked_inv(self) -> Option<Self> {
        let b = self.modulo_val();

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

        if rr != T::one() {
            None
        } else {
            Some(Self::new_with_modulo(rs, self.modulo))
        }
    }
}

impl<T, M> Display for ModInt<T, M>
where
    T: Rem<T, Output = T> + Display,
    M: Into<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, M> From<T> for ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    M: ConstWrap<BaseType = T> + Into<T>,
{
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T, M> From<(T, M)> for ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    M: Into<T> + Clone,
{
    fn from(value: (T, M)) -> Self {
        Self::new_with_modulo(value.0, value.1)
    }
}

impl<T, M> Add<ModInt<T, M>> for ModInt<T, M>
where
    T: Bounded + Clone + OverflowingAdd + PartialOrd + Rem<Output = T> + Zero,
    M: Clone + Debug + Into<T> + PartialEq<M>,
{
    type Output = Self;
    fn add(self, rhs: ModInt<T, M>) -> Self::Output {
        debug_assert_eq!(self.modulo, rhs.modulo);
        let (v, o) = self.value.overflowing_add(&rhs.value);
        let value = if o {
            let b = self.modulo_val();
            T::max_value() % b.clone() + v % b
        } else {
            v
        };
        ModInt::new_with_modulo(value, self.modulo)
    }
}

impl<T, M> Sub<ModInt<T, M>> for ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd<T> + Zero + Bounded + OverflowingAdd + Sub<Output = T>,
    M: Into<T> + PartialEq<M> + Clone + Debug,
{
    type Output = Self;
    fn sub(self, rhs: ModInt<T, M>) -> Self::Output {
        debug_assert_eq!(self.modulo, rhs.modulo);
        self + (-rhs)
    }
}

impl<T, M> Mul<ModInt<T, M>> for ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd<T> + Zero + Bounded + OverflowingMul,
    M: Into<T> + PartialEq<M> + Clone + Debug,
{
    type Output = Self;
    fn mul(self, rhs: ModInt<T, M>) -> Self::Output {
        debug_assert_eq!(self.modulo, rhs.modulo);
        let (v, o) = self.value.overflowing_mul(&rhs.value);
        let value = if o {
            let b = self.modulo_val();
            T::max_value() % b.clone() + v % b
        } else {
            v
        };
        ModInt::new_with_modulo(value, self.modulo)
    }
}

impl<T, M> Neg for ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Rem<Output = T> + Sub<Output = T> + Zero,
    M: Into<T> + Clone,
{
    type Output = Self;
    fn neg(self) -> Self {
        debug_assert!(self.value < self.modulo_val());
        debug_assert!(self.value >= T::zero());
        unsafe { Self::new_unchecked(self.modulo_val() - self.value, self.modulo) }
    }
}

impl<T, M> Zero for ModInt<T, M>
where
    T: Bounded + Clone + OverflowingAdd + PartialOrd + Rem<Output = T> + Zero,
    M: Clone + Debug + Into<T> + PartialEq<M> + ConstWrap<BaseType = T>,
{
    fn zero() -> Self {
        ModInt::new(T::zero())
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
}

impl<T, M> One for ModInt<T, M>
where
    T: Bounded
        + Clone
        + OverflowingAdd
        + OverflowingMul
        + PartialOrd
        + Rem<Output = T>
        + Zero
        + One,
    M: Clone + Debug + Into<T> + PartialEq<M> + ConstWrap<BaseType = T>,
{
    fn one() -> Self {
        ModInt::new(T::one())
    }

    fn is_one(&self) -> bool {
        self.value.is_one()
    }
}

/// Calculate [Modular multiplicative inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse).
impl<T, M> Inv for ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug,
    M: Into<T> + Clone,
{
    type Output = Self;
    fn inv(self) -> Self {
        self.clone().checked_inv().expect(&format!(
            "Cannot inverse. {:?} and {:?} is not coprimpe.",
            self.value(),
            self.modulo_val()
        ))
    }
}

/// ```
/// # use modulo_int::*;
/// use num_traits::Inv;
/// use const_generic_wrap::WrapI32;
/// let c17 = WrapI32::<17>;
/// for i in 1..17 {
///     let l = ModInt::new_with_modulo(i, c17);
///     for j in 1..17 {
///         let r = ModInt::new_with_modulo(j, c17);
///         assert_eq!(l * r.inv(), l / r);
///         assert_eq!(l, (l / r) * r);
///     }
/// }
/// ```
impl<T, M> Div for ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug + Bounded + OverflowingMul,
    M: Into<T> + PartialEq<M> + Clone + Debug,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * (rhs.inv())
    }
}

impl<T, M> Rem for ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num,
    M: Into<T> + Clone,
{
    type Output = Self;

    fn rem(self, rhs: Self) -> Self {
        Self::new_with_modulo(self.value % rhs.value, self.modulo)
    }
}

impl<T, M, E> Pow<E> for ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num,
    M: Into<T> + Clone,
    E: BitAnd<Output = E> + Clone + One + PartialOrd + ShrAssign<usize> + Zero,
{
    type Output = Self;

    fn pow(self, mut rhs: E) -> Self {
        let mut value = self.value().clone();
        let modulo = self.modulo_val();
        let mut result = T::one();
        let ez = E::zero();
        let eo = E::one();
        while rhs > ez {
            if (rhs.clone() & eo.clone()).is_one() {
                result = (result * value.clone()) % modulo.clone();
            }
            rhs >>= 1;
            value = (value.clone() * value) % modulo.clone();
        }
        Self::new_with_modulo(result, self.modulo)
    }
}

impl<T, M> Num for ModInt<T, M>
where
    T: Num + Bounded + Clone + Debug + PartialOrd<T> + OverflowingAdd + OverflowingMul,
    M: Clone + Debug + ConstWrap<BaseType = T> + Into<T> + PartialEq,
{
    type FromStrRadixErr = T::FromStrRadixErr;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        T::from_str_radix(str, radix).map(|x| Self::new(x))
    }
}

impl<T, M> Bounded for ModInt<T, M>
where
    T: Rem<T, Output = T> + Zero + Clone + PartialOrd,
    M: Into<T> + Clone + ConstWrap<BaseType = T>,
{
    fn min_value() -> Self {
        T::zero().into()
    }

    fn max_value() -> Self {
        M::default().into().into()
    }
}

impl<T, M> ToPrimitive for ModInt<T, M>
where
    T: Rem<T, Output = T> + ToPrimitive,
    M: Into<T>,
{
    fn to_i64(&self) -> Option<i64> {
        self.value().to_i64()
    }

    fn to_u64(&self) -> Option<u64> {
        self.value().to_u64()
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use const_generic_wrap::*;

    #[test]
    fn add() {
        let c17 = WrapU32::<17>;
        let l = ModInt::new_with_modulo(11, c17);
        assert_eq!(11, *l.value());
        let r = 35.into();
        let lr = l + r;
        assert_eq!(12, *lr.value());
        let r = 36.into();
        let lr = l + r;
        assert_eq!(13, *lr.value());
        let r = 40.into();
        let lr = l + r;
        assert_eq!(0, *lr.value());
    }

    #[test]
    fn sub() {
        let c17 = WrapU32::<17>;
        let l = ModInt::new_with_modulo(11, c17);
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
        let l = ModInt::new_with_modulo(11, c17);
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
            let l = ModInt::new_with_modulo(i, c17);
            assert_eq!(i, *l.value());
            assert_eq!(1, *(l * l.inv()).value());
        }
        let c12 = WrapU32::<12>;
        assert!(ModInt::new_with_modulo(4, c12).checked_inv().is_none());
        assert!(ModInt::new_with_modulo(8, c12).checked_inv().is_none());
    }

    #[test]
    fn inv_i() {
        let c17 = WrapI32::<17>;
        for i in 1..17 {
            let l = ModInt::new_with_modulo(i, c17);
            assert_eq!(i, *l.value());
            assert_eq!(1, *(l * l.inv()).value());
        }
        let c12 = WrapI32::<12>;
        assert!(ModInt::new_with_modulo(4, c12).checked_inv().is_none());
        assert!(ModInt::new_with_modulo(8, c12).checked_inv().is_none());
    }

    #[test]
    fn div() {
        let c17 = WrapI32::<17>;
        for i in 1..17 {
            let l = ModInt::new_with_modulo(i, c17);
            for j in 1..17 {
                let r = ModInt::new_with_modulo(j, c17);
                assert_eq!(l, (l / r) * r);
            }
        }
    }
}
