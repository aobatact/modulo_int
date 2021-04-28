use const_generic_wrap::ConstWrap;
use core::fmt::Debug;
use num_traits::{
    ops::overflowing::{OverflowingAdd, OverflowingMul},
    Bounded, Inv, Num, One, Pow, ToPrimitive, Unsigned, WrappingAdd, WrappingMul, WrappingNeg,
    WrappingSub, Zero,
};
use std::{
    fmt::{Display, Write},
    ops::*,
};
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct ModInt<T, M = T> {
    value: T,
    modulo: M,
}

/// Alias of [`ModInt`] for [`u32`]
/// ```
/// # use modulo_int::*;
/// # use const_generic_wrap::*;
/// assert_eq!(ModU32::<17>::new(12), ModInt::new_with_modulo(12, WrapU32::<17>));
/// ```
pub type ModU32<const N: u32> = ModInt<u32, const_generic_wrap::WrapU32<N>>;

/// Alias of [`ModInt`] for [`u64`]
/// ```
/// # use modulo_int::*;
/// # use const_generic_wrap::*;
/// assert_eq!(ModU64::<17>::new(12), ModInt::new_with_modulo(12, WrapU64::<17>));
/// ```
pub type ModU64<const N: u64> = ModInt<u64, const_generic_wrap::WrapU64<N>>;

/// Alias of [`ModInt`] for [`i32`]
/// ```
/// # use modulo_int::*;
/// # use const_generic_wrap::*;
/// assert_eq!(ModI32::<17>::new(12), ModInt::new_with_modulo(12, WrapI32::<17>));
/// ```
pub type ModI32<const N: i32> = ModInt<i32, const_generic_wrap::WrapI32<N>>;

/// Alias of [`ModInt`] for [`i64`]
/// ```
/// # use modulo_int::*;
/// # use const_generic_wrap::*;
/// assert_eq!(ModI64::<17>::new(12), ModInt::new_with_modulo(12, WrapI64::<17>));
/// ```
pub type ModI64<const N: i64> = ModInt<i64, const_generic_wrap::WrapI64<N>>;

impl<T, M> ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd + Zero,
    M: Into<T> + Clone,
{
    /// Creates new [`ModInt`] with [`ConstWrap`]. The modulo is selected statically by const generics.
    pub fn new(value: T) -> Self
    where
        M: ConstWrap<BaseType = T>,
    {
        Self::new_with_modulo(value, M::default())
    }

    /// Creates new [`ModInt`]. Modulo should be positive.
    pub fn new_with_modulo(value: T, modulo: M) -> Self {
        let t_modulo = modulo.clone().into();
        assert!(t_modulo > T::zero(), "modulo must be positive number");
        let v = value.clone() % t_modulo.clone();
        Self {
            value: if v < T::zero() { t_modulo + v } else { v },
            modulo,
        }
    }

    /// Creates new [`ModInt`] with out checking whether `modulo > 0` and `0 <= value < modulo`.
    pub unsafe fn new_unchecked(value: T, modulo: M) -> Self {
        Self { value, modulo }
    }

    /// Creates new [`ModInt`] with the value set to zero.
    pub fn zero_with_modulo(modulo: M) -> Self {
        Self::new_with_modulo(T::zero(), modulo)
    }
}

impl<T, M> ModInt<T, M> {
    /// Gets the modulo.
    pub fn modulo(&self) -> &M {
        &self.modulo
    }

    /// Gets the modulo converted to the value type.
    pub fn modulo_val(&self) -> T
    where
        M: Clone + Into<T>,
    {
        self.modulo.clone().into()
    }

    /// Gets the value.
    pub fn value(&self) -> &T {
        &self.value
    }
}

impl<T, M> ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug,
    M: Into<T> + Clone,
{
    /// Try to get the modular inverse. It will return [`None`] if `value` and `modulo` is not coprime.
    #[inline]
    pub fn checked_inv(&self) -> Option<Self> {
        let b = self.modulo_val();

        fn unsigned<T>(b: T, v: T) -> (T, T)
        where
            T: PartialOrd<T> + Clone + Num,
        {
            //unsigned
            let mut s = (T::zero(), T::one(), false, false);
            let mut r = (b.clone(), v, false, false);

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
        }
        fn signed<T>(b: T, v: T) -> (T, T)
        where
            T: PartialOrd<T> + Clone + Num,
        {
            // signed
            let mut s = (T::zero(), T::one());
            let mut r = (b.clone(), v);

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
        }

        let (rs, rr) = if T::zero() == T::min_value() {
            unsigned(b, self.value.clone())
        } else {
            signed(b, self.value.clone())
        };

        if rr != T::one() {
            None
        } else {
            Some(Self::new_with_modulo(rs, self.modulo.clone()))
        }
    }
}

impl<T, M> Display for ModInt<T, M>
where
    T: Display,
    M: Into<T> + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)?;
        f.write_str(" mod( ")?;
        self.modulo_val().fmt(f)?;
        f.write_char(')')
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

impl<T, M> Add<&ModInt<T, M>> for &ModInt<T, M>
where
    T: Bounded + Clone + OverflowingAdd + PartialOrd + Rem<Output = T> + Zero,
    M: Clone + Debug + Into<T> + PartialEq<M>,
{
    type Output = ModInt<T, M>;
    fn add(self, rhs: &ModInt<T, M>) -> Self::Output {
        debug_assert_eq!(self.modulo, rhs.modulo);
        let (v, o) = self.value.overflowing_add(&rhs.value);
        let value = if o {
            let b = self.modulo_val();
            T::max_value() % b.clone() + v % b
        } else {
            v
        };
        ModInt::new_with_modulo(value, self.modulo.clone())
    }
}

/// Same as [`Add`] because [`Add::add`] is wrapping.
impl<T, M> WrappingAdd for ModInt<T, M>
where
    Self: Add<Output = Self>,
    for<'a> &'a Self: Add<Output = Self>,
{
    fn wrapping_add(&self, v: &Self) -> Self {
        self.add(v)
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

impl<T, M> Sub<&ModInt<T, M>> for &ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd<T> + Zero + Bounded + OverflowingAdd + Sub<Output = T>,
    M: Into<T> + PartialEq<M> + Clone + Debug,
{
    type Output = ModInt<T, M>;
    fn sub(self, rhs: &ModInt<T, M>) -> Self::Output {
        debug_assert_eq!(self.modulo, rhs.modulo);
        self + &(-rhs)
    }
}

/// Same as [`Sub`] because [`Sub::sub`] is wrapping.
impl<T, M> WrappingSub for ModInt<T, M>
where
    Self: Sub<Output = Self>,
    for<'a> &'a Self: Sub<Output = Self>,
{
    fn wrapping_sub(&self, rhs: &ModInt<T, M>) -> Self {
        self - rhs
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

impl<T, M> Mul<&ModInt<T, M>> for &ModInt<T, M>
where
    T: Rem<Output = T> + Clone + PartialOrd<T> + Zero + Bounded + OverflowingMul,
    M: Into<T> + PartialEq<M> + Clone + Debug,
{
    type Output = ModInt<T, M>;
    fn mul(self, rhs: &ModInt<T, M>) -> Self::Output {
        debug_assert_eq!(self.modulo, rhs.modulo);
        let (v, o) = self.value.overflowing_mul(&rhs.value);
        let value = if o {
            let b = self.modulo_val();
            T::max_value() % b.clone() + v % b
        } else {
            v
        };
        ModInt::new_with_modulo(value, self.modulo.clone())
    }
}

/// Same as [`Mul`] because [`Mul::mul`] is wrapping.
impl<T, M> WrappingMul for ModInt<T, M>
where
    Self: Mul<Output = Self>,
    for<'a> &'a Self: Mul<Output = Self>,
{
    fn wrapping_mul(&self, rhs: &ModInt<T, M>) -> Self {
        self * rhs
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

impl<T, M> Neg for &ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Rem<Output = T> + Sub<Output = T> + Zero,
    M: Into<T> + Clone,
{
    type Output = ModInt<T, M>;
    fn neg(self) -> ModInt<T, M> {
        self.clone().neg()
    }
}

/// Same as [`Neg`] because [`Neg::neg`] is wrapping.
impl<T, M> WrappingNeg for ModInt<T, M>
where
    for<'a> &'a Self: Neg<Output = Self>,
{
    fn wrapping_neg(&self) -> ModInt<T, M> {
        self.neg()
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
    type Output = ModInt<T, M>;
    fn inv(self) -> ModInt<T, M> {
        (&self).inv()
    }
}

/// Calculate [Modular multiplicative inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse).
impl<T, M> Inv for &ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug,
    M: Into<T> + Clone,
{
    type Output = ModInt<T, M>;
    fn inv(self) -> ModInt<T, M> {
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

impl<T, M> Div for &ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num + Bounded + Debug + Bounded + OverflowingMul,
    M: Into<T> + PartialEq<M> + Clone + Debug,
{
    type Output = ModInt<T, M>;

    fn div(self, rhs: Self) -> Self::Output {
        self * &(rhs.inv())
    }
}

impl<T, M> Rem for ModInt<T, M>
where
    T: Rem<Output = T> + PartialOrd<T> + Clone + Zero,
    M: Into<T> + Clone,
{
    type Output = Self;

    fn rem(self, rhs: Self) -> Self {
        Self::new_with_modulo(self.value % rhs.value, self.modulo)
    }
}

impl<T, M> Rem for &ModInt<T, M>
where
    T: Rem<Output = T> + PartialOrd<T> + Clone + Zero,
    for<'a> &'a T: Rem<Output = T>,
    M: Into<T> + Clone,
{
    type Output = ModInt<T, M>;

    fn rem(self, rhs: Self) -> ModInt<T, M> {
        ModInt::new_with_modulo(&self.value % &rhs.value, self.modulo.clone())
    }
}

impl<T, M, E> Pow<E> for ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num,
    M: Into<T> + Clone,
    E: BitAnd<Output = E> + Clone + One + PartialOrd + ShrAssign<usize> + Zero,
{
    type Output = Self;

    /// mod pow
    fn pow(self, rhs: E) -> Self {
        self.clone().pow(rhs)
    }
}

impl<T, M, E> Pow<E> for &ModInt<T, M>
where
    T: PartialOrd<T> + Clone + Num,
    M: Into<T> + Clone,
    E: BitAnd<Output = E> + Clone + One + PartialOrd + ShrAssign<usize> + Zero,
{
    type Output = ModInt<T, M>;

    /// mod pow
    fn pow(self, mut rhs: E) -> ModInt<T, M> {
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
        ModInt::new_with_modulo(result, self.modulo.clone())
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

impl<T, M> Unsigned for ModInt<T, M> where Self: Num {}

#[cfg(test)]
mod tests {
    use crate::*;
    use const_generic_wrap::*;

    #[test]
    fn new() {
        let c17 = WrapU32::<17>;
        let l = ModInt::new_with_modulo(11, c17);
        let l2 = ModInt::new(11);
        assert_eq!(l, l2);
        let r = ModInt::new_with_modulo(28_u32, 17_u32);
        assert_eq!(l.value(), r.value());
    }

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
        let l = ModU32::<17>::new(11);
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
        let l = ModU32::<17>::new(11);
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

    #[test]
    fn display() {
        let l = ModU32::<17>::new(11);
        assert_eq!("11 mod( 17)", l.to_string());
    }
}
