#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]

//! # CPF
//!
//! Brazilian CPF parsing, validating and formatting library.
//!
//! ```rust
//! # fn main() -> Result<(), cpf::ParseCpfError> {
//! use cpf::Cpf;
//!
//! // Use the `valid` function if all you need is validating a CPF number
//! assert!(cpf::valid("385.211.390-39"));
//! assert!(cpf::valid("38521139039"));
//! assert!(!cpf::valid("000.000.000-00"));
//!
//! // Parse into a Cpf struct if you need formatting or other metadata
//! let cpf: Cpf = "38521139039".parse()?;
//! assert_eq!(format!("{cpf}"), "385.211.390-39");
//! assert_eq!(cpf.as_str(), "38521139039");
//! assert_eq!(cpf.digits(), [3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
//!
//! // Note that the Cpf struct is guaranteed to always be valid
//! assert!("000.000.000-00".parse::<Cpf>().is_err());
//! assert!(cpf::valid("385.211.390-39".parse::<Cpf>()?));
//! # Ok(())
//! # }
//! ```
//!
//! ## no_std support
//!
//! The library makes no dinamic allocation and can be used on no_std
//! environments by disabling the `std` flag:
//!
//! ```toml
//! [dependencies]
//! cpf = { version = "0.3", default-features = false }
//! ```
//!
//! ## Random CPF generation support
//!
//! The `rand` feature flag enables random CPF generation:
//!
//! ```toml
//! [dependencies]
//! cpf = { version = "0.3", features = ["rand"] }
//! rand = "0.8"
//! ```
//!
//! ```rust
//! # #[cfg(feature = "rand")] {
//! use cpf::Cpf;
//! use rand;
//! use rand::Rng;
//!
//! let cpf = rand::thread_rng().gen::<Cpf>();
//! # }
//! ```

use core::convert::TryFrom;
use core::fmt;
use core::str::{from_utf8_unchecked, FromStr};

/// Validates a CPF number.
/// ```rust
/// use cpf;
///
/// assert!(cpf::valid("385.211.390-39"));
/// assert!(!cpf::valid("000.000.000-00"));
/// ```
pub fn valid<T: AsRef<str>>(cpf: T) -> bool {
    parse(cpf).is_ok()
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub enum ParseCpfError {
    InvalidLength,
    InvalidChecksum,
    InvalidDigit,
}

/// A valid CPF number.
///
/// Initialize a `Cpf` from a `&str` or an array of digits:
/// ```rust
/// # fn main() -> Result<(), cpf::ParseCpfError> {
/// # use core::convert::TryFrom;
/// use cpf::Cpf;
///
/// let cpf1 = "385.211.390-39".parse::<Cpf>()?;
/// let cpf2 = Cpf::try_from([3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9])?;
/// assert_eq!(cpf1, cpf2);
/// # Ok(())
/// # }
/// ```
///
/// Note that the `Cpf` struct can only be initialized after a successfully parse,
/// so it is guaranteed to always be valid.
/// ```rust
/// use cpf::Cpf;
///
/// let cpf = "000.000.000-00".parse::<Cpf>();
/// assert!(cpf.is_err());
///
/// let cpf = "385.211.390-39".parse::<Cpf>().unwrap();
/// assert!(cpf::valid(cpf));
/// ```
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Cpf {
    digits: [u8; 11],
}

impl Cpf {
    /// The Cpf digits.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCpfError> {
    /// use cpf::Cpf;
    ///
    /// let cpf: Cpf = "385.211.390-39".parse()?;
    /// assert_eq!(cpf.digits(), [3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn digits(&self) -> [u8; 11] {
        self.digits.map(|digit| digit - 48)
    }

    /// Returns the (unformatted) CPF number.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCpfError> {
    /// use cpf::Cpf;
    ///
    /// let cpf: Cpf = "385.211.390-39".parse()?;
    /// assert_eq!(cpf.as_str(), "38521139039");
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note that even being unformatted, the number will be padded by zeros.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCpfError> {
    /// use cpf::Cpf;
    ///
    /// let cpf: Cpf = "5120101".parse()?;
    /// assert_eq!(cpf.as_str(), "00005120101");
    /// # Ok(())
    /// # }
    /// ```
    pub fn as_str(&self) -> &str {
        // Safety: all the digits are guaranteed to be in ASCII range
        unsafe { from_utf8_unchecked(&self.digits) }
    }

    fn from_valid_digits(digits: [u8; 11]) -> Cpf {
        Cpf {
            digits: digits.map(|digit| digit + 48),
        }
    }
}

fn valid_checksum(digits: &[u8; 11]) -> bool {
    if digits.windows(2).all(|d| d[0] == d[1]) {
        return false;
    }

    [9, 10]
        .iter()
        .all(|d| digits[*d] == check_digit(&digits[0..*d]))
}

fn check_digit(digits: &[u8]) -> u8 {
    let check_sum = digits
        .iter()
        .rev()
        .zip(2..)
        .map(|(i, n)| (i * n) as usize)
        .sum::<usize>();

    match check_sum % 11 {
        n if n < 2 => 0,
        n => 11 - n as u8,
    }
}

fn parse<T: AsRef<str>>(cpf: T) -> Result<Cpf, ParseCpfError> {
    try_from_iter(
        cpf.as_ref()
            .chars()
            .filter_map(|c| c.to_digit(10).map(|d| d as u8))
            .rev(),
    )
}

fn try_from_iter(iter: impl Iterator<Item = u8>) -> Result<Cpf, ParseCpfError> {
    let mut digits: [u8; 11] = [0; 11];

    for (i, digit) in iter
        .map(|digit| {
            matches!(digit, 0..=9)
                .then_some(digit)
                .ok_or(ParseCpfError::InvalidDigit)
        })
        .enumerate()
    {
        if i == 11 {
            return Err(ParseCpfError::InvalidLength);
        }

        digits[10 - i] = digit?;
    }

    if digits
        .iter()
        .take_while(|digit| **digit == 0)
        .take(10)
        .count()
        > 9
    {
        return Err(ParseCpfError::InvalidLength);
    }

    if !valid_checksum(&digits) {
        return Err(ParseCpfError::InvalidChecksum);
    }

    Ok(Cpf::from_valid_digits(digits))
}

impl AsRef<str> for Cpf {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Debug for Cpf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Cpf")
            .field(&format_args!("{}", self))
            .finish()
    }
}

impl fmt::Display for Cpf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let digits = self.as_str();
        write!(
            f,
            "{}.{}.{}-{}",
            &digits[0..3],
            &digits[3..6],
            &digits[6..9],
            &digits[9..11]
        )
    }
}

impl FromStr for Cpf {
    type Err = ParseCpfError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse(s)
    }
}

impl TryFrom<&str> for Cpf {
    type Error = ParseCpfError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        parse(value)
    }
}

impl TryFrom<[u8; 11]> for Cpf {
    type Error = ParseCpfError;

    fn try_from(value: [u8; 11]) -> Result<Self, Self::Error> {
        if valid_checksum(&value) {
            Ok(Cpf::from_valid_digits(value))
        } else {
            Err(ParseCpfError::InvalidChecksum)
        }
    }
}

impl TryFrom<&[u8]> for Cpf {
    type Error = ParseCpfError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        try_from_iter(value.iter().copied().rev())
    }
}

impl fmt::Display for ParseCpfError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseCpfError::InvalidChecksum => "invalid Cpf checksum".fmt(f),
            ParseCpfError::InvalidLength => "invalid Cpf length".fmt(f),
            ParseCpfError::InvalidDigit => "invalid Cpf digit".fmt(f),
        }
    }
}

#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "std")]
impl std::error::Error for ParseCpfError {}

#[cfg(feature = "rand")]
use rand::{
    distributions::{Distribution, Standard, Uniform},
    Rng,
};

/// Random CPF generation
///
/// ```rust
/// # #[cfg(feature = "rand")] {
/// use cpf::Cpf;
/// use rand::Rng;
///
/// let cpf: Cpf = rand::thread_rng().gen();
/// # }
/// ```
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
impl Distribution<Cpf> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Cpf {
        let digit = Uniform::from(0..=9);
        let mut digits: [u8; 11] = [0; 11];
        for d in digits.iter_mut().take(9) {
            *d = digit.sample(rng);
        }
        digits[9] = check_digit(&digits[0..9]);
        digits[10] = check_digit(&digits[0..10]);

        Cpf::from_valid_digits(digits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_validates() {
        assert!(valid("385.211.390-39"));
        assert!(!valid("385.211.390-49"));
    }

    #[test]
    fn it_disallow_same_digit_numbers() {
        assert!(!valid("111.111.111-11"));
        assert!(!valid("222.222.222-22"));
        assert!(!valid("333.333.333-33"));
        assert!(!valid("444.444.444-44"));
        assert!(!valid("555.555.555-55"));
        assert!(!valid("666.666.666-66"));
        assert!(!valid("777.777.777-77"));
        assert!(!valid("888.888.888-88"));
        assert!(!valid("999.999.999-99"));
    }

    #[test]
    fn it_parses() {
        let cpf = "38521139039".parse::<Cpf>();
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), [3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = "385.211.390-39".parse::<Cpf>();
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), [3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
    }

    #[test]
    fn it_initializes_with_digits() {
        let cpf = Cpf::try_from([3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), [3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = Cpf::try_from([4, 4, 7, 2, 1, 8, 4, 9, 8, 1, 9]);
        assert!(cpf.is_err());
    }

    #[test]
    fn it_fails_with_invalid_digits() {
        let x = [3u8, 11, 9, 0, 8 + 22, 8, 5, 6, 33, 3, 2];

        assert_eq!(
            Cpf::try_from(&x[..]).unwrap_err(),
            ParseCpfError::InvalidDigit
        );
    }

    #[test]
    fn it_initializes_with_digits_on_heap() {
        extern crate std;
        use std::vec;

        let cpf = Cpf::try_from(&vec![3_u8, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9][..]);
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), [3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = Cpf::try_from(&vec![4_u8, 4, 7, 2, 1, 8, 4, 9, 8, 1, 9][..]);
        assert!(cpf.is_err());
    }

    #[test]
    fn it_pads_numbers_with_less_than_eleven_digits() {
        let cpf = parse("5120101").unwrap();
        assert_eq!(cpf.digits(), [0, 0, 0, 0, 5, 1, 2, 0, 1, 0, 1]);
    }

    #[test]
    fn it_fails_to_parse_numbers_that_dont_match_the_min_length() {
        let cpf = "0".parse::<Cpf>();
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidLength);

        let cpf = "01".parse::<Cpf>();
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidLength);

        let cpf = "272".parse::<Cpf>();
        assert!(cpf.is_ok());
    }

    #[test]
    fn it_fails_to_parse_numbers_with_more_than_eleven_digits() {
        let cpf = "138521139039".parse::<Cpf>();
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidLength);
    }

    #[test]
    fn it_fails_on_invalid_checksums() {
        let cpf = "38521139038".parse::<Cpf>();
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidChecksum);
    }

    #[test]
    fn it_display() {
        extern crate std;
        let cpf = "38521139039".parse::<Cpf>().unwrap();
        assert_eq!(std::format!("{}", cpf), "385.211.390-39");
    }

    #[test]
    #[cfg(feature = "rand")]
    fn it_generates_valid_numbers() {
        use rand::{rngs::SmallRng, Rng, SeedableRng};
        let mut rng = SmallRng::seed_from_u64(0);
        for _ in 1..10000 {
            let cpf = rng.gen::<Cpf>();
            assert!(valid(cpf));
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn it_generates_different_numbers() {
        use rand::{rngs::SmallRng, Rng, SeedableRng};
        let mut rng = SmallRng::seed_from_u64(0);
        let cpf1 = rng.gen::<Cpf>();
        let cpf2 = rng.gen::<Cpf>();
        assert_ne!(cpf1, cpf2);
    }
}

#[cfg(feature = "serde")]
mod __serde {
    use core::fmt;

    use serde::de::{Error, Visitor};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::*;

    impl<'de> Deserialize<'de> for Cpf {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct CpfVisitor;

            impl<'de> Visitor<'de> for CpfVisitor {
                type Value = Cpf;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("a string containing a valid Cpf")
                }

                fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    v.parse().map_err(Error::custom)
                }

                fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    v.parse().map_err(Error::custom)
                }

                #[cfg(feature = "std")]
                fn visit_string<E>(self, v: std::string::String) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    v.parse().map_err(Error::custom)
                }
            }

            deserializer.deserialize_str(CpfVisitor)
        }
    }

    impl Serialize for Cpf {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.as_str().serialize(serializer)
        }
    }

    #[cfg(test)]
    mod tests {
        use serde::de::value::Error;
        use serde::de::IntoDeserializer;

        use super::*;

        #[test]
        fn it_deserializes_valid_str() {
            use serde::de::value::StrDeserializer;

            let de: StrDeserializer<'_, Error> = "385.211.390-39".into_deserializer();
            assert!(Cpf::deserialize(de).is_ok());
        }

        #[test]
        fn it_deserializes_invalid_str() {
            use serde::de::value::StrDeserializer;

            let de: StrDeserializer<'_, Error> = "385.211.390-49".into_deserializer();
            assert!(Cpf::deserialize(de).is_err());
        }

        #[test]
        #[cfg(feature = "std")]
        fn it_deserializes_valid_borrowed_cow() {
            use std::borrow::Cow;

            use serde::de::value::CowStrDeserializer;

            let cpf = "385.211.390-39";
            let de: CowStrDeserializer<'_, Error> = Cow::from(cpf).into_deserializer();
            assert!(Cpf::deserialize(de).is_ok());
        }

        #[test]
        #[cfg(feature = "std")]
        fn it_deserializes_invalid_borrowed_cow() {
            use std::borrow::Cow;

            use serde::de::value::CowStrDeserializer;

            let cpf = "385.211.390-49";
            let de: CowStrDeserializer<'_, Error> = Cow::from(cpf).into_deserializer();
            assert!(Cpf::deserialize(de).is_err());
        }

        #[test]
        #[cfg(feature = "std")]
        fn it_deserializes_valid_owned_cow() {
            use std::borrow::Cow;
            use std::string::ToString;

            use serde::de::value::CowStrDeserializer;

            let cpf = "385.211.390-39".to_string();
            let de: CowStrDeserializer<'_, Error> = Cow::from(cpf).into_deserializer();
            assert!(Cpf::deserialize(de).is_ok());
        }

        #[test]
        #[cfg(feature = "std")]
        fn it_deserializes_invalid_owned_cow() {
            use std::borrow::Cow;
            use std::string::ToString;

            use serde::de::value::CowStrDeserializer;

            let cpf = "385.211.390-49".to_string();
            let de: CowStrDeserializer<'_, Error> = Cow::from(cpf).into_deserializer();
            assert!(Cpf::deserialize(de).is_err());
        }

        #[test]
        #[cfg(feature = "std")]
        fn it_deserializes_valid_string() {
            use std::string::ToString;

            use serde::de::value::StringDeserializer;

            let de: StringDeserializer<Error> = "385.211.390-39".to_string().into_deserializer();
            assert!(Cpf::deserialize(de).is_ok());
        }

        #[test]
        #[cfg(feature = "std")]
        fn it_deserializes_invalid_string() {
            use std::string::ToString;

            use serde::de::value::StringDeserializer;

            let de: StringDeserializer<Error> = "385.211.390-49".to_string().into_deserializer();
            assert!(Cpf::deserialize(de).is_err());
        }
    }
}
