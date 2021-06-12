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
//! assert_eq!(format!("{}", cpf), "385.211.390-39");
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
//! cpf = { version = "0.2", default-features = false }
//! ```
//!
//! ## Random CPF generation support
//!
//! The `rand` feature flag enables random CPF generation:
//!
//! ```toml
//! [dependencies]
//! cpf = { version = "0.2", features = ["rand"] }
//! rand = "0.8"
//! ```
//!
//! ```rust
//! # #[cfg(feature = "rand")] {
//! use cpf::Cpf;
//! use rand;
//! use rand::Rng;
//!
//! let cpf: Cpf = rand::thread_rng().gen();
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
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
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
        let mut digits: [u8; 11] = [0; 11];
        for (i, digit) in self.digits.iter().enumerate() {
            digits[i] = digit - 48;
        }
        digits
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
        let mut ascii_digits: [u8; 11] = [48; 11];
        for (i, digit) in digits.iter().enumerate() {
            ascii_digits[i] = digit + 48;
        }

        Cpf {
            digits: ascii_digits,
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
    let cpf = cpf.as_ref();

    let mut digits: [u8; 11] = [0; 11];

    for (i, digit) in cpf
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .rev()
        .enumerate()
    {
        if i == 11 {
            return Err(ParseCpfError::InvalidLength);
        } else {
            digits[10 - i] = digit
        }
    }

    if digits.iter().take_while(|digit| **digit == 0).count() > 9 {
        Err(ParseCpfError::InvalidLength)
    } else if valid_checksum(&digits) {
        Ok(Cpf::from_valid_digits(digits))
    } else {
        Err(ParseCpfError::InvalidChecksum)
    }
}

impl AsRef<str> for Cpf {
    fn as_ref(&self) -> &str {
        self.as_str()
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

impl fmt::Display for ParseCpfError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseCpfError::InvalidChecksum => "invalid Cpf checksum".fmt(f),
            ParseCpfError::InvalidLength => "invalid Cpf lenght".fmt(f),
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
        extern crate std;
        use rand;
        use rand::Rng;
        for _ in 1..10000 {
            let cpf = rand::thread_rng().gen::<Cpf>();
            assert!(valid(cpf));
        }
    }
}
