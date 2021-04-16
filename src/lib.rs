#![no_std]

//! # CPF
//!
//! Brazilian CPF parsing, validating and formatting library.
//!
//! ```rust
//! # fn main() -> Result<(), cpf::ParseCPFError> {
//! use cpf::CPF;
//!
//! // If all you need is validating a CPF number, use the `valid` function:
//! assert!(cpf::valid("38521139039"));
//!
//! // For formatting and additional metadata from the number, parse into the CPF struct:
//! let cpf: CPF = "38521139039".parse()?;
//!
//! assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
//! assert_eq!(cpf.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
//! # Ok(())
//! # }
//! ```
//!
//! ## no_std support
//!
//! The library can be used on no_std environments by disabling the `std` flag:
//!
//! ```toml
//! [dependencies]
//! cpf = { version = "0.1", default-features = false }
//! ```
//!
//! ## Random CPF generation support
//!
//! The `rand` feature flag enables random CPF generation:
//!
//! ```toml
//! [dependencies]
//! cpf = { version = "0.1", features = ["rand"] }
//! rand = "0.8.3"
//! ```
//!
//! ```rust
//! # #[cfg(feature = "rand")] {
//! use cpf::CPF;
//! use rand;
//! use rand::Rng;
//!
//! let cpf: CPF = rand::thread_rng().gen();
//! # }
//! ```

use arrayvec::{ArrayString, ArrayVec};
use core::char::from_digit;
use core::convert::TryFrom;
use core::fmt;
use core::str::FromStr;

/// Validates a CPF number.
/// ```
/// use cpf;
///
/// assert!(cpf::valid("385.211.390-39"));
/// assert!(!cpf::valid("385.211.390-49"));
/// ```
pub fn valid<T: AsRef<str>>(cpf: T) -> bool {
    parse(cpf).is_ok()
}

#[derive(Debug, PartialEq, Clone)]
pub enum ParseCPFError {
    InvalidLength,
    InvalidChecksum,
}

/// A valid CPF number.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CPF {
    digits: [u8; 11],
}

impl CPF {
    /// The CPF digits.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCPFError> {
    /// use cpf::CPF;
    ///
    /// let cpf: CPF = "385.211.390-39".parse()?;
    ///
    /// assert_eq!(cpf.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn digits(&self) -> &[u8; 11] {
        &self.digits
    }

    /// Formats a CPF number.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCPFError> {
    /// use cpf::CPF;
    ///
    /// let cpf: CPF = "38521139039".parse()?;
    ///
    /// assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note that numbers with less than 11 digits will be padded by zeros.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCPFError> {
    /// # use cpf::CPF;
    /// let cpf: CPF = "5120101".parse()?;
    ///
    /// assert_eq!(cpf.formatted().as_str(), "000.051.201-01");
    /// # Ok(())
    /// # }
    /// ```
    pub fn formatted(&self) -> ArrayString<14> {
        let d = self
            .digits
            .iter()
            .map(|d| from_digit((*d).into(), 10).unwrap())
            .collect::<ArrayVec<char, 11>>();

        let mut fmt = ArrayString::<14>::new();
        fmt.push(d[0]);
        fmt.push(d[1]);
        fmt.push(d[2]);
        fmt.push('.');
        fmt.push(d[3]);
        fmt.push(d[4]);
        fmt.push(d[5]);
        fmt.push('.');
        fmt.push(d[6]);
        fmt.push(d[7]);
        fmt.push(d[8]);
        fmt.push('-');
        fmt.push(d[9]);
        fmt.push(d[10]);
        fmt
    }
}

fn valid_digits(digits: &[u8; 11]) -> bool {
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

fn parse<T: AsRef<str>>(cpf: T) -> Result<CPF, ParseCPFError> {
    let cpf = cpf.as_ref();

    let mut digits = ArrayVec::<u8, 11>::new();

    for (i, digit) in cpf
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .enumerate()
    {
        if i == 11 {
            return Err(ParseCPFError::InvalidLength);
        } else {
            digits.push(digit);
        }
    }

    if digits.len() < 3 {
        return Err(ParseCPFError::InvalidLength);
    }

    for i in 0..digits.remaining_capacity() {
        digits.insert(i, 0);
    }

    let digits = digits.into_inner().unwrap();

    if valid_digits(&digits) {
        Ok(CPF { digits })
    } else {
        Err(ParseCPFError::InvalidChecksum)
    }
}

impl fmt::Display for CPF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for c in self
            .digits()
            .iter()
            .map(|d| from_digit((*d).into(), 10).unwrap())
        {
            write!(f, "{}", c)?;
        }
        Ok(())
    }
}

impl FromStr for CPF {
    type Err = ParseCPFError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse(s)
    }
}

impl TryFrom<&str> for CPF {
    type Error = ParseCPFError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        parse(value)
    }
}

impl TryFrom<[u8; 11]> for CPF {
    type Error = ParseCPFError;

    fn try_from(value: [u8; 11]) -> Result<Self, Self::Error> {
        if valid_digits(&value) {
            Ok(CPF { digits: value })
        } else {
            Err(ParseCPFError::InvalidChecksum)
        }
    }
}

impl fmt::Display for ParseCPFError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseCPFError::InvalidChecksum => "invalid CPF checksum".fmt(f),
            ParseCPFError::InvalidLength => "invalid CPF lenght".fmt(f),
        }
    }
}

#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "std")]
impl std::error::Error for ParseCPFError {}

#[cfg(feature = "rand")]
mod random {
    use super::*;
    use rand::distributions::{Distribution, Standard, Uniform};
    use rand::Rng;

    impl Distribution<CPF> for Standard {
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> CPF {
            let digit = Uniform::from(1..9);
            let mut digits = ArrayVec::<u8, 11>::new();
            for _ in 0..9 {
                digits.push(digit.sample(rng));
            }
            digits.push(check_digit(&digits.as_slice()));
            digits.push(check_digit(&digits.as_slice()));
            CPF {
                digits: digits.into_inner().unwrap(),
            }
        }
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
        assert!(!valid("11111111111"));
        assert!(!valid("22222222222"));
        assert!(!valid("33333333333"));
        assert!(!valid("44444444444"));
        assert!(!valid("55555555555"));
        assert!(!valid("66666666666"));
        assert!(!valid("77777777777"));
        assert!(!valid("88888888888"));
        assert!(!valid("99999999999"));
    }

    #[test]
    fn it_parses() {
        let cpf = parse("38521139039");
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = parse("385.211.390-39");
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = "385.211.390-39".parse::<CPF>();
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
    }

    #[test]
    fn it_initializes_with_digits() {
        let cpf = CPF::try_from([3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = CPF::try_from([4, 4, 7, 2, 1, 8, 4, 9, 8, 1, 9]);
        assert!(cpf.is_err());
    }

    #[test]
    fn it_pads_numbers_with_less_than_eleven_digits() {
        let cpf = parse("5120101").unwrap();
        assert_eq!(cpf.digits(), &[0, 0, 0, 0, 5, 1, 2, 0, 1, 0, 1]);
    }

    #[test]
    fn it_fails_to_parse_numbers_that_dont_match_the_min_length() {
        let cpf = parse("01");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCPFError::InvalidLength);

        let cpf = parse("0");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCPFError::InvalidLength);
    }

    #[test]
    fn it_fails_to_parse_numbers_with_more_than_eleven_digits() {
        let cpf = parse("138521139039");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCPFError::InvalidLength);
    }

    #[test]
    fn it_fails_on_invalid_checksums() {
        let cpf = parse("38521139038");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCPFError::InvalidChecksum);
    }

    #[test]
    fn it_formats() {
        let cpf = parse("38521139039").unwrap();
        assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
    }

    #[test]
    fn it_display() {
        extern crate std;
        let cpf = parse("38521139039").unwrap();
        assert_eq!(std::format!("{}", cpf), "38521139039");
    }

    #[test]
    #[cfg(feature = "rand")]
    fn it_generates_valid_numbers() {
        use rand;
        use rand::Rng;
        let cpf = rand::thread_rng().gen::<CPF>();
        assert!(valid_digits(cpf.digits()));
    }
}
