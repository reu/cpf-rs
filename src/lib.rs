#![no_std]

//! # CPF
//!
//! Brazilian CPF parsing, validating and formatting library.
//!
//! ```rust
//! # fn main() -> Result<(), cpf::ParseCpfError> {
//! use cpf::Cpf;
//!
//! // Use the `valid` function if all you need is validating a CPF number
//! assert!(cpf::valid("38521139039"));
//! assert!(!cpf::valid("38521139030"));
//!
//! // Parse into a Cpf struct if you need formatting and other metadata
//! let cpf: Cpf = "38521139039".parse()?;
//!
//! assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
//! assert_eq!(cpf.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
//!
//! // Note that the Cpf struct is guaranteed to always be valid
//! assert!("38521139030".parse::<Cpf>().is_err());
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
//! use cpf::Cpf;
//! use rand;
//! use rand::Rng;
//!
//! let cpf: Cpf = rand::thread_rng().gen();
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
/// use core::convert::TryFrom;
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
    ///
    /// assert_eq!(cpf.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn digits(&self) -> &[u8; 11] {
        &self.digits
    }

    /// Formats a Cpf number.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCpfError> {
    /// use cpf::Cpf;
    ///
    /// let cpf: Cpf = "38521139039".parse()?;
    ///
    /// assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note that numbers with less than 11 digits will be padded by zeros.
    /// ```rust
    /// # fn main() -> Result<(), cpf::ParseCpfError> {
    /// # use cpf::Cpf;
    /// let cpf: Cpf = "5120101".parse()?;
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

fn parse<T: AsRef<str>>(cpf: T) -> Result<Cpf, ParseCpfError> {
    let cpf = cpf.as_ref();

    let mut digits = ArrayVec::<u8, 11>::new();

    for (i, digit) in cpf
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .enumerate()
    {
        if i == 11 {
            return Err(ParseCpfError::InvalidLength);
        } else {
            digits.push(digit);
        }
    }

    if digits.len() < 3 {
        return Err(ParseCpfError::InvalidLength);
    }

    for i in 0..digits.remaining_capacity() {
        digits.insert(i, 0);
    }

    let digits = digits.into_inner().unwrap();

    if valid_digits(&digits) {
        Ok(Cpf { digits })
    } else {
        Err(ParseCpfError::InvalidChecksum)
    }
}

impl fmt::Display for Cpf {
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
        if valid_digits(&value) {
            Ok(Cpf { digits: value })
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
mod random {
    use super::*;
    use rand::distributions::{Distribution, Standard, Uniform};
    use rand::Rng;

    impl Distribution<Cpf> for Standard {
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Cpf {
            let digit = Uniform::from(1..9);
            let mut digits = ArrayVec::<u8, 11>::new();
            for _ in 0..9 {
                digits.push(digit.sample(rng));
            }
            digits.push(check_digit(&digits.as_slice()));
            digits.push(check_digit(&digits.as_slice()));
            Cpf {
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

        let cpf = "385.211.390-39".parse::<Cpf>();
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
    }

    #[test]
    fn it_initializes_with_digits() {
        let cpf = Cpf::try_from([3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
        assert!(cpf.is_ok());
        assert_eq!(cpf.unwrap().digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

        let cpf = Cpf::try_from([4, 4, 7, 2, 1, 8, 4, 9, 8, 1, 9]);
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
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidLength);

        let cpf = parse("0");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidLength);
    }

    #[test]
    fn it_fails_to_parse_numbers_with_more_than_eleven_digits() {
        let cpf = parse("138521139039");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidLength);
    }

    #[test]
    fn it_fails_on_invalid_checksums() {
        let cpf = parse("38521139038");
        assert!(cpf.is_err());
        assert_eq!(cpf.unwrap_err(), ParseCpfError::InvalidChecksum);
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
        for _ in 1..10000 {
            let cpf = rand::thread_rng().gen::<Cpf>();
            assert!(valid_digits(cpf.digits()));
        }
    }
}
