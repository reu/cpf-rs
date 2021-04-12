#![no_std]

use arrayvec::{ArrayString, ArrayVec};
use core::char::from_digit;
use core::convert::TryFrom;
use core::fmt;
use core::str::FromStr;

#[cfg(feature = "rand")]
use rand::distributions::{Distribution, Standard, Uniform};
#[cfg(feature = "rand")]
use rand::Rng;

static BLACK_LIST: &'static [[u8; 11]] = &[
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
    [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
    [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8],
    [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
];

/// Validates the given CPF number.
/// ```
/// use cpf;
///
/// assert!(cpf::valid("385.211.390-39"));
/// assert!(!cpf::valid("385.211.390-49"));
/// ```
pub fn valid<T: AsRef<str>>(cpf: T) -> bool {
    parse(cpf).is_ok()
}

/// Parses a CPF number.
/// ```
/// use cpf;
///
/// assert!(cpf::parse("385.211.390-39").is_ok());
/// assert!(cpf::parse("385.211.390-49").is_err());
/// ```
pub fn parse<T: AsRef<str>>(cpf: T) -> Result<CPF, ParseCPFError> {
    let cpf = cpf.as_ref();

    let digits_count = cpf.chars().filter(|c| c.is_numeric()).count();

    if digits_count < 3 || digits_count > 11 {
        return Err(ParseCPFError::InvalidLength);
    }

    let mut digits = cpf
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .collect::<ArrayVec<u8, 11>>();

    for i in 0..digits.remaining_capacity() {
        digits.insert(i, 0);
    }

    let cpf = CPF {
        digits: digits.into_inner().unwrap(),
    };

    if cpf.valid() {
        Ok(cpf)
    } else {
        Err(ParseCPFError::InvalidChecksum)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum ParseCPFError {
    InvalidLength,
    InvalidChecksum,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CPF {
    digits: [u8; 11],
}

impl CPF {
    pub fn digits(&self) -> &[u8; 11] {
        &self.digits
    }

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

    pub fn check_digits(&self) -> (&u8, &u8) {
        (&self.digits[9], &self.digits[10])
    }

    fn valid(&self) -> bool {
        if BLACK_LIST.contains(self.digits()) {
            return false;
        }

        let check_digit1 = check_digit(&self.digits[0..9]);
        let check_digit2 = check_digit(&self.digits[0..10]);

        self.check_digits() == (&check_digit1, &check_digit2)
    }
}

fn check_digit(digits: &[u8]) -> u8 {
    let check_sum = digits
        .iter()
        .rev()
        .enumerate()
        .map(|(i, n)| (i + 2) * (*n as usize))
        .sum::<usize>();

    match check_sum % 11 {
        n if n < 2 => 0,
        n => 11 - n as u8,
    }
}

impl fmt::Display for CPF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for c in self.formatted().chars() {
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
        let cpf = CPF { digits: value };
        if cpf.valid() {
            Ok(cpf)
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

#[cfg(feature = "rand")]
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
    #[cfg(feature = "rand")]
    fn it_generates_valid_numbers() {
        use rand;
        let mut rng = rand::thread_rng();
        assert!(valid(rand::thread_rng().gen::<CPF>().formatted()));
    }
}
