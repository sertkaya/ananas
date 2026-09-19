use std::fs::File;
use crate::af::AF;
use std::io::BufReader;
use std::io::BufRead;

/// Parse an argumentation framework from a file in the `p af <n>` format:
/// the first line declares the argument count, and each following
/// whitespace-separated `attacker victim` pair (1-indexed) adds an attack.
/// Lines starting with `#`, and empty lines, are skipped.
pub fn read_af(f: File) -> AF {
    let mut reader = BufReader::new(f);

    // Read the first line and parse
    let mut first_line = String::new();
    reader.read_line(&mut first_line).expect("Failed to read first line");
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    if parts.len() != 3 || parts[0] != "p" || parts[1] != "af" {
        panic!("Invalid header line, expected 'p af <n>'");
    }
    let arg_count: usize = parts[2].parse().expect("Argument count is not a number");

    // Create an empty AF
    let mut af = AF::new(arg_count);

    // Read the attacks
    for (ln, line) in reader.lines().enumerate() {
        let line = line.unwrap();
        // Skip comments
        if line.starts_with('#') {
            continue;
        }
        // Skip empty lines
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() != 2 {
            panic!("Syntax error in line {}", ln + 2);
        }
        let attacker:  usize = parts[0].parse().expect("Attacker is not a number");
        let victim:  usize = parts[1].parse().expect("Victim is not a number");
        if attacker == 0 || victim == 0 {
            panic!("Argument ids must be >= 1 in line {}", ln + 2);
        }
        af.add_attack(attacker - 1, victim - 1);
    }
    af
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_af() -> std::io::Result<()> {
        let input_af = File::open("tests/jelia23-example.af")?;
        let af = read_af(input_af);
        assert_eq!(af.argument_count(), 5);
        assert_eq!(af.attack_count(), 8);
        Ok(())
        // assert_eq!(result, 4);
    }

    #[test]
    #[should_panic(expected = "Argument ids must be >= 1")]
    fn test_read_af_zero_argument_id() {
        let input_af = File::open("tests/zero-id.af").unwrap();
        read_af(input_af);
    }

    #[test]
    #[should_panic(expected = "Invalid header line")]
    fn test_read_af_invalid_header() {
        let input_af = File::open("tests/invalid-header.af").unwrap();
        read_af(input_af);
    }
}