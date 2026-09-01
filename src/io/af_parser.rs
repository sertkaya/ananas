use std::fs::File;
use crate::af::AF;
use std::io::BufReader;
use std::io::BufRead;

pub fn read_af(f: File) -> AF {
    let mut reader = BufReader::new(f);

    // Read the first line and parse
    let mut first_line = String::new();
    reader.read_line(&mut first_line).expect("Failed to read first line");
    let parts: Vec<&str> = first_line.split_whitespace().collect();
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
}