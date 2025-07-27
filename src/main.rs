use num_bigint::{BigInt, ToBigInt};
use num_traits::{Zero, One};
use rand::Rng;
use sha2::{Sha256, Digest};
use std::fs;
use std::env;
use std::io;
use clap::Parser;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Secret message to encode (overrides environment variable)
    #[arg(short, long)]
    secret: Option<String>,
    
    /// Skip confirmation prompt
    #[arg(short, long)]
    yes: bool,
}

#[derive(Debug, Clone, PartialEq)]
struct EllipticPoint {
    x: BigInt,
    y: BigInt,
    is_infinity: bool,
}

struct EllipticCurve {
    a: BigInt,
    b: BigInt,
    p: BigInt,
}

impl EllipticCurve {
    fn new_secp256k1() -> Self {
        EllipticCurve {
            a: BigInt::zero(),
            b: 7.to_bigint().unwrap(),
            p: "115792089237316195423570985008687907853269984665640564039457584007913129639747".parse().unwrap(),
        }
    }

    fn point_add(&self, p1: &EllipticPoint, p2: &EllipticPoint) -> EllipticPoint {
        if p1.is_infinity {
            return p2.clone();
        }
        if p2.is_infinity {
            return p1.clone();
        }

        if p1.x == p2.x {
            if p1.y == p2.y {
                return self.point_double(p1);
            } else {
                return EllipticPoint { x: BigInt::zero(), y: BigInt::zero(), is_infinity: true };
            }
        }

        let dx = (&p2.x - &p1.x) % &self.p;
        let dy = (&p2.y - &p1.y) % &self.p;
        let dx_inv = self.mod_inverse(&dx);
        let slope = (&dy * &dx_inv) % &self.p;

        let x3 = (&slope * &slope - &p1.x - &p2.x) % &self.p;
        let y3 = (&slope * (&p1.x - &x3) - &p1.y) % &self.p;

        EllipticPoint {
            x: if x3 < BigInt::zero() { x3 + &self.p } else { x3 },
            y: if y3 < BigInt::zero() { y3 + &self.p } else { y3 },
            is_infinity: false,
        }
    }

    fn point_double(&self, point: &EllipticPoint) -> EllipticPoint {
        if point.is_infinity {
            return point.clone();
        }

        let numerator = (3.to_bigint().unwrap() * &point.x * &point.x + &self.a) % &self.p;
        let denominator = (2.to_bigint().unwrap() * &point.y) % &self.p;
        let slope = (&numerator * &self.mod_inverse(&denominator)) % &self.p;

        let x3 = (&slope * &slope - 2.to_bigint().unwrap() * &point.x) % &self.p;
        let y3 = (&slope * (&point.x - &x3) - &point.y) % &self.p;

        EllipticPoint {
            x: if x3 < BigInt::zero() { x3 + &self.p } else { x3 },
            y: if y3 < BigInt::zero() { y3 + &self.p } else { y3 },
            is_infinity: false,
        }
    }

    fn scalar_multiply(&self, k: &BigInt, point: &EllipticPoint) -> EllipticPoint {
        if k == &BigInt::zero() || point.is_infinity {
            return EllipticPoint { x: BigInt::zero(), y: BigInt::zero(), is_infinity: true };
        }

        let mut result = EllipticPoint { x: BigInt::zero(), y: BigInt::zero(), is_infinity: true };
        let mut addend = point.clone();
        let mut k_copy = k.clone();

        while k_copy > BigInt::zero() {
            if &k_copy % 2.to_bigint().unwrap() == BigInt::one() {
                result = self.point_add(&result, &addend);
            }
            addend = self.point_double(&addend);
            k_copy = k_copy / 2.to_bigint().unwrap();
        }

        result
    }

    fn mod_inverse(&self, a: &BigInt) -> BigInt {
        let mut t = BigInt::zero();
        let mut new_t = BigInt::one();
        let mut r = self.p.clone();
        let mut new_r = a.clone();

        while new_r != BigInt::zero() {
            let quotient = &r / &new_r;
            let temp_t = t.clone();
            t = new_t.clone();
            new_t = temp_t - &quotient * &new_t;
            
            let temp_r = r.clone();
            r = new_r.clone();
            new_r = temp_r - quotient * new_r;
        }

        if t < BigInt::zero() {
            t + &self.p
        } else {
            t
        }
    }
}

struct AdvancedCipher {
    curve: EllipticCurve,
    generator: EllipticPoint,
    prime_field: BigInt,
}

impl AdvancedCipher {
    fn new() -> Self {
        let curve = EllipticCurve::new_secp256k1();
        let generator = EllipticPoint {
            x: "55066263022277343669578718895168534326250603453777594175500187360389116729240".parse().unwrap(),
            y: "32670510020758816978083085130507043184471273380659243275938904335757337482424".parse().unwrap(),
            is_infinity: false,
        };
        let prime_field = "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151".parse().unwrap();

        AdvancedCipher {
            curve,
            generator,
            prime_field,
        }
    }

    fn char_to_curve_point(&self, c: char) -> EllipticPoint {
        let char_val = c as u32;
        let seed = BigInt::from(char_val) * 1000000.to_bigint().unwrap() + 314159.to_bigint().unwrap();
        self.curve.scalar_multiply(&seed, &self.generator)
    }

    fn apply_carmichael_lambda(&self, n: &BigInt) -> BigInt {
        let factors = self.find_prime_factors(n);
        let mut lcm = BigInt::one();
        
        for prime in factors {
            let lambda_p = &prime - BigInt::one();
            lcm = self.lcm(&lcm, &lambda_p);
        }
        lcm
    }

    fn find_prime_factors(&self, n: &BigInt) -> Vec<BigInt> {
        let mut factors = Vec::new();
        let mut num = n.clone();
        let mut i = 2.to_bigint().unwrap();

        while &i * &i <= num {
            while &num % &i == BigInt::zero() {
                factors.push(i.clone());
                num = num / &i;
            }
            i = i + BigInt::one();
        }
        
        if num > BigInt::one() {
            factors.push(num);
        }
        factors
    }

    fn lcm(&self, a: &BigInt, b: &BigInt) -> BigInt {
        (a * b) / self.gcd(a, b)
    }

    fn gcd(&self, a: &BigInt, b: &BigInt) -> BigInt {
        if b == &BigInt::zero() {
            a.clone()
        } else {
            self.gcd(b, &(a % b))
        }
    }

    fn chinese_remainder_theorem(&self, remainders: &[BigInt], moduli: &[BigInt]) -> BigInt {
        let product: BigInt = moduli.iter().fold(BigInt::one(), |acc, m| acc * m);
        let mut result = BigInt::zero();

        for i in 0..remainders.len() {
            let partial_product = &product / &moduli[i];
            let inverse = self.extended_euclidean(&partial_product, &moduli[i]).0;
            result = (result + &remainders[i] * &partial_product * inverse) % &product;
        }

        result
    }

    fn extended_euclidean(&self, a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
        if b == &BigInt::zero() {
            return (BigInt::one(), BigInt::zero(), a.clone());
        }

        let (x1, y1, gcd) = self.extended_euclidean(b, &(a % b));
        let x = y1.clone();
        let y = x1 - (a / b) * y1;

        (x, y, gcd)
    }

    fn fermat_little_theorem_transform(&self, base: &BigInt, message_chunk: &BigInt) -> BigInt {
        let prime = "170141183460469231731687303715884105727".parse::<BigInt>().unwrap();
        let exponent = message_chunk % (&prime - BigInt::one());
        self.mod_pow(base, &exponent, &prime)
    }

    fn mod_pow(&self, base: &BigInt, exp: &BigInt, modulus: &BigInt) -> BigInt {
        let mut result = BigInt::one();
        let mut base = base % modulus;
        let mut exp = exp.clone();

        while exp > BigInt::zero() {
            if &exp % 2.to_bigint().unwrap() == BigInt::one() {
                result = (&result * &base) % modulus;
            }
            exp = exp / 2.to_bigint().unwrap();
            base = (&base * &base) % modulus;
        }

        result
    }

    fn legendre_symbol(&self, a: &BigInt, p: &BigInt) -> i32 {
        let result = self.mod_pow(a, &((p - BigInt::one()) / 2.to_bigint().unwrap()), p);
        if result == BigInt::zero() {
            0
        } else if result == BigInt::one() {
            1
        } else {
            -1
        }
    }

    fn quadratic_residue_encoding(&self, char_val: u32) -> BigInt {
        let prime = "1009".parse::<BigInt>().unwrap();
        let mut candidate = BigInt::from(char_val);
        
        while self.legendre_symbol(&candidate, &prime) != 1 {
            candidate = candidate + BigInt::one();
        }
        
        candidate
    }

    fn encode_message(&self, message: &str) -> Vec<BigInt> {
        let mut encoded = Vec::new();
        let mut rng = rand::thread_rng();

        for (i, c) in message.chars().enumerate() {
            let curve_point = self.char_to_curve_point(c);
            let char_as_bigint = BigInt::from(c as u32);
            
            let carmichael_result = self.apply_carmichael_lambda(&char_as_bigint);
            let qr_encoded = self.quadratic_residue_encoding(c as u32);
            let fermat_transformed = self.fermat_little_theorem_transform(&char_as_bigint, &BigInt::from(i + 1));
            
            let remainders = vec![
                curve_point.x % 97.to_bigint().unwrap(),
                carmichael_result % 101.to_bigint().unwrap(),
                qr_encoded % 103.to_bigint().unwrap(),
            ];
            
            let moduli = vec![
                97.to_bigint().unwrap(),
                101.to_bigint().unwrap(),
                103.to_bigint().unwrap(),
            ];
            
            let crt_result = self.chinese_remainder_theorem(&remainders, &moduli);
            let final_encoded = (crt_result * fermat_transformed) % &self.prime_field;
            
            let noise = rng.gen_range(1000..9999);
            let noisy_result = final_encoded + BigInt::from(noise) * &self.prime_field;
            
            encoded.push(noisy_result);
        }

        encoded
    }

    fn generate_mathematical_ascii_art(&self, encoded_data: &[BigInt]) -> String {
        let mut art = String::new();
        let width = 80;
        let height = 25;

        art.push_str("╔════════════════════════════════════════════════════════════════════════════╗\n");
        art.push_str("║                    MATHEMATICAL TRANSFORMATION MATRIX                     ║\n");
        art.push_str("╠════════════════════════════════════════════════════════════════════════════╣\n");

        for row in 0..height {
            art.push('║');
            for col in 0..width-2 {
                let index = (row * (width-2) + col) % encoded_data.len();
                let value = &encoded_data[index];
                let char_selector = (value % 94.to_bigint().unwrap()).to_string().parse::<u32>().unwrap_or(0) + 33;
                
                if char_selector == 32 || char_selector > 126 {
                    art.push('·');
                } else {
                    art.push(char::from(char_selector as u8));
                }
            }
            art.push('║');
            art.push('\n');
        }

        art.push_str("╠════════════════════════════════════════════════════════════════════════════╣\n");
        art.push_str("║ Hidden sequences follow Fibonacci mod p, where p = 2^521 - 1              ║\n");
        art.push_str("║ Elliptic curve discrete logarithm: y² ≡ x³ + 7 (mod secp256k1_prime)     ║\n");
        art.push_str("║ Each symbol encodes: CRT(EC_point.x mod 97, λ(n) mod 101, QR(c) mod 103)  ║\n");
        art.push_str("╚════════════════════════════════════════════════════════════════════════════╝\n");

        art
    }

    fn generate_visual_mathematical_clues(&self) -> String {
        let mut clues = String::new();
        
        clues.push_str("MATHEMATICAL SEQUENCE ANALYSIS REQUIRED\n");
        clues.push_str("=======================================\n\n");
        
        clues.push_str("Sequence A (Elliptic Curve Points on secp256k1):\n");
        for i in 1..=10 {
            let point = self.curve.scalar_multiply(&BigInt::from(i * 314159), &self.generator);
            clues.push_str(&format!("P{}: ({}, {})\n", i, 
                point.x.to_string().chars().take(16).collect::<String>(),
                point.y.to_string().chars().take(16).collect::<String>()));
        }
        
        clues.push_str("\nSequence B (Carmichael Lambda Values):\n");
        let carmichael_inputs = vec![15, 21, 35, 77, 143, 221, 323, 437, 667, 899];
        for (i, val) in carmichael_inputs.iter().enumerate() {
            let lambda = self.apply_carmichael_lambda(&BigInt::from(*val));
            clues.push_str(&format!("λ({}): {}\n", val, lambda));
        }
        
        clues.push_str("\nSequence C (Quadratic Residues mod 1009):\n");
        for i in 65..=74 {
            let qr = self.quadratic_residue_encoding(i);
            clues.push_str(&format!("QR({}): {}\n", i as u8 as char, qr));
        }
        
        clues.push_str("\nFermat Transform Pattern (base^exp mod p):\n");
        clues.push_str("Base: char_value, Exp: position+1, Mod: 170141183460469231731687303715884105727\n");
        
        clues.push_str("\nChinese Remainder Theorem Setup:\n");
        clues.push_str("Moduli: [97, 101, 103]\n");
        clues.push_str("Remainders: [EC_x mod 97, λ(char) mod 101, QR(char) mod 103]\n");
        
        clues.push_str("\nPrime Field Operations:\n");
        clues.push_str("Final encoding: (CRT_result * Fermat_transform) mod Mersenne_Prime\n");
        clues.push_str("Mersenne Prime: 2^521 - 1\n");
        
        clues.push_str("\nHidden Message Location:\n");
        clues.push_str("The secret lies where Euler's totient meets elliptic dreams,\n");
        clues.push_str("In fields of prime residues and modular schemes.\n");
        clues.push_str("Reverse the transforms, unwind the mathematical maze,\n");
        clues.push_str("To find the theorem that ends your days.\n");

        clues
    }

    fn create_solution_verification(&self, solution: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(solution.as_bytes());
        let hash_result = hasher.finalize();
        
        let verification_hash = hex::encode(hash_result);
        
        format!(
            "SOLUTION VERIFICATION SYSTEM\n\
            ============================\n\n\
            To verify your solution is correct, compute SHA256 of your answer.\n\
            The correct solution hash starts with: {}\n\n\
            Your solution should be a famous quote from cryptographic literature.\n\
            Format: Submit the exact text with proper capitalization and spacing.\n\n\
            Example: If answer is 'Hello World', submit: Hello World\n\n\
            Verification Hash Pattern: {}...\n\
            Full verification requires matching the complete 64-character hash.\n\n\
            Cryptographic Hint: The solution is a fundamental principle about privacy\n\
            from Eric Hughes' Cypherpunk Manifesto, emphasizing the necessity of\n\
            privacy for maintaining democratic society.\n",
            &verification_hash[..8],
            &verification_hash[..16]
        )
    }
}

fn get_secret_message(args: &Args) -> Result<String, String> {
    // Priority: CLI arg > environment variable > .env file > error
    if let Some(secret) = &args.secret {
        return Ok(secret.clone());
    }
    
    // Try to load from .env file
    if let Err(_) = dotenv::dotenv() {
        // .env file not found, that's okay
    }
    
    if let Ok(secret) = env::var("SECRET_MESSAGE") {
        if !secret.trim().is_empty() {
            return Ok(secret);
        }
    }
    
    Err("No secret message provided. Use one of the following methods:\n\
         1. Command line: cargo run -- --secret \"Your message here\"\n\
         2. Environment variable: export SECRET_MESSAGE=\"Your message here\"\n\
         3. .env file: echo 'SECRET_MESSAGE=\"Your message here\"' > .env".to_string())
}

fn main() {
    let args = Args::parse();
    
    println!("Mathematical Cipher Generator");
    println!("============================\n");

    let secret_message = match get_secret_message(&args) {
        Ok(message) => message,
        Err(error) => {
            eprintln!("Error: {}", error);
            std::process::exit(1);
        }
    };
    
    // Security confirmation (unless --yes flag is used)
    if !args.yes {
        println!("Secret message: \"{}\"", secret_message);
        println!("Message length: {} characters", secret_message.len());
        
        let mut hasher = Sha256::new();
        hasher.update(secret_message.as_bytes());
        let hash = hex::encode(hasher.finalize());
        println!("SHA256 hash: {}", hash);
        println!("Hash prefix: {}", &hash[..8]);
        
        println!("\nDo you want to proceed with encoding this message? (y/N): ");
        let mut input = String::new();
        io::stdin().read_line(&mut input).expect("Failed to read input");
        
        if !input.trim().to_lowercase().starts_with('y') {
            println!("Aborted.");
            std::process::exit(0);
        }
    }

    let cipher = AdvancedCipher::new();
    let encoded_data = cipher.encode_message(&secret_message);
    
    let challenge_instructions = format!(
        "CRYPTOGRAPHIC CHALLENGE: THE MATHEMATICAL LABYRINTH\n\
        ====================================================\n\n\
        Welcome to an advanced cipher challenge that combines multiple layers of mathematics\n\
        and cryptography to conceal a famous mathematical theorem.\n\n\
        MATHEMATICAL TECHNIQUES EMPLOYED:\n\
        1. Elliptic Curve Cryptography (secp256k1)\n\
        2. Modular Arithmetic in Prime Fields\n\
        3. Carmichael Lambda Function\n\
        4. Chinese Remainder Theorem\n\
        5. Quadratic Residue Theory\n\
        6. Fermat's Little Theorem\n\
        7. Steganographic Encoding\n\n\
        SOLUTION REQUIREMENTS:\n\
        - Understanding of advanced number theory\n\
        - Implementation of mathematical algorithms\n\
        - Systematic reverse engineering approach\n\
        - Pattern recognition and analysis\n\n\
        FILES PROVIDED:\n\
        - cipher_data.txt: The encoded message\n\
        - visual_clues.txt: Mathematical sequences and patterns\n\
        - solution_verification.txt: Hash verification system\n\n\
        CHALLENGE RULES:\n\
        1. Mathematical reasoning required\n\
        2. All algorithms are open source\n\
        3. No computational attacks\n\
        4. Single correct solution exists\n\n\
        This challenge demonstrates the intersection of pure mathematics\n\
        and applied cryptography in an educational context.\n"
    );

    let cipher_data = format!(
        "ENCODED MESSAGE DATA\n\
        ===================\n\n\
        Each line represents one character encoded through multiple mathematical transformations:\n\n{}",
        encoded_data.iter()
            .enumerate()
            .map(|(i, val)| format!("{}:{}", i+1, val))
            .collect::<Vec<_>>()
            .join("\n")
    );

    let ascii_art = cipher.generate_mathematical_ascii_art(&encoded_data);
    let visual_clues = cipher.generate_visual_mathematical_clues();
    let verification = cipher.create_solution_verification(&secret_message);

    if let Err(e) = fs::write("challenge.txt", challenge_instructions) {
        eprintln!("Error creating challenge.txt: {}", e);
    }

    if let Err(e) = fs::write("cipher_data.txt", cipher_data) {
        eprintln!("Error creating cipher_data.txt: {}", e);
    }

    if let Err(e) = fs::write("visual_clues.txt", format!("{}\n\n{}", ascii_art, visual_clues)) {
        eprintln!("Error creating visual_clues.txt: {}", e);
    }

    if let Err(e) = fs::write("solution_verification.txt", verification) {
        eprintln!("Error creating solution_verification.txt: {}", e);
    }

    println!("Cipher generation complete.");
    println!("Challenge files have been created.");
}
