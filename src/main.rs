use crypto_bigint::{
    modular::{MontyForm, MontyParams},
    U256, U512, Odd, NonZero, CheckedMul, RandomMod,
};
use crypto_primes::{generate_safe_prime, is_safe_prime, is_prime};
use rand::rngs::OsRng;
use std::collections::HashMap;

struct BraavosAccumulator {
    sk: U256,        // p'q' = (p-1)/2 * (q-1)/2
    n: Odd<U512>,    // RSA modulus as an Odd type
    a: MontyForm<8>, // Current accumulator value in Montgomery form
    prf_key: U256,   // PRF key for element generation
    element_cache: HashMap<Vec<u8>, U256>, // Cache for x -> prime mapping
    monty_params: MontyParams<8>, // Montgomery parameters for modular arithmetic
}

impl BraavosAccumulator {
    fn new(prime_bits: u32) -> Result<Self, &'static str> {
        // Generate safe primes using crypto-primes
        let p = generate_safe_prime::<U256>(prime_bits);
        let q = generate_safe_prime::<U256>(prime_bits);

        // Ensure the primes are safe
        assert!(is_safe_prime(&p));
        assert!(is_safe_prime(&q));

        // Calculate p' and q' where p = 2p' + 1 and q = 2q' + 1
        let divisor = NonZero::new(U256::from(2u32)).unwrap();
        let p_prime = (p - U256::ONE).wrapping_div(&divisor);
        let q_prime = (q - U256::ONE).wrapping_div(&divisor);

        // Verify that p' and q' are also prime
        if !is_prime(&p_prime) || !is_prime(&q_prime) {
            return Err("Generated safe primes have non-prime p' and q'");
        }

        // Additional verification: ensure p' and q' are actually the Sophie Germain primes
        // that correspond to p and q being safe primes
        let p_check = p_prime.checked_mul(&U256::from(2u32)).unwrap() + U256::ONE;
        let q_check = q_prime.checked_mul(&U256::from(2u32)).unwrap() + U256::ONE;
        
        if p_check != p || q_check != q {
            return Err("Generated primes are not proper safe primes");
        }

        // Convert U256 primes to U512 with proper padding
        let p_512 = pad_u256_to_u512(p);
        let q_512 = pad_u256_to_u512(q);

        let n = p_512.checked_mul(&q_512).unwrap();
        let n_odd = Odd::new(n).expect("RSA modulus must be odd");

        let sk = p_prime.checked_mul(&q_prime).unwrap();

        // Initialize Montgomery parameters
        let monty_params = MontyParams::new(n_odd);

        // Select random a' from Z*n and set a = (a')^2 mod n
        let a_prime = U512::random_mod(&mut OsRng, &NonZero::new(n).unwrap());
        let a_prime_monty = MontyForm::new(&a_prime, monty_params);
        let a = a_prime_monty.mul(&a_prime_monty);

        // Generate random PRF key
        let prf_key = U256::random_mod(&mut OsRng, &NonZero::new(U256::MAX).unwrap());

        Ok(Self {
            sk,
            n: n_odd,
            a,
            prf_key,
            element_cache: HashMap::new(),
            monty_params,
        })
    }

    fn get_or_generate_element(&mut self, x: &[u8]) -> U256 {
        if let Some(&prime) = self.element_cache.get(x) {
            return prime;
        }
        let mut seed = Vec::with_capacity(x.len() + 32);
        seed.extend_from_slice(x);
        seed.extend_from_slice(&self.prf_key.to_be_bytes());
        let prime = generate_safe_prime::<U256>(256);
        self.element_cache.insert(x.to_vec(), prime);
        prime
    }

    fn add(&mut self, x: &[u8]) -> Result<U512, &'static str> {
        let elem = self.get_or_generate_element(x);
        let elem_inv = if elem.inv_mod(&self.sk).is_some().into() {
            elem.inv_mod(&self.sk).unwrap()
        } else {
            return Err("Element not invertible modulo sk");
        };
        let elem_inv_512 = pad_u256_to_u512(elem_inv);
        let w_monty = self.mont_mod_exp(self.a, &elem_inv_512);
        let w = w_monty.retrieve();
        Ok(w % *self.n.as_ref())
    }

    fn delete(&mut self, x: &[u8]) -> Result<(), &'static str> {
        // Step 1: Check that x is an odd prime (already done in get_or_generate_element)
        let elem = self.get_or_generate_element(x);
        
        // Step 2: Let a = a^(x^-1 mod sk)
        let elem_inv = if elem.inv_mod(&self.sk).is_some().into() {
            elem.inv_mod(&self.sk).unwrap()
        } else {
            return Err("Element not invertible modulo sk");
        };
        let elem_inv_512 = pad_u256_to_u512(elem_inv);
        let new_a = self.mont_mod_exp(self.a, &elem_inv_512);
        
        // Step 3 & 4: Update accumulator and return
        self.a = MontyForm::new(&(new_a.retrieve() % *self.n.as_ref()), self.monty_params);
        Ok(())
    }

    fn verify(&mut self, x: &[u8], w: U512) -> bool {
        let elem = self.get_or_generate_element(x);
        let elem_512 = pad_u256_to_u512(elem);
        let w_reduced = w % *self.n.as_ref();
        let w_monty = MontyForm::new(&w_reduced, self.monty_params);
        let computed_a = self.mont_mod_exp(w_monty, &elem_512);
        let computed_a_reduced = computed_a.retrieve() % *self.n.as_ref();
        let current_a_reduced = self.a.retrieve() % *self.n.as_ref();
        println!("Verification debug:");
        println!("w^x = {:?}", computed_a_reduced);
        println!("a = {:?}", current_a_reduced);
        computed_a_reduced == current_a_reduced
    }

    fn mont_mod_exp(&self, base: MontyForm<8>, exponent: &U512) -> MontyForm<8> {
        let mut result = MontyForm::new(&U512::ONE, self.monty_params);
        let base_power = base;
        
        // Process exponent in chunks of 64 bits
        for i in (0..512).rev() {
            // Square step
            result = result.mul(&result);
            
            // Multiply step (if bit is set)
            if (exponent.as_words()[i / 64] >> (i % 64)) & 1 == 1 {
                result = result.mul(&base_power);
            }
            
            // Every 64 bits, reduce the intermediate result
            if i % 64 == 0 {
                let temp = result.retrieve() % *self.n.as_ref();
                result = MontyForm::new(&temp, self.monty_params);
            }
        }
        
        result
    }

    fn update_witness_on_deletion(&mut self, x: &[u8], w: U512, y: &[u8]) -> Result<U512, &'static str> {
        let elem_x = self.get_or_generate_element(x);
        let elem_y = self.get_or_generate_element(y);
        let n = *self.n.as_ref();
        let p_prime_q_prime = self.sk; // This is p'q' = (p-1)/2 * (q-1)/2
        
        // Convert to Montgomery form for calculations
        let w_monty = MontyForm::new(&w, self.monty_params);
        let a_monty = self.a;
        
        // Find y^(-1) mod p'q'
        let y_inv = elem_y.inv_mod(&p_prime_q_prime);
        if !bool::from(y_inv.is_some()) {
            return Err("y is not invertible modulo p'q'");
        }
        let y_inv = y_inv.unwrap();
        
        // Debug output
        println!("Witness update verification:");
        println!("Original witness = {:?}", w);
        println!("Current accumulator = {:?}", self.a.retrieve());
        println!("Element x = {:?}", elem_x);
        println!("Element y = {:?}", elem_y);
        println!("y^(-1) mod p'q' = {:?}", y_inv);
        
        // Calculate w^(1/y) mod n
        // This is equivalent to w^(y^(-1) mod p'q') mod n
        let y_inv_512 = pad_u256_to_u512(y_inv);
        let result = self.mont_mod_exp(w_monty, &y_inv_512);
        let result = result.retrieve() % n;
        
        println!("Final result = {:?}", result);
        
        // Verify that result^y = w mod n
        let result_monty = MontyForm::new(&result, self.monty_params);
        let y_512 = pad_u256_to_u512(elem_y);
        let result_y = self.mont_mod_exp(result_monty, &y_512);
        println!("Verification that result^y = w:");
        println!("result^y = {:?}", result_y.retrieve());
        println!("w = {:?}", w);
        
        // Verify that result^x = a mod n
        let x_512 = pad_u256_to_u512(elem_x);
        let result_x = self.mont_mod_exp(result_monty, &x_512);
        println!("Verification that result^x = a:");
        println!("result^x = {:?}", result_x.retrieve());
        println!("a = {:?}", self.a.retrieve());
        
        Ok(result)
    }
}

fn pad_u256_to_u512(value: U256) -> U512 {
    let mut bytes = [0u8; 64];
    let value_bytes = value.to_be_bytes();
    bytes[32..].copy_from_slice(&value_bytes);
    U512::from_be_slice(&bytes)
}

fn main() {
    println!("Initializing BraavosAccumulator...");
    let mut acc = BraavosAccumulator::new(64).expect("Failed to create accumulator");
    println!("Accumulator initialized successfully!");

    // Test case 1: Basic add, delete, verify
    println!("\n=== Test Case 1: Basic Operations ===");
    let x = b"element_x";
    let y = b"element_y";

    println!("Initial accumulator value: {:?}", acc.a.retrieve());

    println!("Adding element x...");
    let w_x = acc.add(x).expect("Failed to add element x");
    println!("Witness for x: {:?}", w_x);
    println!("Accumulator after adding x: {:?}", acc.a.retrieve());

    println!("Verifying element x...");
    assert!(acc.verify(x, w_x), "Verification for x failed");
    println!("Element x verified successfully!");

    println!("Adding element y...");
    let w_y = acc.add(y).expect("Failed to add element y");
    println!("Witness for y: {:?}", w_y);
    println!("Accumulator after adding y: {:?}", acc.a.retrieve());

    println!("Deleting element y...");
    acc.delete(y).expect("Failed to delete element y");
    println!("Accumulator after deleting y: {:?}", acc.a.retrieve());
    println!("Element y deleted successfully!");

    println!("Updating witness for x...");
    let mut updated_witness = acc.update_witness_on_deletion(x, w_x, y)
        .expect("Failed to update witness");
    println!("Updated witness: {:?}", updated_witness);

    println!("Verifying element x with updated witness...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    println!("Element x verified successfully!");

    // Test case 2: Multiple elements
    println!("\n=== Test Case 2: Multiple Elements ===");
    let z = b"element_z";
    let d = b"element_d";
    let e = b"element_e";

    println!("Adding elements z, d, and e...");
    let w_z = acc.add(z).expect("Failed to add element z");
    let w_d = acc.add(d).expect("Failed to add element d");
    let w_e = acc.add(e).expect("Failed to add element e");
    println!("Accumulator after adding z, d, and e: {:?}", acc.a.retrieve());

    println!("Verifying all elements...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    assert!(acc.verify(z, w_z), "Verification for z failed");
    assert!(acc.verify(d, w_d), "Verification for d failed");
    assert!(acc.verify(e, w_e), "Verification for e failed");
    println!("All elements verified successfully!");

    // Test case 3: Delete middle element
    println!("\n=== Test Case 3: Delete Middle Element ===");
    println!("Deleting element d...");
    acc.delete(d).expect("Failed to delete element d");
    println!("Accumulator after deleting d: {:?}", acc.a.retrieve());
    println!("Element d deleted successfully!");

    println!("Updating witnesses for remaining elements...");
    updated_witness = acc.update_witness_on_deletion(x, updated_witness, d)
        .expect("Failed to update witness for x");
    let updated_w_z = acc.update_witness_on_deletion(z, w_z, d)
        .expect("Failed to update witness for z");
    let updated_w_e = acc.update_witness_on_deletion(e, w_e, d)
        .expect("Failed to update witness for e");

    println!("Verifying remaining elements...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    assert!(acc.verify(z, updated_w_z), "Verification for z failed");
    assert!(acc.verify(e, updated_w_e), "Verification for e failed");
    println!("All remaining elements verified successfully!");

    // Test case 4: Delete multiple elements
    println!("\n=== Test Case 4: Delete Multiple Elements ===");
    println!("Deleting element z...");
    acc.delete(z).expect("Failed to delete element z");
    println!("Accumulator after deleting z: {:?}", acc.a.retrieve());
    println!("Element z deleted successfully!");

    println!("Updating witnesses for remaining elements...");
    updated_witness = acc.update_witness_on_deletion(x, updated_witness, z)
        .expect("Failed to update witness for x");
    let updated_w_e = acc.update_witness_on_deletion(e, w_e, z)
        .expect("Failed to update witness for e");

    println!("Deleting element e...");
    acc.delete(e).expect("Failed to delete element e");
    println!("Accumulator after deleting e: {:?}", acc.a.retrieve());
    println!("Element e deleted successfully!");

    println!("Updating witness for x...");
    updated_witness = acc.update_witness_on_deletion(x, updated_witness, e)
        .expect("Failed to update witness for x");

    println!("Verifying element x...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    println!("Element x verified successfully!");

    // Test case 5: Add elements after deletion
    println!("\n=== Test Case 5: Add Elements After Deletion ===");
    let f = b"element_f";
    let g = b"element_g";

    println!("Adding elements f and g...");
    let w_f = acc.add(f).expect("Failed to add element f");
    let w_g = acc.add(g).expect("Failed to add element g");
    println!("Accumulator after adding f and g: {:?}", acc.a.retrieve());

    println!("Verifying all elements...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    assert!(acc.verify(f, w_f), "Verification for f failed");
    assert!(acc.verify(g, w_g), "Verification for g failed");
    println!("All elements verified successfully!");

    // Test case 6: Delete and re-add same element
    println!("\n=== Test Case 6: Delete and Re-add Same Element ===");
    println!("Deleting element f...");
    acc.delete(f).expect("Failed to delete element f");
    println!("Accumulator after deleting f: {:?}", acc.a.retrieve());
    println!("Element f deleted successfully!");

    println!("Updating witnesses for remaining elements...");
    updated_witness = acc.update_witness_on_deletion(x, updated_witness, f)
        .expect("Failed to update witness for x");
    let updated_w_g = acc.update_witness_on_deletion(g, w_g, f)
        .expect("Failed to update witness for g");

    println!("Re-adding element f...");
    let w_f_new = acc.add(f).expect("Failed to re-add element f");
    println!("Accumulator after re-adding f: {:?}", acc.a.retrieve());
    println!("Element f re-added successfully!");

    println!("Verifying all elements...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    assert!(acc.verify(f, w_f_new), "Verification for f failed");
    assert!(acc.verify(g, updated_w_g), "Verification for g failed");
    println!("All elements verified successfully!");

    println!("\nAll test cases completed successfully!");
}
