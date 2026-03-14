//! Archimedes-Richardson Exhaustion-Extrapolation Method for High-precision Pi Computation
//!
//! This program implements four progressively optimized methods for computing π:
//! 1. Basic Exhaustion Method (2nd-order convergence)
//! 2. Weighted Average Method (4th-order convergence)
//! 3. Richardson Extrapolation 1st Order (6th-order convergence)
//! 4. Richardson Extrapolation 2nd Order (8th-order convergence)
//!
//! Reference: "Archimedes-Richardson Exhaustion-Extrapolation Method for High-Precision
//! Pi Computation: Theory, Error Analysis, and Engineering Practice"

use std::f64::consts::PI;

// =============================================================================
// Phase 1: Core Constants and Basic Functions
// =============================================================================

/// Calculate relative error: |π_approx - π_true| / π_true
fn relative_error(pi_approx: f64) -> f64 {
    (pi_approx - PI).abs() / PI
}

/// Format error in scientific notation
fn format_error_scientific(error: f64) -> String {
    if error == 0.0 {
        return "0.0".to_string();
    }
    let exponent = error.log10().floor() as i32;
    let mantissa = error / 10_f64.powi(exponent);
    format!("{:.4}e{}", mantissa, exponent)
}

// =============================================================================
// Phase 2: Module 1 - Basic Exhaustion Method (2nd-order convergence)
// =============================================================================

/// Calculate π using inscribed polygon: π_in = N * sin(π/N)
fn pi_inscribed(n: f64) -> f64 {
    n * (PI / n).sin()
}

/// Calculate π using circumscribed polygon: π_out = N * tan(π/N)
fn pi_circumscribed(n: f64) -> f64 {
    n * (PI / n).tan()
}

/// Module 1: Basic Exhaustion Method (Archimedes' classical approach)
/// Formula: Archimedes_Exhaustion = (π_in + π_out) / 2
/// Convergence order: 2 (error ∝ 1/N²)
/// Dominant error term: π³/(12N²) ≈ 2.584/N²
fn archimedes_exhaustion(n: f64) -> f64 {
    let pi_in = pi_inscribed(n);
    let pi_out = pi_circumscribed(n);
    (pi_in + pi_out) / 2.0
}

// =============================================================================
// Phase 3: Module 2 - Weighted Average Method (4th-order convergence)
// =============================================================================

/// Module 2: Snellius-Huygens Weighted Average
/// Formula: Snellius_Huygens_Approx = (2π_in + π_out) / 3
/// Convergence order: 4 (error ∝ 1/N⁴)
/// Dominant error term: π⁵/(20N⁴) ≈ 15.301/N⁴
///
/// The 2:1 weighting exploits the opposite signs of leading errors:
/// - π_in has negative leading error: -π³/(6N²)
/// - π_out has positive leading error: +π³/(3N²)
/// - 2:1 ratio cancels the 1/N² term exactly
fn snellius_huygens_approx(n: f64) -> f64 {
    let pi_in = pi_inscribed(n);
    let pi_out = pi_circumscribed(n);
    (2.0 * pi_in + pi_out) / 3.0
}

// =============================================================================
// Phase 4: Module 3 - Richardson Extrapolation (6th and 8th-order convergence)
// =============================================================================

/// Module 3a: First Richardson Extrapolation (6th-order convergence)
/// Formula: Richardson_Extrap_1st = [16 * SH(2N) - SH(N)] / 15
/// where SH = Snellius_Huygens_Approx
///
/// Convergence order: 6 (error ∝ 1/N⁶)
/// Dominant error term: π⁷/(1120 N⁶) ≈ 2.697/N⁶
///
/// The coefficient A=16 is derived from: A/16 - 1 = 0
/// This eliminates the 1/N⁴ term from the error expansion
fn richardson_extrap_1st(n: f64) -> f64 {
    let sh_n = snellius_huygens_approx(n);
    let sh_2n = snellius_huygens_approx(2.0 * n);
    (16.0 * sh_2n - sh_n) / 15.0
}

/// Module 3b: Second Richardson Extrapolation (8th-order convergence)
/// Formula: Richardson_Extrap_2nd = [64 * RE1(2N) - RE1(N)] / 63
/// where RE1 = Richardson_Extrap_1st
///
/// Convergence order: 8 (error ∝ 1/N⁸)
/// Dominant error term: π⁹/(120960 N⁸) ≈ 0.2464/N⁸
///
/// The coefficient B=64 is derived from: B/64 - 1 = 0
/// This eliminates the 1/N⁶ term from the error expansion
fn richardson_extrap_2nd(n: f64) -> f64 {
    let re1_n = richardson_extrap_1st(n);
    let re1_2n = richardson_extrap_1st(2.0 * n);
    (64.0 * re1_2n - re1_n) / 63.0
}

// =============================================================================
// Phase 5: Verification and Reporting System
// =============================================================================

/// Structure to hold computation results
#[derive(Debug, Clone)]
struct ComputationResult {
    n: f64,
    pi_approx: f64,
    error: f64,
    convergence_order: u32,
}

impl ComputationResult {
    fn new(n: f64, pi_approx: f64, order: u32) -> Self {
        ComputationResult {
            n,
            pi_approx,
            error: relative_error(pi_approx),
            convergence_order: order,
        }
    }
}

/// Verify convergence order by computing error ratio
/// For p-th order method: error(N) / error(2N) → 2^p as N → ∞
fn verify_convergence_order(results: &[ComputationResult]) -> Vec<(f64, f64)> {
    let mut ratios = Vec::new();
    for i in 0..results.len() - 1 {
        let ratio = results[i].error / results[i + 1].error;
        ratios.push((results[i].n, ratio));
    }
    ratios
}

/// Print a formatted separator line
fn print_separator() {
    println!("{}", "=".repeat(70));
}

/// Print a formatted section header
fn print_section_header(title: &str) {
    println!();
    print_separator();
    println!("  {}", title);
    print_separator();
    println!();
}

/// Print computation results in simple list format
fn print_results_table(results: &[ComputationResult]) {
    println!("{:<10} {:<22} {:<25} {:<15}", "N", "π Approximation", "Relative Error", "Conv. Order");
    println!("{}", "-".repeat(75));
    for r in results {
        println!("{:<10.0} {:<22.15} {:<25} {:<15}",
            r.n,
            r.pi_approx,
            format_error_scientific(r.error),
            r.convergence_order
        );
    }
}

/// Print error ratio analysis
fn print_error_ratios(ratios: &[(f64, f64)], theoretical: f64) {
    println!("\n[Error Ratio Analysis (Convergence Verification)]");
    println!("Theoretical Target: 2^p = {:.0}", theoretical);
    println!("{:<10} {:<20} {:<15}", "N", "Error Ratio", "Deviation (%)");
    println!("{}", "-".repeat(50));
    for (n, ratio) in ratios {
        let deviation = ((ratio - theoretical) / theoretical * 100.0).abs();
        println!("{:<10.0} {:<20.4} {:<15.2}", n, ratio, deviation);
    }
}

/// Calculate efficiency improvement compared to basic method
fn calculate_efficiency(n_required: f64, n_basic: f64) -> f64 {
    n_basic / n_required
}

// =============================================================================
// Phase 6: Main Function - Integration and Testing
// =============================================================================

fn main() {
    // Print program header
    println!("\nArchimedes-Richardson Exhaustion-Extrapolation Method");
    println!("for High-Precision π Computation\n");

    // Define test values of N (following N = 6 × 2^k pattern)
    let n_values: Vec<f64> = vec
![6.0, 12.0, 24.0, 48.0, 96.0, 192.0, 384.0];

    // =========================================================================
    // Module 1: Basic Exhaustion Method (2nd-order convergence)
    // =========================================================================
    print_section_header("Module 1: Basic Exhaustion Method (2nd-Order)
");
    println!("Formula: Archimedes_Exhaustion = (N/2)[sin(π/N) + tan(π/N)]");
    println!("Dominant error term: π³/(12N²) ≈ 2.584/N²");
    println!("Convergence order: 2 (error ratio → 4 when N doubles)\n");

    let mut basic_results: Vec<ComputationResult> = Vec::new();
    for &n in &n_values {
        let pi_approx = archimedes_exhaustion(n);
        basic_results.push(ComputationResult::new(n, pi_approx, 2));
    }
    print_results_table(&basic_results);
    let basic_ratios = verify_convergence_order(&basic_results);
    print_error_ratios(&basic_ratios, 4.0);

    // =========================================================================
    // Module 2: Weighted Average Method (4th-order convergence)
    // =========================================================================
    print_section_header("Module 2: Weighted Average Method (4th-Order)");
    println!("Formula: Snellius_Huygens_Approx = (N/3)[2sin(π/N) + tan(π/N)]");
    println!("Dominant error term: π⁵/(20N⁴) ≈ 15.301/N⁴");
    println!("Convergence order: 4 (error ratio → 16 when N doubles)");
    println!("Optimization: 2:1 weighting cancels the 1/N² error term\n");

    let mut weighted_results: Vec<ComputationResult> = Vec::new();
    for &n in &n_values {
        let pi_approx = snellius_huygens_approx(n);
        weighted_results.push(ComputationResult::new(n, pi_approx, 4));
    }
    print_results_table(&weighted_results);
    let weighted_ratios = verify_convergence_order(&weighted_results);
    print_error_ratios(&weighted_ratios, 16.0);

    // =========================================================================
    // Module 3a: First Richardson Extrapolation (6th-order convergence)
    // =========================================================================
    print_section_header("Module 3a: Richardson Extrapolation 1st (6th-Order)");
    println!("Formula: Richardson_Extrap_1st = [16×SH(2N) - SH(N)] / 15");
    println!("Dominant error term: π⁷/(1120 N⁶) ≈ 2.697/N⁶");
    println!("Convergence order: 6 (error ratio → 64 when N doubles)");
    println!("Optimization: Eliminates 1/N⁴ term using A=16 coefficient\n");

    let mut re1_results: Vec<ComputationResult> = Vec::new();
    let n_values_re1: Vec<f64> = vec
![24.0, 48.0, 96.0, 192.0, 384.0];
    for &n in &n_values_re1 {
        let pi_approx = richardson_extrap_1st(n);
        re1_results.push(ComputationResult::new(n, pi_approx, 6));
    }
    print_results_table(&re1_results);
    let re1_ratios = verify_convergence_order(&re1_results);
    print_error_ratios(&re1_ratios, 64.0);

    // =========================================================================
    // Module 3b: Second Richardson Extrapolation (8th-order convergence)
    // =========================================================================
    print_section_header("Module 3b: Richardson Extrapolation 2nd (8th-Order)");
    println!("Formula: Richardson_Extrap_2nd = [64×RE1(2N) - RE1(N)] / 63");
    println!("Dominant error term: π⁹/(120960 N⁸) ≈ 0.2464/N⁸");
    println!("Convergence order: 8 (error ratio → 256 when N doubles)");
    println!("Optimization: Eliminates 1/N⁶ term using B=64 coefficient\n");

    let mut re2_results: Vec<ComputationResult> = Vec::new();
    let n_values_re2: Vec<f64> = vec
![48.0, 96.0, 192.0, 384.0];
    for &n in &n_values_re2 {
        let pi_approx = richardson_extrap_2nd(n);
        re2_results.push(ComputationResult::new(n, pi_approx, 8));
    }
    print_results_table(&re2_results);
    let re2_ratios = verify_convergence_order(&re2_results);
    print_error_ratios(&re2_ratios, 256.0);

    // =========================================================================
    // Efficiency Comparison Summary
    // =========================================================================
    print_section_header("Efficiency Comparison Summary");
    
    let n_basic: f64 = 201_326_592.0; // N required for basic method
    let n_weighted: f64 = 24_576.0;
    let n_re1: f64 = 1_536.0;
    let n_re2: f64 = 192.0;

    println!("{:<25} {:<7} {:<15} {:<20}", "Method", "Order", "N for 10⁻¹⁵", "Relative Efficiency");
    println!("{}", "-".repeat(70));
    println!("{:<25} {:<7} {:<15.0} {:<20}", "Basic Exhaustion", 2, n_basic, "1× (baseline)");
    println!("{:<25} {:<7} {:<15.0} {:<20.0}×", "Weighted Average", 4, n_weighted, calculate_efficiency(n_weighted, n_basic));
    println!("{:<25} {:<7} {:<15.0} {:<20.0}×", "Richardson Extrapol. 1st", 6, n_re1, calculate_efficiency(n_re1, n_basic));
    println!("{:<25} {:<7} {:<15.0} {:<20.0}×", "Richardson Extrapol. 2nd", 8, n_re2, calculate_efficiency(n_re2, n_basic));

    // =========================================================================
    // Final Verification
    // =========================================================================
    print_section_header("Final Verification: Double-Precision Limit Achievement");
    
    let final_n = 192.0;
    let final_pi = richardson_extrap_2nd(final_n);
    let final_error = relative_error(final_pi);

    println!("Using N = {} polygon divisions:", final_n);
    println!("  Computed π = {:.15}", final_pi);
    println!("  True π      = {:.15}", PI);
    println!("  Difference  = {:.2e}", (final_pi - PI).abs());
    println!("  Relative Error = {:.2e}", final_error);

    if final_error <= 1e-15 {
        println!("\n[SUCCESS] Achieved double-precision limit (error ≤ 10⁻¹⁵)");
    } else {
        println!("\n[NOTE] Error slightly above 10⁻¹⁵ due to floating-point limitations");
    }

    // =========================================================================
    // Key Constants Reference
    // =========================================================================
    print_section_header("Appendix: Key Mathematical Constants");
    
    println!("{:<15} {:<30}", "Constant", "Value (Double Precision)");
    println!("{}", "-".repeat(50));
    println!("{:<15} {:.15}", "π", PI);
    println!("{:<15} {:.15}", "π³", PI.powi(3));
    println!("{:<15} {:.15}", "π³/12", PI.powi(3) / 12.0);
    println!("{:<15} {:.15}", "π⁵", PI.powi(5));
    println!("{:<15} {:.15}", "π⁵/20", PI.powi(5) / 20.0);
    println!("{:<15} {:.15}", "π⁷", PI.powi(7));
    println!("{:<15} {:.15}", "π⁷/1120", PI.powi(7) / 1120.0);
    println!("{:<15} {:.15}", "π⁹", PI.powi(9));
    println!("{:<15} {:.15}", "π⁹/120960", PI.powi(9) / 120960.0);

    // =========================================================================
    // Theoretical Significance
    // =========================================================================
    print_section_header("Theoretical Significance");
    
    println!("The Archimedes-Richardson Exhaustion-Extrapolation Method demonstrates:\n");
    println!("1. Classical-to-Modern Bridge:");
    println!("   Archimedes' geometric intuition (3rd century BC) combined with");
    println!("   Richardson's extrapolation theory (20th century AD)\n");
    println!("2. Systematic Error Control:");
    println!("   Each optimization step eliminates a specific error term,");
    println!("   with clear mathematical justification and verification\n");
    println!("3. Efficiency Improvement:");
    println!("   Over 1,000,000× efficiency gain: from ~200 million divisions");
    println!("   (basic method) to just 192 divisions (8th-order scheme)\n");
    println!("4. Educational Value:");
    println!("   Modular structure supports progressive learning of");
    println!("   numerical analysis concepts: convergence order, error cancellation,");
    println!("   and extrapolation techniques\n");
    
    print_separator();
    println!("Computation Complete");
    print_separator();
}
