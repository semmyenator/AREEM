# Archimedes-Richardson Exhaustion-Extrapolation Method (AREEM)
## Project Overview
The **Archimedes-Richardson Exhaustion-Extrapolation Method (AREEM)** is a high-precision framework for computing the mathematical constant $\pi$. This method bridges classical geometric intuition with modern numerical analysis techniques—specifically weighted averaging and Richardson extrapolation.
By systematically analyzing and eliminating error terms, AREEM elevates the convergence order from the traditional second-order to **eighth-order**. This allows the method to reach the double-precision floating-point limit (relative error $\le 1 \times 10^{-15}$) using only **$N = 192$ polygon divisions**, achieving an efficiency improvement of over six orders of magnitude compared to the classical approach.
## Core Methodology
The method is structured into four progressive optimization modules:
### 1. Basic Exhaustion Method (2nd-Order Convergence)
Based on Archimedes' classical approach using inscribed and circumscribed regular polygons around a unit circle.
*   **Formula**:
    $$ \pi_{ex} = \frac{N}{2} \left[ \sin\left(\frac{\pi}{N}\right) + \tan\left(\frac{\pi}{N}\right) \right] $$
*   **Error**: The dominant error term is $\frac{\pi^3}{12N^2}$, resulting in relatively slow convergence.
### 2. Weighted Average Optimization (4th-Order Convergence)
By exploiting the opposite signs of the leading errors in the inscribed and circumscribed approximations, a 2:1 weighted average is used to eliminate the second-order error term.
*   **Formula**:
    $$ \pi_{sh} = \frac{N}{3} \left[ 2\sin\left(\frac{\pi}{N}\right) + \tan\left(\frac{\pi}{N}\right) \right] $$
*   **Error**: The dominant error is reduced to $\frac{\pi^5}{20N^4}$.
### 3. Richardson Extrapolation (6th- and 8th-Order Convergence)
Utilizing the even-power structure of the error expansion, Richardson extrapolation is applied to successively eliminate higher-order error terms.
*   **First Extrapolation (6th-Order)**:
    $$ \pi_{r1} = \frac{16 \cdot \pi_{sh}(2N) - \pi_{sh}(N)}{15} $$
    *   Dominant Error: $-\frac{\pi^7}{1120N^6}$.
*   **Second Extrapolation (8th-Order)**:
    $$ \pi_{r2} = \frac{64 \cdot \pi_{r1}(2N) - \pi_{r1}(N)}{63} $$
    *   Dominant Error: $\frac{\pi^9}{184320N^8}$.
## Performance Comparison
The table below summarizes the number of sides ($N$) required to achieve double-precision accuracy (error $\le 10^{-15}$) for each scheme:
| Scheme | Convergence Order | Sides ($N$) Required | Relative Efficiency |
| :--- | :---: | :--- | :---: |
| Basic Exhaustion | 2 | 201,326,592 | 1x (Baseline) |
| Weighted Average | 4 | 24,576 | 8,100x |
| Sixth-Order Extrapolation | 6 | 1,536 | 130,000x |
| **Eighth-Order Extrapolation** | **8** | **192** | **1,040,000x** |
## Engineering Calculation Process
The methodology is designed as a modular engineering process suitable for both practical computation and pedagogical demonstration:
1.  **Module 1: Basic Calculator**
    *   Computes the arithmetic mean of inscribed and circumscribed perimeters.
    *   Continues until relative error $\le 10^{-4}$.
2.  **Module 2: Weighted Optimizer**
    *   Applies the 2:1 weighting optimization.
    *   Continues until relative error $\le 10^{-8}$.
3.  **Module 3: Extrapolation Engine**
    *   **Step 1**: Applies the first Richardson extrapolation formula. Target error $\le 10^{-12}$.
    *   **Step 2**: Applies the second Richardson extrapolation formula. Target error $\le 10^{-15}$.
4.  **Module 4: Verification**
    *   Validates results against known constants and generates a comprehensive error report.
## Theoretical & Educational Value
*   **Systematic Error Analysis**: The method provides a clear pathway for elevating convergence orders (2 → 4 → 6 → 8) through rigorous Taylor expansion analysis.
*   **Numerical Verification**: The theoretical convergence rates are verified by observing error reduction ratios when $N$ is doubled (approaching $2^2, 2^4, 2^6, 2^8$).
*   **Pedagogical Utility**: The modular design allows students to verify each step using basic calculators for small $N$, bridging the gap between abstract theory and engineering practice.
## Key Constants Reference
*   $\pi \approx 3.141592653589793$
*   $\pi^3/12 \approx 2.58386$
*   $\pi^5/20 \approx 15.30098$
## Naming Significance
The name **AREEM** honors the dual heritage of the methodology:
*   **Archimedes**: Representing the geometric intuition of the classical exhaustion method.
*   **Richardson**: Representing modern extrapolation techniques and error analysis theory.
*   **Exhaustion-Extrapolation**: Symbolizing the methodological evolution from "exhaustion" to "extrapolation."
---
*This README is based on the paper "Archimedes-Richardson Exhaustion-Extrapolation Method for High-Precision Pi Computation".*
