# -*- coding: utf-8 -*-
from z3 import *
import time

# ---------------------------------------------------------------------------
# Z3 Solver Setup and Checker Function
# ---------------------------------------------------------------------------
# This is an auxillary file for the paper "Semi-abelian by Design: Johnstone Algebras Unifying Implication and Division".
# This script is used to check Theorem 1.14 in the paper.

# Enable proof generation globally if needed (can slow down checks significantly)
# set_param(proof=True)

# In the bottom of this file, you may choose a list of axioms and a list of conclusions to check,
# There is function check(assumptions, conclusions) that takes the assumptions and conclusions as arguments.
# The function will return a list of results for each conclusion, indicating whether it holds, doesn't hold, or is unknown.
# The search for proofs can easily crash the computer, I recommend to keep the timeout short.

def check(assumptions, conclusions, timeout_ms=1000):
    """
    Checks if assumptions logically entail each conclusion using Z3.

    Args:
        assumptions (list): A list of Z3 constraints (axioms).
        conclusions (list): A list of Z3 constraints (potential theorems).
        timeout_ms (int): Timeout for the solver in milliseconds.

    Returns:
        list: A list of strings ("holds", "doesn't hold", "unknown")
              corresponding to each conclusion.
    """
    results = []
    print("-" * 70)
    print("Starting Z3 Checks...")
    print(f"Number of Assumptions: {len(assumptions)}")
    print(f"Timeout per check: {timeout_ms / 1000.0} seconds")
    print("-" * 70)

    for i, concl in enumerate(conclusions):
        s = Solver()
        s.set("timeout", timeout_ms)
        s.add(assumptions)
        # Add Not(Conclusion) to check entailment via unsatisfiability
        s.add(Not(concl))

        print(f"\n[Check {i+1}/{len(conclusions)}] Checking Conclusion:")
        try:
            # Attempt to pretty-print if possible, otherwise use S-expression
            print(f"  {concl}")
        except Exception:
            try:
                print(f"  {concl.sexpr()}")
            except AttributeError:
                 print(f"  [Could not format conclusion]")


        start_time = time.time()
        result = s.check()
        end_time = time.time()
        duration = end_time - start_time
        status_str = f"({duration:.3f}s)"

        if result == unsat:
            print(f"  Result: HOLDS (Assumptions entail Conclusion) {status_str}")
            results.append("holds")
            # Uncomment the following lines to see proofs if proof=True is set
            # try:
            #    print("  Proof:\n", s.proof())
            # except Z3Exception as e:
            #    print(f"  Proof generation failed: {e}")
        elif result == sat:
            print(f"  Result: DOESN'T HOLD (Found countermodel/scenario) {status_str}")
            results.append("doesn't hold")
            # Uncomment the following lines to see the model
            # try:
            #     print("  Model:\n", s.model())
            # except Z3Exception as e:
            #     print(f"  Model generation failed: {e}")
        else:
            print(f"  Result: UNKNOWN (Timeout or resource limit?) {status_str}")
            results.append("unknown")
        print("-" * 25)

    print("-" * 70)
    print("Checks Complete.")
    print("-" * 70)
    return results

# ---------------------------------------------------------------------------
# Declarations and Helper Functions
# ---------------------------------------------------------------------------

# Declare an uninterpreted sort (the domain of the algebra)
U = DeclareSort('U')

# Declare function symbols
f = Function('f', U, U, U)    # Implication ->
m = Function('m', U, U, U)    # Multiplication *
p = Function('p', U, U, U)    # Generic binary operation 't' for relative closure
e = Const('e', U)             # Constant e

# Declare variables for use in axioms
x, y, z, w = Consts('x y z w', U)

# Helper functions for complex terms using 'f' (implication)
def t(a, b):
    """ t(a,b) := f(f(a, b), b) """
    # Expands to: f(f(a,b),b)
    return f(f(a, b), b)

def v(a, b):
    """ v(a,b) := t(t(a, b), a) using t """
    # Expands to: t(t(a, b), a) = t(f(f(a,b),b), a)
    #            = f( f( f(f(a,b),b), a) , a )
    return t(t(a, b), a)


# ---------------------------------------------------------------------------
# Helper Functions for Left-Associative Application (Makes axioms readable)
# ---------------------------------------------------------------------------

def P(*args):
    """ Applies 'p' left-associatively. P(x,y,z) -> p(p(x,y),z) """
    if not args: raise ValueError("Function P requires at least one argument.")
    res = args[0]
    for arg in args[1:]: res = p(res, arg)
    return res

def M(*args):
    """ Applies 'm' left-associatively. M(x,y,z) -> m(m(x,y),z) """
    if not args: raise ValueError("Function M requires at least one argument.")
    res = args[0]
    for arg in args[1:]: res = m(res, arg)
    return res

def F(*args):
    """ Applies 'f' left-associatively. F(x,y,z) -> f(f(x,y),z) """
    if not args: raise ValueError("Function F requires at least one argument.")
    res = args[0]
    for arg in args[1:]: res = f(res, arg)
    return res

# ---------------------------------------------------------------------------
# Axiom Definitions (using f, m, e, p)
# ---------------------------------------------------------------------------

# --- Axioms from Example 1.3 (using f, m, e) ---
# Naming convention: Matches paper example numbers
Axiom_1_Assoc = ForAll([x,y,z], M(x,y,z) == m(x, m(y,z)))
Axiom_2_RightId = ForAll(x, m(x, e) == x)
Axiom_3_LeftId  = ForAll(x, m(e, x) == x)
Axiom_4_Comm = ForAll([x,y], m(x,y) == m(y,x))
Axiom_5_Refl = ForAll(x, f(x,x) == e)
Axiom_6_UnitRed = ForAll(x, f(e, x) == x)
Axiom_7_HoopSym = ForAll([x,y], m(x, f(x,y)) == m(y, f(y,x)))
Axiom_8_Resid = ForAll([x,y,z], f(x, f(y,z)) == f(m(y,x), z)) 
Axiom_9_Idemp = ForAll(x, m(x,x) == x)
Axiom_10_Fusion = ForAll([x,y], m(x,y) == m(y, f(y,x)))
Axiom_11_T = ForAll(x, f(x, e) == e)
Axiom_12_LowerDiv = ForAll([x,y], m(x, f(x,y)) == y)
Axiom_13_UpperDiv = ForAll([x,y], f(x, m(x,y)) == y)
Axiom_14_K = ForAll([x,y], f(x, f(y,x)) == e)
Axiom_15_MP = ForAll([x,y], f(x, t(x,y)) == e) # Uses t(x,y) = f(f(x,y),y)
Axiom_16_C = ForAll([x,y,z], f(x, f(y,z)) == f(y, f(x,z)))
Axiom_17_B = ForAll([x,y,z], F(f(x,y), f(f(z,x), f(z,y))) == e) # Using F helper
Axiom_18_S = ForAll([x,y,z], F(f(z, f(x,y)), f(f(z,x), f(z,y))) == e) # Using F helper
Axiom_19_MonoDiv = ForAll([x,y], m(t(x,y), f(t(x,y), x)) == x) # Uses t helper
Axiom_20_H = ForAll([x,y,z], f(f(x,y), f(x,z)) == f(f(y,x), f(y,z)))
Axiom_21_M = ForAll([x,y,z], f(f(t(x,y), x), f(t(x,y), z)) == f(x,z)) # Uses t helper
Axiom_22_CornishJ = ForAll([x,y], v(x,y) == v(y,x)) # Uses v helper

# Relevant Quasi-Identities for f
Quasi_AntiSym_f = ForAll([x,y], Implies(And(f(x,y) == e, f(y,x) == e), x == y))
Quasi_Transitive_f = ForAll([x,y,z], Implies(And(f(x,y) == e, f(y,z) == e), f(x,z) == e))

# Equational Anti-symmetry for f
# v(x,y) == t(v(x,y), y) using f
Axiom_IAS_Equational_f = ForAll([x,y], v(x,y) == t(v(x,y), y)) # Uses t, v helpers

# --- Axioms for Relative Closure (RC) from Definition 1.11 (using generic 'p') ---
# Encoding: 'L <= R' is translated to 'P(L, R) == R'
#           'L == R' is translated to 'L == R'
# Suffix 'E' denotes an axiom that is inherently equational in the definition.

Axiom_RC_1_tReflexivityE = ForAll(x, x == p(x, x))                              # (1) t-refl E
Axiom_RC_2_tTransitivityE = ForAll([x, y, z], P(x, P(x,y,z)) == P(x,y,z))       # (2) t-trans E: x(x̄z) ≈ x̄z
Axiom_RC_3_tAntisymmetryE = ForAll([x, y], P(x,y,x) == P(x,y,x,y))              # (3) t-anti E: X ≈ Xy
Axiom_RC_4_LeftAbsorptionE = ForAll([x, y], p(x, p(x, y)) == p(x, y))           # (4) LeftAbs E: x(xy) ≈ xy
Axiom_RC_5_RightAbsorption = ForAll([x, y], P(x, y, y, p(x, y)) == p(x, y))     # (5) RightAbs <=: (xy)y <= xy
Axiom_RC_5_RightAbsorptionE = ForAll([x, y], P(x, y, y) == p(x, y))             # (5) RightAbs E: (xy)y ≈ xy
Axiom_RC_6_LeftMonotonicity = ForAll([x, y, z], P(x,z, P(x,y,z)) == P(x,y,z))   # (6) LeftMono <=: xz <= (xy)z
Axiom_RC_7_Flattening = ForAll([x, y, z], p(p(x, y), p(x, z)) == p(p(x, y), z)) # (7) Flattening E: (xy)(xz) ≈ (xy)z
Axiom_RC_8_ClosureStability = ForAll([x, y, z],                                 # (8) ClosureStab <=: ((xy)z (xy))x <= ((xy)z)x
    P(P(P(x,y,z), p(x,y)), x, P(x,y,z,x)) == P(x,y,z,x))
Axiom_RC_8_ClosureStabilityE = ForAll([x, y, z],                                # (8) ClosureStab E: ((xy)z (xy))x ≈ ((xy)z)x
    P(P(P(x,y,z), p(x,y)), x) == P(x,y,z,x))
Axiom_RC_9_WeakClosureStability = ForAll([x, y],                                # (9) WeakClosStab <=: ((xy)x (xy))x <= ((xy)x)x
    P(P(P(x,y,x), p(x,y)), x, P(x,y,x,x)) == P(x,y,x,x))
Axiom_RC_9_WeakClosureStabilityE = ForAll([x, y],                               # (9) WeakClosStab E: ((xy)x (xy))x ≈ ((xy)x)x
    P(P(P(x,y,x), p(x,y)), x) == P(x,y,x,x))

# Corresponding Quasi-Identity for 'p'
Quasi_AntiSym_p = ForAll([x,y], Implies(And(p(x,y) == y, p(y,x) == x), x == y))
# Helper for y <= xy using p
Axiom_K_p = ForAll([x,y], P(y, p(x,y)) == p(x,y))
# Cornish J using p
Axiom_CornishJ_p = ForAll([x,y],P(x,y,x) == P(y,x,y)) # Uses P helper

# --- Link between p and f (Optional: Uncomment to identify p with t) ---
# Link_p_equals_tf = ForAll([x,y], p(x,y) == t(x,y))


# ---------------------------------------------------------------------------
# Theory Definitions (Explicit Lists of Axioms)
# ---------------------------------------------------------------------------

# Theory for Weak Relative Closure using generic 'p'
Theory_WRC_p = [ # Def 1.11: (5)<=, (7)E, (9)<=
    Axiom_RC_5_RightAbsorption,
    Axiom_RC_7_Flattening, # Removed E suffix
    Axiom_RC_9_WeakClosureStability,
]

# Theory for Relative Closure using generic 'p'
Theory_RC_p = [ # Def 1.11: (4)E, (5)<=, (6)<=, (7)E, (8)<=
    Axiom_RC_4_LeftAbsorptionE,
    Axiom_RC_5_RightAbsorption,
    Axiom_RC_6_LeftMonotonicity,
    Axiom_RC_7_Flattening, # Removed E suffix
    Axiom_RC_8_ClosureStability,
]

# Theory for MBC-algebras (assumes 'f' is implication)
Theory_MBC = [
    Axiom_5_Refl, Axiom_6_UnitRed, # Base for implicative structures
    Axiom_21_M,                   # M-axiom
    Axiom_17_B,                   # B-axiom (Compositionality)
    Axiom_16_C,                   # C-axiom (Implicative Commutativity)
    Quasi_AntiSym_f
]


# --- Other theories for reference ---
Theory_Johnstone_J = [Axiom_5_Refl, Axiom_6_UnitRed, Axiom_19_MonoDiv]
Theory_Hoops = [
    Axiom_1_Assoc, Axiom_2_RightId, Axiom_3_LeftId,
    Axiom_4_Comm, Axiom_5_Refl, Axiom_6_UnitRed,
    Axiom_7_HoopSym, Axiom_8_Resid,
]
Theory_HeytingSemilattices = Theory_Hoops + [Axiom_9_Idemp]


# ---------------------------------------------------------------------------
# Main Execution Block - Select Assumptions and Conclusions to Check
# ---------------------------------------------------------------------------

if __name__ == '__main__':

    # --- Select Assumptions ---
    assumptions = Theory_WRC_p + [Quasi_AntiSym_p]# + [Axiom_K_p]
    
    # --- Select Conclusions to Check ---
    conclusions = [
        Axiom_RC_3_tAntisymmetryE,
        #Axiom_CornishJ_p
    ]
    # --- Run the Checks ---

    results = check(assumptions, conclusions)

    # --- Print Summary ---
    print("\n" + "=" * 70)
    print("SUMMARY OF CHECKS:")
    print("=" * 70)
    print(f"Assumptions Used: {len(assumptions)} axioms")
    for idx, res in enumerate(results):
        conclusion_checked = conclusions[idx]
        check_no = idx + 1
        try:
            print(f"Conclusion {check_no}: [{conclusion_checked}]")
        except Exception:
            print(f"Conclusion {check_no}: [Could not format conclusion]")
        print(f"  Result: {res}")
    print("=" * 70)