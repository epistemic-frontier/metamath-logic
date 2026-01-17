
import sys
from pathlib import Path

# Adjust path to find the packages
ROOT = Path(__file__).resolve().parents[1]
sys.path.append(str(ROOT / "metamath-logic" / "src"))
sys.path.append(str(ROOT / "metamath-prelude" / "src"))
sys.path.append(str(ROOT / "proof-scaffold" / "src"))

from skfd.core.symbols import SymbolInterner
from skfd.authoring.formula import Wff
from logic.propositional.hilbert import HilbertSystem
from logic.propositional.hilbert.lemmas import (
    LemmaBuilder, LemmaProof, ProofStep,
    prove_pm2_21, prove_con3, prove_L7_double_neg_elim, prove_syl, prove_a1i
)

def prove_modus_tollens(sys: HilbertSystem) -> LemmaProof:
    """Modus Tollens: ph -> ps, -. ps |- -. ph
    
    Source: https://math.stackexchange.com/questions/767603/hilbert-system-with-propositional-logic-p-rightarrow-q-neg-q-vdash-neg-p
    """
    lb = LemmaBuilder(sys, "modus_tollens")
    
    # Hypotheses
    h1 = lb.hyp("h1", "ph -> ps")
    h2 = lb.hyp("h2", "-. ps")
    
    # Step 1: (ph -> ps) -> (-. ps -> -. ph)  (Contrapositive)
    # We can use con3: (ph -> ps) -> (-. ps -> -. ph)
    # But wait, con3 is a lemma, so we need to instantiate it or use it.
    # In HilbertSystem, we can compile the statement of a lemma.
    # But here we want to use the lemma as a rule/scheme.
    # Since lemmas.py functions return a LemmaProof, we can't directly "call" them in the builder 
    # unless we treat them as axioms or we re-prove them.
    # However, for this exercise, we can just assume we can compile the theorem statement directly
    # if we consider it "known".
    # Or better, let's just use the Axioms to prove it if it's short, or use the lemma statement.
    
    # Let's use the statement of con3 directly.
    s1 = lb.step("s1", "( ph -> ps ) -> ( -. ps -> -. ph )", "con3")
    
    # Step 2: -. ps -> -. ph (MP h1, s1)
    s2 = lb.mp("s2", h1, s1, "MP h1, s1")
    
    # Step 3: -. ph (MP h2, s2)
    s3 = lb.mp("s3", h2, s2, "MP h2, s2")
    
    return lb.build(s3)

def prove_linearity(sys: HilbertSystem) -> LemmaProof:
    """Linearity: -. ( ph -> ps ) -> ( ps -> ph )
       Equivalent to (ph -> ps) \/ (ps -> ph)

       Source: https://math.stackexchange.com/questions/4476682/prove-that-p-to-q-lor-q-to-p-is-a-tautology-in-hilbert-system
    """
    lb = LemmaBuilder(sys, "linearity")
    
    # Goal: -. ( ph -> ps ) -> ( ps -> ph )
    
    # Strategy:
    # 1. -. ( ph -> ps ) -> ph
    # 2. ph -> ( ps -> ph )  (A1)
    # 3. -. ( ph -> ps ) -> ( ps -> ph ) (Syllogism)
    
    # Proof of 1: -. ( ph -> ps ) -> ph
    # We know -. ph -> ( ph -> ps ) (pm2.21)
    # Contrapositive (con3): ( -. ph -> ( ph -> ps ) ) -> ( -. ( ph -> ps ) -> -. -. ph )
    # So we can get: -. ( ph -> ps ) -> -. -. ph
    # Then -. -. ph -> ph (L7)
    # So -. ( ph -> ps ) -> ph
    
    # Let's build it.
    
    # Step 1.1: -. ph -> ( ph -> ps )
    s1_1 = lb.step("s1.1", "-. ph -> ( ph -> ps )", "pm2.21")
    
    # Step 1.2: ( -. ph -> ( ph -> ps ) ) -> ( -. ( ph -> ps ) -> -. -. ph )
    # This is con3 with phi = -. ph, psi = (ph -> ps)
    s1_2 = lb.step("s1.2", "( -. ph -> ( ph -> ps ) ) -> ( -. ( ph -> ps ) -> -. -. ph )", "con3 instance")
    
    # Step 1.3: -. ( ph -> ps ) -> -. -. ph
    s1_3 = lb.mp("s1.3", s1_1, s1_2)
    
    # Step 1.4: -. -. ph -> ph
    s1_4 = lb.step("s1.4", "-. -. ph -> ph", "L7_double_neg_elim")
    
    # Step 1.5: -. ( ph -> ps ) -> ph
    # We need syl: (A -> B) -> ((B -> C) -> (A -> C)) ? No, syl is usually a rule A->B, B->C |- A->C
    # In Hilbert system, we usually use syl lemma: (A->B) -> ((B->C) -> (A->C)) is a theorem (imim2 variant or similar).
    # lemmas.py has prove_syl which is a rule: Hyp1, Hyp2 -> Concl.
    # But here we are inside a single proof (no hypotheses). We need the implication form.
    # The implication form is `syl` (theorem). Let's check lemmas.py for the implication form.
    # lemmas.py: prove_syl is a rule.
    # lemmas.py: prove_imim1? No.
    # We need A1 (syl) form or similar.
    # Actually, we can use the `syl` rule if we can lift it to an implication?
    # No, we are building a proof of a theorem, not a rule derivation.
    # We need the theorem: (A -> B) -> ((B -> C) -> (A -> C)).
    # Let's check lemmas.py again.
    # prove_syl is: Hyp 1: ph -> ps, Hyp 2: ps -> ch, Concl: ph -> ch.
    # That's a derived rule.
    # prove_syli: ps -> (ph -> th). Hyp1: ps -> (ph -> ch), Hyp2: ch -> (ph -> th).
    
    # Wait, if we want to prove A -> C from A -> B and B -> C *as theorems*, we can use the syl rule!
    # Because A->B and B->C are provable (as steps in our proof), so we can treat them as "Hypotheses" for the syl rule application?
    # No, `prove_syl` returns a LemmaProof object. It doesn't apply the rule inside another proof.
    # But `LemmaBuilder` doesn't have a `syl` method.
    # However, we can just manually implement the syl steps:
    # syl(f, g) where f: A->B, g: B->C => A->C
    # Proof:
    # 1. f: A->B
    # 2. g: B->C
    # 3. A1: (B->C) -> (A -> (B->C))
    # 4. A->(B->C) (MP 2,3)
    # 5. A2: (A->(B->C)) -> ((A->B) -> (A->C))
    # 6. (A->B) -> (A->C) (MP 4,5)
    # 7. A->C (MP 1,6)
    
    # So I can implement a helper `syl` in the builder or just write the steps.
    # Writing steps is fine.
    
    # Back to Step 1.5: syl(s1.3, s1.4) -> s1.5
    # s1.3: -. ( ph -> ps ) -> -. -. ph
    # s1.4: -. -. ph -> ph
    # Target: -. ( ph -> ps ) -> ph
    
    # Constructing syl steps for s1.5:
    # s1.4_lift: ( -. -. ph -> ph ) -> ( -. ( ph -> ps ) -> ( -. -. ph -> ph ) ) (A1)
    s1_4_lift = lb.step("s1.4_lift", "( -. -. ph -> ph ) -> ( -. ( ph -> ps ) -> ( -. -. ph -> ph ) )", "A1")
    
    # s1_5_pre: -. ( ph -> ps ) -> ( -. -. ph -> ph )
    s1_5_pre = lb.mp("s1.5_pre", s1_4, s1_4_lift)
    
    # s1_5_dist: ( -. ( ph -> ps ) -> ( -. -. ph -> ph ) ) -> ( ( -. ( ph -> ps ) -> -. -. ph ) -> ( -. ( ph -> ps ) -> ph ) ) (A2)
    s1_5_dist = lb.step("s1.5_dist", "( -. ( ph -> ps ) -> ( -. -. ph -> ph ) ) -> ( ( -. ( ph -> ps ) -> -. -. ph ) -> ( -. ( ph -> ps ) -> ph ) )", "A2")
    
    # s1_5_impl: ( -. ( ph -> ps ) -> -. -. ph ) -> ( -. ( ph -> ps ) -> ph )
    s1_5_impl = lb.mp("s1.5_impl", s1_5_pre, s1_5_dist)
    
    # s1_5: -. ( ph -> ps ) -> ph
    s1_5 = lb.mp("s1.5", s1_3, s1_5_impl)
    
    # Step 2: ph -> ( ps -> ph )
    s2 = lb.step("s2", "ph -> ( ps -> ph )", "A1")
    
    # Step 3: -. ( ph -> ps ) -> ( ps -> ph )
    # syl(s1.5, s2)
    # s1.5: -. ( ph -> ps ) -> ph
    # s2: ph -> ( ps -> ph )
    
    # Constructing syl steps for s3:
    # s2_lift: ( ph -> ( ps -> ph ) ) -> ( -. ( ph -> ps ) -> ( ph -> ( ps -> ph ) ) ) (A1)
    s2_lift = lb.step("s2_lift", "( ph -> ( ps -> ph ) ) -> ( -. ( ph -> ps ) -> ( ph -> ( ps -> ph ) ) )", "A1")
    
    # s3_pre: -. ( ph -> ps ) -> ( ph -> ( ps -> ph ) )
    s3_pre = lb.mp("s3_pre", s2, s2_lift)
    
    # s3_dist: ( -. ( ph -> ps ) -> ( ph -> ( ps -> ph ) ) ) -> ( ( -. ( ph -> ps ) -> ph ) -> ( -. ( ph -> ps ) -> ( ps -> ph ) ) ) (A2)
    s3_dist = lb.step("s3_dist", "( -. ( ph -> ps ) -> ( ph -> ( ps -> ph ) ) ) -> ( ( -. ( ph -> ps ) -> ph ) -> ( -. ( ph -> ps ) -> ( ps -> ph ) ) )", "A2")
    
    # s3_impl: ( -. ( ph -> ps ) -> ph ) -> ( -. ( ph -> ps ) -> ( ps -> ph ) )
    s3_impl = lb.mp("s3_impl", s3_pre, s3_dist)
    
    # s3: -. ( ph -> ps ) -> ( ps -> ph )
    s3 = lb.mp("s3", s1_5, s3_impl)
    
    return lb.build(s3)

def run_proofs():
    interner = SymbolInterner()
    sys = HilbertSystem.make(interner=interner)
    
    print("Proving Modus Tollens...")
    mt_proof = prove_modus_tollens(sys)
    print(f"Passed: {mt_proof.name}")
    print(f"Statement: {mt_proof.statement}")
    
    print("\nProving Linearity ( (A->B) \/ (B->A) )...")
    lin_proof = prove_linearity(sys)
    print(f"Passed: {lin_proof.name}")
    print(f"Statement: {lin_proof.statement}")

if __name__ == "__main__":
    run_proofs()
