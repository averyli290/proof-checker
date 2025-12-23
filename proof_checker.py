'''
Docstring for proof_checker

syntax ideas:

use boxes from section 2.1 of https://plato.stanford.edu/entries/natural-deduction/#Intr,
effectively natural deduction

on the right is either ASSUMPTION
or it is a rule of TFL or FOL with lines specifying what to reference

The typically rules of inference include these:

∧-Introduction: a conjunction may be inferred from its two conjuncts
∧-Elimination: a conjunct may be inferred from a conjunction.
∨-Introduction: a disjunction may be inferred from either disjunct.
→-Elimination: B may be inferred from the two premises A and (A→B) (MP)
¬-Elimination: an arbitrary formula, B, may be inferred from a pair of contradictory premises, A and ¬A.


There are also what Jaśkowski calls rules of supposition, in which conclusions are inferred, not from earlier formulas, but from the presence of one or more subproofs of a specified kind. Typically (described in Fitch-style terminology) these include:
This is done when the ASSUMPTION is written in a subproof, and then there is following line in the subproof.
The ASSUMPTIONS are at the top of the subproofs

→-Introduction: (A → B) may be asserted after a subproof having A as its hypothesis and and B as a line.
∨-Elimination: an arbitrary formula C may be asserted after three items: a disjunction, (A ∨ B), a subproof,
                having A as its hypothesis, with C as a line, and a subproof, having B as its hypothesis, with C as a line.
¬-Introduction: a negation, ¬A , may be asserted after a subproof, with A as its hypothesis, containing a pair
                of contradictory formulas, B and ¬B , as lines.

'''


from enum import Enum

class Term:
    '''
    Every variable v_i is a term of L
        – Every constant symbol of L is a term of L
        – If f is an n-place function symbol of L, and t1, ..., tn areterms of L, then f(t1,..., tn) is a term of L (no function symbols yet)
        – Nothing else is a term of L.
    '''
    def __init__(self):
        pass

    def is_constant(self):
        return isinstance(self, Constant)

    def is_variable(self):
        return isinstance(self, Variable)

class Constant(Term):
    '''
    Depends on your language L, but for now there are no constants.
    '''
    def __init__(self, value):
        self.value = value
    
    def __repr__(self):
        return str(self.value)
    
    def __str__(self):
        return self.__repr__()

class Variable(Term):
    '''
    Depends on your language L, for now represented by v_0, v_1, ... with infinitely many indices
    '''
    def __init__(self, idx):
        self.idx = idx
    
    def __eq__(self, other_var):
        return self.idx == other_var.idx

    def __repr__(self):
        return f"v_{self.idx}"

    def __str__(self, ):
        return self.__repr__()

class Op(Enum):
    '''
    – The Propositional Connectives: →, ∧, ∨, ¬, ⊥
    – The Quantifiers: ∀, ∃
    – The Identity Predicate: =
    '''
    IMPLIES = 1
    AND = 2
    OR = 3
    NOT = 4
    BOTTOM = 5
    FORALL = 6
    EXISTS = 7
    EQ = 8
    
    def is_binary(op):
        return (op == Op.IMPLIES or 
                op == Op.AND or 
                op == Op.OR or 
                op == Op.EQ)

    def is_unary(op):
        return op == Op.NOT

    def is_quantifier(op):
        return op == Op.FORALL or op == Op.EXISTS

class Formula:
    '''
    We define the set of formulas Frm(L) of L inductively as follows:
        – ⊥ is an atomic formula.
        – If R is an n-place predicate letter of L, and t1, . . . , tn are terms of L, then R(t1, . . . , tn) is an atomic formula. (Skipping for now)
        – If t1 and t2 are terms of L (and = is in L) then = (t1, t2) is an atomic formula.
        – If A and B are formulas then:
        * ¬A is a formula
        * (A ∧ B) is a formula
        * (A ∨ B) is a formula
        * (A → B) is a formula
        – If A is a formula, and x is a variable then
        * ∃xA is a formula
        * ∀xA is a formula
        – Nothing else is a formula.
    '''
    def __init__(self, op=None, left=None, right=None, var_idx=-1):
        '''
        Docstring for __init__
        
        :param self: Description
        :param op: Description
        :param left: Description
        :param right: Description
        :param var_idx: -1 if there if current Formula is not a variable, index i representing vf_i otherwise where vf_i is a Formula variable
        '''
        self.op = op
        self.left = left
        self.right = right
        self.var_idx = var_idx
        self.validate_formula()
    
    def validate_formula(self):
        '''
        Checks if formula is actually valid
            - e.g. if op is Op.AND, that self.left and self.right are both Formula
            - e.g. if op is Op.NOT, that self.left is a Formula and self.right is None
            - e.g. if op is Op.EXISTS, that self.left is a Variable and self.right is Formula
        '''
        is_valid = False
        if self.op is None:
            if self.var_idx > -1:
                is_valid = isinstance(self, FormulaVar) and self.op is None and self.left is None and self.right is None
            else:
                raise ValueError(f"Formula variable {self} must have an Formula Variable index > -1")
        else:
            if self.var_idx != -1:
                raise ValueError(f"Formula variable {self} must have an Formula Variable index = -1")
            elif Op.is_binary(self.op):
                is_valid = isinstance(self.left, Formula) and isinstance(self.right, Formula)
            elif Op.is_unary(self.op):
                is_valid = isinstance(self.left, Formula) and self.right is None
                if (self.op == Op.NOT and isinstance(self.left, Formula) and self.left.op == Op.Not):
                    self = self.left.left
                is_valid = self.validate_formula(self)
            elif Op.is_quantifier(self.op):
                is_valid = isinstance(self.left, Variable) and isinstance(self.right, Formula)
            else:
                raise RuntimeError(f"Unknown type for operator value of with value {self.op}")

        try:
            assert(is_valid)
        except AssertionError:
            raise AssertionError(f"Formula of value {str(self)} is not a valid formula")
    
    def __eq__(self, other):
        '''
        Check if two formluas are the "same" for ¬-Elimination
        '''
        return ((self.op == other.op) and
                (self.left == other.left) and
                (self.right == other.right) and
                (self.var_idx == other.var_idx))
    
    def __str__(self):
        return f"{str(self.op)}({str(self.left)},{str(self.right)})"

class FormulaVar(Formula):
    '''
    Not to be confused with variables used in terms, which lie in the actual domain
    These are variables which themselves are formulas, which can be understood as 0-ary predicates if so desired
    This workaround is used mostly because this is a proof assistant and we want to be able to refernce arbitrary
    formulas
    '''
    def __init__(self, var_idx=0):
        super().__init__(op=None, left=None, right=None, var_idx=var_idx)
    
    def __eq__(self, other):
        '''
        Two variables are equal if they have the same index
        
        :param self: Description
        :param other: Description
        '''
        return self.var_idx == other.var_idx
    
    def __str__(self):
        return f"FormulaVar({self.var_idx})"

class Rule(Enum):
    '''
    Inference Rule
    ∧-Introduction: a conjunction may be inferred from its two conjuncts
    ∧-Elimination: a conjunct may be inferred from a conjunction.
    ∨-Introduction: a disjunction may be inferred from either disjunct.
    →-Elimination: B may be inferred from the two premises A and (A→B) (MP)
    ¬-Elimination: an arbitrary formula, B, may be inferred from a pair of contradictory premises, A and ¬A.

    Supposition Rules
    →-Introduction: (A → B) may be asserted after a subproof having A as its hypothesis and and B as a line.
    ∨-Elimination: an arbitrary formula C may be asserted after three items: a disjunction, (A ∨ B), a subproof,
                    having A as its hypothesis, with C as a line, and a subproof, having B as its hypothesis, with C as a line.
    ¬-Introduction: a negation, ¬A , may be asserted after a subproof, with A as its hypothesis, containing a pair
                    of contradictory formulas, B and ¬B , as lines.
    '''
    AND_INTR = 1
    AND_ELIM = 2
    OR_INTR = 3
    IMP_ELIM = 4
    NOT_ELIM = 5

    IMP_INTR = 6
    OR_ELIM = 7
    NOT_INTR = 8

class ProofLine:
    def __init__(self, formula: Formula, depth=0, proof_num=0, is_hypothesis=False):
        '''
        Docstring for __init__
        
        :param formula: Formula of the proof line
        :param depth: The depth of the subproof which this ProofLine is contained in
        :param proof_num: The proof that the ProofLine is associated with
        :param is_hypothesis: 
        '''
        self.formula = formula
        self.depth = depth
        self.proof_num = proof_num
        self.is_hypothesis = is_hypothesis
    
    def __str__(self):
        return f"ProofLine(Formula={str(self.formula)},depth={self.depth},proof_num={self.proof_num},is_hypotheses={self.is_hypothesis})"


class Proof:
    def __init__(self, hypotheses):
        self.proof_lines = [None] + hypotheses              # Proof in lines as list of Formulas, 1-indexed

        # need to handle subproof line indexing (can do this through depth instead)

    def add_hypothesis(self, hypothesis: ProofLine):
        assert(hypothesis.is_hypothesis)
        self.proof_lines.append(hypothesis)
    
    def deduce(self, proof_line, rule, line_num_a=-1, line_num_b=-1, line_num_c=-1, line_num_d=-1):
        '''
        Attempt to deduce the given proof line given the rule supplied
        
        :param self: Description
        :param proof_line: Description
        :param rule: Description
        :param line_a: Description
        :param line_b: Description
        '''

        if proof_line.is_hypothesis:
            raise AssertionError(f"Cannot deduce a hypothesis {proof_line}, please use add_hypothesis instead.")

        def assert_one_depth_lower(proof_line_1: ProofLine, proof_line_2: ProofLine):
            # Defaults to true if proof_line_2 is None
            assert(proof_line_2 is None or proof_line_1.depth == proof_line_2.depth - 1)

        def assert_equal_depth(proof_line_1: ProofLine, proof_line_2: ProofLine):
            assert(proof_line_1.depth == proof_line_2.depth)

        formula = None if proof_line is None else proof_line.formula
        is_valid = False
        proof_line_a = None if line_num_a == -1 else self.proof_lines[line_num_a]
        formula_a = None if proof_line_a is None else proof_line_a.formula
        proof_line_b = None if line_num_b == -1 else self.proof_lines[line_num_b]
        formula_b = None if proof_line_b is None else proof_line_b.formula
        proof_line_c = None if line_num_c == -1 else self.proof_lines[line_num_c]
        formula_c = None if proof_line_c is None else proof_line_c.formula
        proof_line_d = None if line_num_d == -1 else self.proof_lines[line_num_d]
        formula_d = None if proof_line_d is None else proof_line_d.formula

        try:
            match rule:
                # Inference Rules
                case Rule.AND_INTR:
                    assert_equal_depth(proof_line, proof_line_a)
                    assert_equal_depth(proof_line, proof_line_b)
                    if (formula.op == Op.AND and formula_a == formula.left and formula_b == formula.right):
                        is_valid = True
                case Rule.AND_ELIM:
                    assert_equal_depth(proof_line, proof_line_a)
                    if (formula_a.op == Op.AND and (formula_a.left == formula or formula_a.right == formula)):
                        is_valid = True
                case Rule.OR_INTR:
                    assert_equal_depth(proof_line, proof_line_a)
                    if (formula.op == Op.OR and formula_a == formula.left or formula_a == formula.right):
                        is_valid = True
                case Rule.IMP_ELIM:
                    assert_equal_depth(proof_line, proof_line_a)
                    assert_equal_depth(proof_line, proof_line_b)
                    if (formula_b.op == Op.IMPLIES and formula_b.left == formula_a and formula_b.right == formula):
                        is_valid = True
                case Rule.NOT_ELIM:
                    assert_equal_depth(proof_line, proof_line_a)
                    assert_equal_depth(proof_line, proof_line_b)
                    if formula_a == Formula(Op.NOT, formula_b) or formula_b == Formula(Op.NOT, formula_a):
                        is_valid = True

                # Supposition Rules
                case Rule.IMP_INTR:
                    assert_one_depth_lower(proof_line, proof_line_a)
                    assert_one_depth_lower(proof_line, proof_line_b)
                    assert(proof_line_c is None and proof_line_d is None)
                    assert(proof_line_a.is_hypothesis and not proof_line_b.is_hypothesis)
                    if formula.op == Op.IMPLIES and formula.left == formula_a and formula.right == formula_b:
                        is_valid = True
                case Rule.OR_ELIM:
                    assert_equal_depth(proof_line, proof_line_a)
                    assert_one_depth_lower(proof_line, proof_line_b)
                    assert_one_depth_lower(proof_line, proof_line_c)
                    assert_one_depth_lower(proof_line, proof_line_d)
                    if (formula_a.op == Op.OR and
                          formula_a.left == formula_b and
                          formula_a.right == formula_c and
                          formula_b.proof_num == formula_d.proof_num and
                          formula_c.proof_num == formula_d.proof_num and
                          formula_b.is_hypothesis and
                          formula_c.is_hypothesis and
                          not formula_d.is_hypothesis
                          ):
                        is_valid = True
                case Rule.NOT_INT:
                    assert_one_depth_lower(proof_line, proof_line_a)
                    assert_one_depth_lower(proof_line, proof_line_b)
                    assert_one_depth_lower(proof_line, proof_line_c)
                    if ((formula == Formula(op=Op.NOT, left=formula_a, right=None) or formula_a == Formula(op=Op.NOT, left=formula, right=None)) and
                        formula_a.is_hypothesis and
                        (formula_b == Formula(op=Op.NOT, left=formula_c, right=None) or formula_c == Formula(op=Op.NOT, left=formula_b, right=None))
                        ):
                        is_valid = True
                case _:
                    raise ValueError(f"Rule {rule} does not have a matching rule.")

            if is_valid:
                self.proof_lines.append(proof_line)
            assert(is_valid)
        except:
            raise AssertionError(f"Proof line {proof_line} could not be deduced from the following lines:\n{proof_line_a}\n{proof_line_b}\n{proof_line_c}\n{proof_line_d}")

def test_IMP_INTR():
    p = Proof(hypotheses=[])
    formula_1 = Formula(Op.AND, FormulaVar(1), FormulaVar(2))
    proof_line_1 = ProofLine(formula=formula_1, depth=1, proof_num=0, is_hypothesis=True)

    formula_2 = FormulaVar(1)
    proof_line_2 = ProofLine(formula=FormulaVar(1), depth=1, proof_num=0)

    proof_line_3 = ProofLine(formula=Formula(op=Op.IMPLIES, left=formula_1, right=formula_2), depth=0, proof_num=0)

    p.add_hypothesis(proof_line_1)
    p.deduce(proof_line=proof_line_2, rule=Rule.AND_ELIM, line_num_a=1)
    p.deduce(proof_line=proof_line_3, rule=Rule.IMP_INTR, line_num_a=1, line_num_b=2)

def test_OR_ELIM():
    pass

if __name__ == "__main__":
    # formula = Formula(Op.NOT, FormulaVar(1), FormulaVar(2))

    # p.deduce(proof_line=FormulaVar(1), rule=Rule.AND_ELIM, line_num_a=1)
    # p.deduce(proof_line=Formula(Op.AND, FormulaVar(1), formula), rule=Rule.AND_INTR, line_num_a=2, line_num_b=1)
    # p.deduce(formula=Formula(Op.AND, FormulaVar(1), formula), rule=Rule.AND_INTR, line_num_a=1, line_num_b=2)
    test_IMP_INTR()