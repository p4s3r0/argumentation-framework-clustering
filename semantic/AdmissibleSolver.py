import z3

from utils import Argument
from . import SemanticHelper


class AdmissibleSolver:
    def __init__(self, AF: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesAdmissible()



    def setRulesAdmissible(self):
        ''' Sets the rules for admissibility check. Formula is in the Readme'''
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton:
                continue
            
            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Implies(a.z3_value, True))
                continue

            clause_left = True
            clause_right = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    clause_left = z3.And(clause_left, z3.Not(z3.And(a.z3_value, b.z3_value)))

                clause_right_right = False
                # check if c exists
                if len(b.defends) == 0:
                    clause_right = z3.And(clause_right, False)
                    continue
                # get c: (c,b)∈R
                c: Argument.Argument
                for c in b.defends:
                    c = self.AF[c]
                    clause_right_right = z3.Or(clause_right_right, c.z3_value)
                    
                clause_right = z3.And(clause_right, clause_right_right)
            clause = z3.And(z3.Implies(a.z3_value, clause_left), z3.Implies(a.z3_value, clause_right))
            self.solver.add(clause)


    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)


    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)